module

public import Lean
public meta import Protobuf.Versions

namespace Protobuf.Elab

open System
open Lean Elab Command

public meta register_option protobuf.trace.notation : Bool := { defValue := false }

public meta register_option protobuf.trace.descriptor : Bool := { defValue := false }

syntax inClause := " in " str

/-- relative to package root -/
syntax (name := loadProtoFileCommand) "#load_proto_file " str (inClause)? : command
/--
Load and validate a schema, but emit only runtime descriptor registrations.
Use this for reflection-only programs that do not need generated Lean types.
-/
syntax (name := loadProtoDescriptorsCommand) "#load_proto_descriptors " str (inClause)? : command
syntax (name := loadProtoDirCommand) "#load_proto_dir " str : command

meta def read_proto (srcFile : FilePath) (protoPath : FilePath) : ExceptT String IO google.protobuf.FileDescriptorSet := do
  let bin ← IO.FS.withTempFile fun _h tmp => do
    _ ← IO.Process.run {
      cmd := "protoc"
      args := #[
        srcFile.toString,
        "--include_imports",
        "--retain_options",
        "--descriptor_set_out", tmp.toString,
        s!"--proto_path={protoPath.toString}"
      ]
    }
    IO.FS.readBinFile tmp -- TODO: may be too large, make it incremental
  let data ← liftExcept <|
    (Binary.Get.run (Binary.getThe Encoding.Message) bin |>.toExcept).mapError fun e =>
      s!"failed to parse protoc output: {e}"
  let desc ← liftExcept <|
    (google.protobuf.FileDescriptorSet.«protobuf.internal».fromMessage data).mapError fun e =>
      s!"failed to parse protoc output: {e}"
  /-
  Keep every transitive descriptor for whole-set static validation, including
  `descriptor.proto`.  `Versions.compile_proto` knows that its Lean
  declarations are already provided by `Protobuf.Internal.Desc` and omits only
  its code generation after validation.  Removing it here would make valid
  custom-option extensions look as though their extendee did not exist.
  -/
  return desc

meta def read_proto_files (srcFiles : Array FilePath) (protoPath : FilePath) :
    ExceptT String IO google.protobuf.FileDescriptorSet := do
  if srcFiles.isEmpty then
    throw "no .proto files found in directory"
  let bin ← IO.FS.withTempFile fun _h tmp => do
    let mut args := #[
      s!"--proto_path={protoPath.toString}",
      "--include_imports",
      "--retain_options",
      s!"--descriptor_set_out={tmp.toString}"
    ]
    args := args ++ srcFiles.map (·.toString)
    _ ← IO.Process.run { cmd := "protoc", args := args }
    IO.FS.readBinFile tmp -- TODO: may be too large, make it incremental
  let data ← liftExcept <|
    (Binary.Get.run (Binary.getThe Encoding.Message) bin |>.toExcept).mapError fun e =>
      s!"failed to parse protoc output: {e}"
  let desc ← liftExcept <|
    (google.protobuf.FileDescriptorSet.«protobuf.internal».fromMessage data).mapError fun e =>
      s!"failed to parse protoc output: {e}"
  -- See `read_proto`: validation needs the complete descriptor graph.
  return desc

meta partial def collect_proto_files (root : FilePath) : IO (Array FilePath) := do
  let entries ← root.readDir
  let mut acc := #[]
  for entry in entries do
    let path := entry.path
    if ← path.isDir then
      acc := acc ++ (← collect_proto_files path)
    else
      match path.extension with
      | some "proto" => acc := acc.push path
      | _ => pure ()
  return acc

@[command_elab loadProtoFileCommand]
public meta def elabLoadProtoFileCommand : CommandElab := fun stx => do
  let `(loadProtoFileCommand| #load_proto_file $pathStx:str $[in $folderStx]?) := stx | throwUnsupportedSyntax
  let path := FilePath.mk pathStx.getString
  unless ← path.pathExists do
    throwErrorAt pathStx "file {path} does not exist"
  if ← path.isDir then
    throwErrorAt pathStx "path {path} is a directory"
  let folder? ← folderStx.mapM fun (x : TSyntax `str) => do
    let f := FilePath.mk x.getString
    unless ← f.pathExists do
      throwErrorAt x "file {f} does not exist"
    unless ← f.isDir do
      throwErrorAt x "path {f} is not a directory"
    pure f
  let protoPath ← (folder? <|> path.parent).getDM (throwError "failed to infer --proto_path")
  let descExcept ← liftM (m := IO) <| read_proto path protoPath
  let desc ← Lean.ofExcept descExcept
  if ← protobuf.trace.descriptor.getM then
    logInfo m!"{repr desc}"
  let commands ← Lean.ofExcept <|
    Versions.compile_proto desc
      #["google/protobuf/descriptor.proto"] |>.run
  if ← protobuf.trace.notation.getM then
    for cmd in commands do
      logInfo m!"{cmd}"
  commands.forM elabCommand

@[command_elab loadProtoDescriptorsCommand]
public meta def elabLoadProtoDescriptorsCommand : CommandElab := fun stx => do
  let `(loadProtoDescriptorsCommand|
      #load_proto_descriptors $pathStx:str $[in $folderStx]?) := stx
    | throwUnsupportedSyntax
  let path := FilePath.mk pathStx.getString
  unless ← path.pathExists do
    throwErrorAt pathStx "file {path} does not exist"
  if ← path.isDir then
    throwErrorAt pathStx "path {path} is a directory"
  let folder? ← folderStx.mapM fun (x : TSyntax `str) => do
    let f := FilePath.mk x.getString
    unless ← f.pathExists do
      throwErrorAt x "file {f} does not exist"
    unless ← f.isDir do
      throwErrorAt x "path {f} is not a directory"
    pure f
  let protoPath ←
    (folder? <|> path.parent).getDM
      (throwError "failed to infer --proto_path")
  let descExcept ← liftM (m := IO) <| read_proto path protoPath
  let desc ← Lean.ofExcept descExcept
  if ← protobuf.trace.descriptor.getM then
    logInfo m!"{repr desc}"
  let commands ← Lean.ofExcept <|
    Versions.compile_proto_descriptors desc
      #["google/protobuf/descriptor.proto"] |>.run
  if ← protobuf.trace.notation.getM then
    for cmd in commands do
      logInfo m!"{cmd}"
  commands.forM elabCommand

@[command_elab loadProtoDirCommand]
public meta def elabLoadProtoDirCommand : CommandElab := fun stx => do
  let `(loadProtoDirCommand| #load_proto_dir $pathStx:str) := stx | throwUnsupportedSyntax
  let path := FilePath.mk pathStx.getString
  unless ← path.pathExists do
    throwErrorAt pathStx "directory {path} does not exist"
  unless ← path.isDir do
    throwErrorAt pathStx "path {path} is not a directory"
  let files ← collect_proto_files path
  let descExcept ← liftM (m := IO) <| read_proto_files files path
  let desc ← Lean.ofExcept descExcept
  if ← protobuf.trace.descriptor.getM then
    logInfo m!"{repr desc}"
  let commands ← Lean.ofExcept <|
    Versions.compile_proto desc
      #["google/protobuf/descriptor.proto"] |>.run
  if ← protobuf.trace.notation.getM then
    for cmd in commands do
      logInfo m!"{cmd}"
  commands.forM elabCommand
