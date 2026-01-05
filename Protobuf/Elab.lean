module

public import Lean
public meta import Protobuf.Versions

namespace Protobuf.Elab

open System
open Lean Elab Command

public meta register_option protobuf.trace.notation : Bool := { defValue := false }

public meta register_option protobuf.trace.descriptor : Bool := { defValue := false }

/-- relative to package root -/
syntax (name := loadProtoFileCommand) "#load_proto_file " str : command
syntax (name := loadProtoDirCommand) "#load_proto_dir " str : command

meta def read_proto (srcFile : FilePath) : ExceptT String IO Protobuf.Internal.Desc.FileDescriptorSet := do
  let bin ← IO.FS.withTempFile fun h tmp => do
    _ ← IO.Process.run { cmd := "protoc", args := #[srcFile.toString, "--descriptor_set_out", tmp.toString] }
    h.readBinToEnd -- TODO: may be too large, make it incremental
  let data ← match (Binary.Get.run (Binary.getThe Encoding.Message) bin |>.toExcept) with
    | .ok data => pure data
    | .error e => throw s!"failed to parse protoc output: {e}"
  let desc ← match Protobuf.Internal.Desc.FileDescriptorSet.fromMessage data with
    | .ok d => pure d
    | .error e => throw s!"failed to parse protoc output: {e}"
  return desc

meta def read_proto_files (srcFiles : Array FilePath) (protoPath : FilePath) :
    ExceptT String IO Protobuf.Internal.Desc.FileDescriptorSet := do
  if srcFiles.isEmpty then
    throw "no .proto files found in directory"
  let bin ← IO.FS.withTempFile fun h tmp => do
    let mut args := #[s!"--proto_path={protoPath.toString}", s!"--descriptor_set_out={tmp.toString}"]
    args := args ++ srcFiles.map (·.toString)
    _ ← IO.Process.run { cmd := "protoc", args := args }
    h.readBinToEnd -- TODO: may be too large, make it incremental
  let data ← match (Binary.Get.run (Binary.getThe Encoding.Message) bin |>.toExcept) with
    | .ok data => pure data
    | .error e => throw s!"failed to parse protoc output: {e}"
  let desc ← match Protobuf.Internal.Desc.FileDescriptorSet.fromMessage data with
    | .ok d => pure d
    | .error e => throw s!"failed to parse protoc output: {e}"
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
  let `(loadProtoFileCommand| #load_proto_file $pathStx:str) := stx | throwUnsupportedSyntax
  let path := FilePath.mk pathStx.getString
  unless ← path.pathExists do
    throwErrorAt pathStx "file {path} does not exist"
  if ← path.isDir then
    throwErrorAt pathStx "path {path} is a directory"
  let descExcept ← liftM (m := IO) <| read_proto path
  let desc ← match descExcept with
    | Except.ok d => pure d
    | Except.error e => throwError "{e}"
  if ← protobuf.trace.descriptor.getM then
    logInfo m!"{repr desc}"
  let commands ← match Versions.compile_proto desc |>.run with
    | Except.ok cmds => pure cmds
    | Except.error e => throwError "{e}"
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
  let files ← liftM (m := IO) <| collect_proto_files path
  let descExcept ← liftM (m := IO) <| read_proto_files files path
  let desc ← match descExcept with
    | Except.ok d => pure d
    | Except.error e => throwError "{e}"
  if ← protobuf.trace.descriptor.getM then
    logInfo m!"{repr desc}"
  let commands ← match Versions.compile_proto desc |>.run with
    | Except.ok cmds => pure cmds
    | Except.error e => throwError "{e}"
  if ← protobuf.trace.notation.getM then
    for cmd in commands do
      logInfo m!"{cmd}"
  commands.forM elabCommand
