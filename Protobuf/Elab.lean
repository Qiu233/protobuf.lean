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
