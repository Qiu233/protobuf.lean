module

import Protobuf.Notation
public import Protobuf.Versions.Editions
public import Protobuf.Versions.Proto2
public import Protobuf.Versions.Proto3

open System
open Lean

public section

namespace Protobuf.Versions

open Internal.Desc Encoding Notation

def compile_proto (desc : FileDescriptorSet) : M (Array Command) := do
  let names ← desc.file.mapM fun x => get!! x.name
  let deps := names.zip <| desc.file.map fun x => x.dependency
  let deps := Std.HashMap.ofList deps.toList
  let sccs := names.topoSortSCCHash deps |>.reverse
  for scc in sccs do
    if scc.size > 1 then
      let cycle := scc.toList
      throw s!"{decl_name%}: mutual recursion in file imports: {String.intercalate ", " cycle}"
  let sortedNames := sccs.flatten
  let sorted := desc.file.toList.mergeSort (fun x y => sortedNames.idxOf x.name.get! ≤ sortedNames.idxOf y.name.get!)
  sorted.toArray.flatMapM fun file => do
    if let some stx := file.syntax then
      if stx == "proto3" then
        Proto3.compile_file file
      else if stx == "proto2" then
        Proto2.compile_file file
      else if stx == "editions" then
        Editions.compile_file file
      else
        throw s!"{stx} is not supported yet"
    else
      Proto2.compile_file file

private def renderCommands (cmds : Array Command) : IO String := do
  unsafe Lean.enableInitializersExecution
  let env ← Lean.importModules #[`Protobuf.Notation] {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<proto>", fileMap := default }
  let st : Core.State := { env := env }
  let mut out := ""
  for cmd in cmds do
    let (fmt, _) ← (Lean.PrettyPrinter.ppCommand cmd).toIO ctx st
    out := out ++ fmt.pretty ++ "\n\n"
  return out
