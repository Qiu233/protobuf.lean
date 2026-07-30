module

import Lean.Data.KVMap
public import Protobuf.Versions.Editions
public import Protobuf.Versions.Proto2
public import Protobuf.Versions.Proto3

open System
open Lean

public section

namespace Protobuf.Versions

open google.protobuf Encoding Notation

def compile_proto
    (desc : FileDescriptorSet)
    (precompiledFiles : Array String := #[]) :
    M (Array Command) := do
  let reflectionDesc ← prepareFileDescriptorSet desc
  let reflectionFiles : Std.HashMap String FileDescriptorProto :=
    reflectionDesc.file.foldl (init := {}) fun files file =>
      match file.name with
      | some name => files.insert name file
      | none => files
  let desc := sanitizeFileDescriptorSet reflectionDesc
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
    if file.name.any precompiledFiles.contains then
      /-
      A frontend may provide declarations for selected imports itself.  Such a
      schema must remain in the set above so all of its types, extension
      targets, and ranges are validated statically; only its code emission is
      skipped.  The caller names these files explicitly, so a forged
      descriptor cannot suppress its own generation merely by claiming a
      well-known path.
      -/
      pure #[]
    else
      let reflectionFile :=
        file.name.bind (reflectionFiles[·]?) |>.getD file
      if let some stx := file.syntax then
        if stx == "proto3" then
          Proto3.compile_file file reflectionFile
        else if stx == "proto2" then
          Proto2.compile_file file reflectionFile
        else if stx == "editions" then
          Editions.compile_file file reflectionFile
        else
          throw s!"{stx} is not supported yet"
      else
        Proto2.compile_file file reflectionFile
