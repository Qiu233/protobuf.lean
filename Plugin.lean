module

import Protobuf.Encoding
import Protobuf.Internal.Desc
meta import Protobuf.Notation
meta import Protobuf.Elab
import Protobuf.Notation.Syntax
import Protobuf.Versions

open Protobuf Encoding Notation
open Lean

section

-- we use internal representation from `Protobuf.Internal.Desc`
-- NOTE: the internal representation is not perfect aligned with proto2 semantics
--    but I believe `protoc` will recognize the encoded result.
#load_proto_file "proto/google/protobuf/compiler/plugin.proto"

open google.protobuf
open google.protobuf.compiler


-- bool compiler::GenerateCode(
--      const CodeGeneratorRequest & request,
--      const CodeGenerator & generator,
--      CodeGeneratorResponse * response,
--      std::string * error_msg)
def generate_code (request : CodeGeneratorRequest) : ExceptT String IO CodeGeneratorResponse := do
  let parseOptions (param? : Option String) : Std.HashMap String String :=
    match param? with
    | none => {}
    | some param =>
      let entries := param.splitOn ","
      entries.foldl (init := {}) fun acc entry =>
        let entry := entry.trim
        if entry.isEmpty then acc
        else
          match entry.splitOn "=" with
          | [] => acc
          | key :: rest =>
            let key := key.trim
            if key.isEmpty then acc
            else
              let value := String.intercalate "=" rest |>.trim
              acc.insert key value

  let normalizePath (path : String) : String :=
    path.map fun c => if c == '\\' then '/' else c

  let rec dropLast (xs : List String) : List String :=
    match xs with
    | [] => []
    | [_] => []
    | x :: xs => x :: dropLast xs

  let rec last? (xs : List String) : Option String :=
    match xs with
    | [] => none
    | [x] => some x
    | _ :: xs => last? xs

  let dirOf (path : String) : String :=
    let parts := (normalizePath path).splitOn "/"
    let parts := dropLast parts
    String.intercalate "/" parts

  let baseName (path : String) : String :=
    let parts := (normalizePath path).splitOn "/"
    (last? parts).getD ""

  let moduleNameFromPath (path : String) : String :=
    let path := normalizePath path
    let path := if path.startsWith "./" then path.drop 2 else path
    let path := if path.endsWith ".proto" then path.dropRight ".proto".length else path
    let parts := path.splitOn "/" |>.filter (fun p => !p.isEmpty)
    String.intercalate "." parts

  let relativeImportPath (current : String) (dep : String) : String :=
    let dep := normalizePath dep
    let curDir := dirOf current
    if curDir.isEmpty then dep
    else
      let prefix_ := curDir ++ "/"
      if dep.startsWith prefix_ then dep.drop prefix_.length else dep

  let withPrefix (prefix_ : String) (mod : String) : String :=
    if prefix_.isEmpty then mod
    else if mod.isEmpty then prefix_
    else prefix_ ++ "." ++ mod

  let options := parseOptions request.parameter
  let lean4Prefix ← options["lean4_prefix"]?.getDM (throw "lean4_prefix is not specified, you should specify by --lean4_opt=lean4_prefix=...")

  let filesToGenerate := request.file_to_generate
  let targetSet : Std.HashMap String PUnit :=
    filesToGenerate.foldl (init := {}) fun acc name => acc.insert name ()
  if filesToGenerate.isEmpty then
    let supportedFeatures : UInt64 := 3
    let response : CodeGeneratorResponse := {
      file := #[]
      supported_features := some supportedFeatures
      minimum_edition := some (1000 : Int32)
      maximum_edition := some (1001 : Int32)
    }
    return response
  let sourceMap : Std.HashMap String FileDescriptorProto :=
    request.source_file_descriptors.foldl (init := {}) fun acc (file : FileDescriptorProto) =>
      match file.name with
      | some name => acc.insert name file
      | none => acc
  let protoFiles : Array FileDescriptorProto :=
    request.proto_file.map fun (file : FileDescriptorProto) =>
      match file.name with
      | some name =>
        match sourceMap[name]? with
        | some full => full
        | none => file
      | none => file

  let desc : FileDescriptorSet := { file := protoFiles }

  let compileTargets (desc : FileDescriptorSet)
      (targets : Std.HashMap String PUnit) :
      Protobuf.Versions.M (Std.HashMap String (Array Command)) := do
    let names ← desc.file.mapM fun (file : FileDescriptorProto) =>
      match file.name with
      | some name => pure name
      | none => throw "file descriptor missing name"
    let deps := names.zip <| desc.file.map fun (file : FileDescriptorProto) => file.dependency
    let deps := Std.HashMap.ofList deps.toList
    let sccs := names.topoSortSCCHash deps |>.reverse
    for scc in sccs do
      if scc.size > 1 then
        let cycle := scc.toList
        throw s!"{decl_name%}: mutual recursion in file imports: {String.intercalate ", " cycle}"
    let sortedNames := sccs.flatten
    let mut nameIndex : Std.HashMap String Nat := {}
    for i in [:sortedNames.size] do
      nameIndex := nameIndex.insert sortedNames[i]! i
    let sorted := desc.file.toList.mergeSort (fun x y =>
      let ix := nameIndex[(x.name.getD "")]?.getD 0
      let iy := nameIndex[(y.name.getD "")]?.getD 0
      ix ≤ iy)
    let mut outputs : Std.HashMap String (Array Command) := {}
    for file in sorted do
      let cmds ←
        match file.syntax with
        | some stx =>
          if stx == "proto3" then
            Protobuf.Versions.Proto3.compile_file file
          else if stx == "proto2" then
            Protobuf.Versions.Proto2.compile_file file
          else if stx == "editions" then
            Protobuf.Versions.Editions.compile_file file
          else
            throw s!"{stx} is not supported yet"
        | none =>
          Protobuf.Versions.Proto2.compile_file file
      let name := file.name.getD ""
      if targets.contains name then
        outputs := outputs.insert name cmds
    return outputs

  let outputs ← liftM (m := Except String) (n := ExceptT String IO ) <| Protobuf.Versions.M.run (compileTargets desc targetSet)

  let renderCommands (cmds : Array Command) : String :=
    let cmds := cmds.map fun x =>
      match x.raw.getKind with
      | ``enumDec => PrettyPrinter.enumDec.pprint <| TSyntax.mk x.raw
      | ``oneofDec => PrettyPrinter.oneofDec.pprint <| TSyntax.mk x.raw
      | ``messageDec => PrettyPrinter.messageDec.pprint <| TSyntax.mk x.raw
      | ``proto_mutual_stx => PrettyPrinter.proto_mutual_stx.pprint <| TSyntax.mk x.raw
      | kind => panic! s!"{decl_name%}: unknown kind {kind}"
    String.intercalate "\n\n" cmds.toList

  let renderFile (imports : Array String) (cmds : Array Command) : String :=
    let body := renderCommands cmds
    let importLines := imports.toList.map fun m => s!"public import {m}"
    let header := String.intercalate "\n"
      [ "module"
      , ""
      , "public import Protobuf.Encoding"
      , "meta import Protobuf.Notation"
      , String.intercalate "\n" importLines
      , ""
      , "public section"
      , ""
      , "open Protobuf Encoding"
      , "open scoped Protobuf.Notation"
      , ""
      ]
    let r := header ++ body
    if r.endsWith "\n" then r
    else r ++ "\n"

  let outputFileName (name : String) : String :=
    let base := baseName name
    if base.endsWith ".proto" then
      base.dropRight ".proto".length ++ ".lean"
    else
      base ++ ".lean"

  let descByName : Std.HashMap String FileDescriptorProto :=
    protoFiles.foldl (init := {}) fun acc file =>
      match file.name with
      | some name => acc.insert name file
      | none => acc

  let mut filesOut := #[]
  for name in filesToGenerate do
    let deps :=
      match descByName[name]? with
      | some file => file.dependency
      | none => #[]
    let importModules ← do
      let mut seen : Std.HashSet String := {}
      let mut out : Array String := #[]
      for dep in deps do
        if dep == "google/protobuf/descriptor.proto" then
          let mod := "Protobuf.Internal.Desc"
          if !mod.isEmpty && !seen.contains mod then
            seen := seen.insert mod
            out := out.push mod
        else
          let rel := relativeImportPath name dep
          let mod := moduleNameFromPath rel
          let mod := withPrefix lean4Prefix mod
          if !mod.isEmpty && !seen.contains mod then
            seen := seen.insert mod
            out := out.push mod
      pure out
    let cmds ← match outputs[name]? with
      | some cmds => pure cmds
      | none => throw s!"file_to_generate {name} was not found in protoc input"
    let content := renderFile importModules cmds
    let outName := outputFileName name
    let file : CodeGeneratorResponse.File := { name := some outName, content := some content }
    filesOut := filesOut.push file

  let supportedFeatures : UInt64 := 3
  let response : CodeGeneratorResponse := {
    file := filesOut
    supported_features := some supportedFeatures
    minimum_edition := some (1000 : Int32)
    maximum_edition := some (1001 : Int32)
  }
  return response

def exeName : String := "protoc-gen-lean4"

public def main : IO UInt32 := do
  let stdIn ← IO.getStdin
  let stdErr ← IO.getStderr
  let stdOut ← IO.getStdout
  let input ← stdIn.readBinToEnd
  let request := CodeGeneratorRequest.decode input
  let request ← match request with
    | .ok r => pure r
    | .error _ =>
      stdErr.putStrLn s!"{exeName}: protoc sent unparseable request to plugin."
      return 1
  let result ← generate_code request
  let result ← match result with
    | .ok r => pure r
    | .error err =>
      stdErr.putStrLn s!"{exeName}: {err}"
      return 1
  let resultBin ← match result.encode with
    | .ok r => pure r
    | .error err =>
      stdErr.putStrLn s!"{exeName}: failed to serialize protobuf: {err}"
      return 1
  stdOut.write resultBin
  return 0
