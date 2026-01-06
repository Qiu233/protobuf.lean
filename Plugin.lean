module

import Protobuf.Encoding
import Protobuf.Internal.Desc
meta import Protobuf.Notation
meta import Protobuf.Elab
import Protobuf.Notation.Syntax
import Protobuf.Versions

open Protobuf Encoding Notation Internal
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

  let renderFile (cmds : Array Command) : String :=
    let body := renderCommands cmds
    let header := String.intercalate "\n"
      [ "module"
      , ""
      , "import Protobuf.Encoding"
      , "meta import Protobuf.Notation"
      , ""
      , "open Protobuf Encoding"
      , "open scoped Protobuf.Notation"
      , ""
      ]
    let r := header ++ body
    if r.endsWith "\n" then r
    else r ++ "\n"

  let outputFileName (name : String) : String :=
    if name.endsWith ".proto" then
      name.dropRight ".proto".length ++ ".lean"
    else
      name ++ ".lean"

  let mut filesOut := #[]
  for name in filesToGenerate do
    let cmds ← match outputs[name]? with
      | some cmds => pure cmds
      | none => throw s!"file_to_generate {name} was not found in protoc input"
    let content := renderFile cmds
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
