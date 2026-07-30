module

import Lean.Syntax
import Protobuf.Encoding
import Protobuf.Internal.Desc
import Protobuf.Plugin.DescriptorBoundary
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

private def supportedResponse
    (files : Array CodeGeneratorResponse.File := #[])
    (error? : Option String := none) : CodeGeneratorResponse := {
  error := error?
  file := files
  supported_features := some 3
  minimum_edition := some (1000 : Int32)
  maximum_edition := some (1001 : Int32)
}

private def isAsciiAlpha (c : Char) : Bool :=
  let n := c.toNat
  (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122)

private def isWindowsDrivePath (path : String) : Bool :=
  match path.toList with
  | drive :: ':' :: _ => isAsciiAlpha drive
  | _ => false

private def normalizePath (path : String) : String :=
  path.map fun c => if c == '\\' then '/' else c

private def dropLeadingCurrentDir (path : String) : String :=
  if path.startsWith "./" then
    (path.drop 2).toString
  else
    path

private def normalizeRelativePath (path : String) : Except String String := do
  let path := dropLeadingCurrentDir (normalizePath path)
  if path.isEmpty || path.startsWith "/" then
    throw s!"protobuf file name must be a non-empty relative path: {path.quote}"
  if path.any fun c => c.toNat < 32 || c.toNat == 127 then
    throw s!"protobuf file name contains a control character: {path.quote}"
  if isWindowsDrivePath path then
    throw s!"protobuf file name must not use a Windows drive path: {path.quote}"
  let parts := path.splitOn "/"
  if parts.any fun part => part.isEmpty || part == "." || part == ".." then
    throw s!"protobuf file name contains a forbidden path component: {path.quote}"
  return String.intercalate "/" parts

private def moduleNameFromPath (path : String) : Except String String := do
  let path ← normalizeRelativePath path
  let path :=
    if path.endsWith ".proto" then
      (path.dropEnd ".proto".length).toString
    else
      path
  let parts := path.splitOn "/"
  if parts.any (·.isEmpty) then
    throw s!"protobuf file name has an empty Lean module component: {path.quote}"
  let parts ← parts.mapM fun part => do
    let some escaped := Name.escapePart part (force := true)
      | throw
          s!"cannot represent protobuf path component {part.quote} as a Lean module name"
    return escaped
  return String.intercalate "." parts

private def withPrefix (prefix_ : String) (mod : String) : String :=
  if prefix_.isEmpty then mod
  else if mod.isEmpty then prefix_
  else prefix_ ++ "." ++ mod

private def isModuleIdentStart (c : Char) : Bool :=
  c == '_' || isAsciiAlpha c

private def isModuleIdentRest (c : Char) : Bool :=
  isModuleIdentStart c || let n := c.toNat; 48 ≤ n && n ≤ 57

private def normalizeModulePrefix (prefix_ : String) : Except String String := do
  if prefix_.isEmpty then
    return ""
  let parts := prefix_.splitOn "."
  if parts.any fun part =>
      match part.toList with
      | [] => true
      | first :: rest =>
        !isModuleIdentStart first || !rest.all isModuleIdentRest then
    throw
      s!"lean4_prefix must be a dot-separated ASCII Lean module name: {prefix_.quote}"
  let escaped ← parts.mapM fun part => do
    let some value := Name.escapePart part (force := true)
      | throw
          s!"cannot represent lean4_prefix component {part.quote} as a Lean module name"
    return value
  return String.intercalate "." escaped

private def outputFileName (name : String) : Except String String := do
  let path ← normalizeRelativePath name
  let output :=
    if path.endsWith ".proto" then
      let stem := (path.dropEnd ".proto".length).toString
      if stem.isEmpty || (stem.splitOn "/").any (·.isEmpty) then
        none
      else
        some (stem ++ ".lean")
    else
      some (path ++ ".lean")
  let output ← output.getDM
    (throw
      s!"protobuf file name has an empty Lean module component: {path.quote}")
  /-
  protoc 35 rejects every output name containing `..`, even when it is not an
  entire path component.  Reject here so the diagnostic is returned in
  CodeGeneratorResponse.error rather than as a later filesystem failure.
  -/
  if output.contains ".." then
    throw
      s!"generated Lean file name contains `..`, which protoc rejects: {output.quote}"
  return output


-- bool compiler::GenerateCode(
--      const CodeGeneratorRequest & request,
--      const CodeGenerator & generator,
--      CodeGeneratorResponse * response,
--      std::string * error_msg)
def generate_code (request : CodeGeneratorRequest) : ExceptT String IO CodeGeneratorResponse := do
  let decodeProtocolString (field : String)
      (value : Protobuf.UnvalidatedString) : Except String String :=
    value.toString?.getDM
      (throw s!"CodeGeneratorRequest.{field} contains invalid UTF-8")

  let parseOptions (param? : Option String) : Std.HashMap String String :=
    match param? with
    | none => {}
    | some param =>
      let entries := param.splitOn ","
      entries.foldl (init := {}) fun acc entry =>
        let entry := entry.trimAscii.toString
        if entry.isEmpty then acc
        else
          match entry.splitOn "=" with
          | [] => acc
          | key :: rest =>
            let key := key.trimAscii.toString
            if key.isEmpty then acc
            else
              let value := String.intercalate "=" rest |>.trimAscii.toString
              acc.insert key value

  let parameter ← request.parameter.mapM fun value =>
    decodeProtocolString "parameter" value
  let options := parseOptions parameter
  let rawLean4Prefix ← options["lean4_prefix"]?.getDM (throw "lean4_prefix is not specified, you should specify by --lean4_opt=lean4_prefix=...")
  let lean4Prefix ← normalizeModulePrefix rawLean4Prefix

  let filesToGenerate ← request.file_to_generate.mapM fun value =>
    decodeProtocolString "file_to_generate" value
  let mut targetSet : Std.HashMap String PUnit := {}
  for name in filesToGenerate do
    if targetSet.contains name then
      throw s!"file_to_generate `{name}` is listed more than once"
    targetSet := targetSet.insert name ()
  if filesToGenerate.isEmpty then
    return supportedResponse

  let mut outputOwners : Std.HashMap String String := {}
  let mut moduleOwners : Std.HashMap String String := {}
  for name in filesToGenerate do
    let moduleName ← moduleNameFromPath name
    if let some previous := moduleOwners[moduleName]? then
      throw
        s!"file_to_generate `{name}` and `{previous}` map to the same Lean module `{moduleName}`"
    moduleOwners := moduleOwners.insert moduleName name
    let outputName ← outputFileName name
    if let some previous := outputOwners[outputName]? then
      throw
        s!"file_to_generate `{name}` and `{previous}` map to the same output file `{outputName}`"
    outputOwners := outputOwners.insert outputName name

  let mut runtimeByName : Std.HashMap String FileDescriptorProto := {}
  for file in request.proto_file do
    let name ← file.name.getDM
      (throw "proto_file descriptor is missing its name")
    if runtimeByName.contains name then
      throw s!"proto_file descriptor name `{name}` is listed more than once"
    runtimeByName := runtimeByName.insert name file
  for name in filesToGenerate do
    unless runtimeByName.contains name do
      throw s!"file_to_generate {name} was not found in protoc input"

  let mut sourceMap : Std.HashMap String FileDescriptorProto := {}
  if !request.source_file_descriptors.isEmpty then
    if request.source_file_descriptors.size != filesToGenerate.size then
      throw
        s!"source_file_descriptors must contain exactly one entry for each file_to_generate; got {request.source_file_descriptors.size}, expected {filesToGenerate.size}"
    for source in request.source_file_descriptors do
      let name ← source.name.getDM
        (throw "source_file_descriptors entry is missing its name")
      unless targetSet.contains name do
        throw
          s!"source_file_descriptors entry `{name}` is not listed in file_to_generate"
      if sourceMap.contains name then
        throw
          s!"source_file_descriptors entry `{name}` is listed more than once"
      let runtime ← runtimeByName[name]?.getDM
        (throw
          s!"source_file_descriptors entry `{name}` has no matching proto_file descriptor")
      let equivalent ←
        Protobuf.Plugin.DescriptorBoundary.runtimeEquivalent runtime source
      unless equivalent do
        throw
          s!"source_file_descriptors entry `{name}` does not match its stripped proto_file descriptor"
      sourceMap := sourceMap.insert name source
    for name in filesToGenerate do
      unless sourceMap.contains name do
        throw
          s!"source_file_descriptors is missing file_to_generate `{name}`"

  let protoFiles : Array FileDescriptorProto :=
    request.proto_file.map fun runtime =>
      match runtime.name >>= fun name => sourceMap[name]? with
      | some source =>
        Protobuf.Plugin.DescriptorBoundary.mergeSourceOnlyFields
          runtime source
      | none => runtime

  let desc : FileDescriptorSet := { file := protoFiles }

  let compileTargets (desc : FileDescriptorSet)
      (targets : Std.HashMap String PUnit) :
      Protobuf.Versions.M (Std.HashMap String (Array Command)) := do
    let reflectionDesc ← Protobuf.Versions.prepareFileDescriptorSet desc
    let reflectionFiles : Std.HashMap String FileDescriptorProto :=
      reflectionDesc.file.foldl (init := {}) fun files file =>
        match file.name with
        | some name => files.insert name file
        | none => files
    let desc := Protobuf.Versions.sanitizeFileDescriptorSet reflectionDesc
    let names ← desc.file.mapM fun (file : FileDescriptorProto) => do
      let some name := file.name | throw "file descriptor missing name"
      return name
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
      let reflectionFile :=
        file.name.bind (reflectionFiles[·]?) |>.getD file
      let cmds ←
        match file.syntax with
        | some stx =>
          if stx == "proto3" then
            Protobuf.Versions.Proto3.compile_file file reflectionFile
          else if stx == "proto2" then
            Protobuf.Versions.Proto2.compile_file file reflectionFile
          else if stx == "editions" then
            Protobuf.Versions.Editions.compile_file file reflectionFile
          else
            throw s!"{stx} is not supported yet"
        | none =>
          Protobuf.Versions.Proto2.compile_file file reflectionFile
      let name := file.name.getD ""
      if targets.contains name then
        outputs := outputs.insert name cmds
    return outputs

  let outputs ← Protobuf.Versions.M.run (compileTargets desc targetSet)

  let renderCommand (x : Command) : Except String String :=
    PrettyPrinter.command.pprintSafe x

  let renderCommands (cmds : Array Command) : Except String String := do
    return String.intercalate "\n\n" (← cmds.mapM renderCommand).toList

  let renderFile (imports : Array String) (cmds : Array Command) : Except String String := do
    let body ← renderCommands cmds
    let importLines := imports.toList.map fun m => s!"public import {m}"
    let header := String.intercalate "\n"
      [ "module"
      , ""
      , "public import Protobuf.Encoding"
      , "public import Protobuf.Base64"
      , "public import Protobuf.Reflection"
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
    if r.endsWith "\n" then return r
    else return r ++ "\n"

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
          let mod ← moduleNameFromPath dep
          let mod := withPrefix lean4Prefix mod
          if !mod.isEmpty && !seen.contains mod then
            seen := seen.insert mod
            out := out.push mod
      pure out
    let some cmds := outputs[name]?
      | throw s!"file_to_generate {name} was not found in protoc input"
    let content ← renderFile importModules cmds
    let outName ← outputFileName name
    let file : CodeGeneratorResponse.File := { name := some outName, content := some content }
    filesOut := filesOut.push file

  return supportedResponse filesOut

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
      -- `plugin.proto` requires generation failures to be returned in the
      -- response while the plugin itself exits successfully.  A non-zero exit
      -- is reserved for failures such as an unparseable request.
      pure (supportedResponse (error? := some err))
  let resultBin ← match result.encode with
    | .ok r => pure r
    | .error err =>
      stdErr.putStrLn s!"{exeName}: failed to serialize protobuf: {err}"
      return 1
  stdOut.write resultBin
  return 0
