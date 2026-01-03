module

public import Lean
public meta import Lake
public meta import Protobuf.Internal.Desc
public import Protobuf.Encoding.Builder
public import Protobuf.Encoding.Unwire
import Protobuf.Internal.Notation.Enum
import Protobuf.Internal.Notation.Message
import all Lean.Elab.App
public import Protobuf.Utils

open Lake DSL System
open Lean

public meta section

-- def load
#check Target

-- def compile_proto : Target FilePath
#check TextFilePath

#check buildArtifactUnlessUpToDate
#check LeanLibConfig
#check LeanLib

#check inputFile
#check inputFileCommand
#check inputFileAttr

-- public configuration ProtobufFileConfig (name : Name) where
--   /-- path to the `.proto` source file -/
--   path : FilePath := name.toString (escape := false)

-- public structure ConfigTarget (kind : Name) where
--   /-- The package the target belongs to. -/
--   pkg : Package
--   /-- The target's name. -/
--   name : Name
--   /-- The target's user-defined configuration. -/
--   config : ConfigType kind pkg.name name

-- #check elabInputfileCommand
-- attribute [command_elab] elabInputfileCommand

#check Target
#check LakeM
#check FetchM
#check SpawnM
#check ScriptM
#check getBuildDir

#check IO.FS.withTempFile

open Protobuf Internal Desc Notation


def compile_proto_ (srcFile : FilePath) (targetLeanPath : FilePath) : FetchM (Job FilePath) := do
  let inputJob ← inputFile srcFile (text := true)
  inputJob.mapM fun srcFile => do
    let a ← buildArtifactUnlessUpToDate srcFile (ext := "lean") (text := true) do
      let bin ← IO.FS.withTempFile fun h _ => do
        proc { cmd := "protoc", args := #[srcFile.toString] }
        h.readBinToEnd -- TODO: may be too large, make it incremental
      let data ← match (Binary.Get.run (Binary.getThe Encoding.Message) bin |>.toExcept) with
        | .ok data => pure data
        | .error e => error s!"failed to parse protoc output: {e}"
      let desc ← match FileDescriptorSet.fromMessage data with
        | .ok d => pure d
        | .error e => error s!"failed to parse protoc output: {e}"
      sorry
    return a.path

structure M.Context where
  currentMacroScope : Nat := 0
  ref : Syntax := mkNullNode
  currentNamePrefixRev : List String := []

structure M.State where
  nextMacroScope : Nat := 0
  types : NameTrie String := {}

abbrev M := ReaderT M.Context <| StateRefT M.State IO

@[inline]
def M.run : M α → IO α := fun x => x { } |>.run' {}

@[inline]
def wrapName : String → M Name := fun s c =>
  let rec go (ns : List String) : Name :=
    match ns with
    | [] => Name.anonymous
    | x :: ns => (go ns).str x
  return (go c.currentNamePrefixRev).str s

@[specialize]
def withNewNameLevel (n : String) (x : M α) : M α := fun c => x { c with currentNamePrefixRev := n :: c.currentNamePrefixRev }

@[specialize]
def withNewNameLevel? (n : Option String) (x : M α) : M α := fun c =>
  if let some n := n then
    x { c with currentNamePrefixRev := n :: c.currentNamePrefixRev }
  else
    x c

@[specialize]
def withPackageName (n : String) (x : M α) : M α := fun c =>
  let n := n.trim
  let xs := n.splitOn "."
  if xs.isEmpty then
    x c
  else
    x { c with currentNamePrefixRev := xs.reverse ++ c.currentNamePrefixRev }

@[specialize, always_inline]
protected def M.withFreshMacroScope {α} (x : M α) : M α := do
  let fresh ← modifyGetThe M.State (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }))
  withReader (fun ctx => { ctx with currentMacroScope := fresh }) x

def resolveName (raw : String) : M Name := do
  -- TODO: fully check string validity
  if raw.isEmpty then
    error s!"{decl_name%}: input is empty"
  let rec conc (ns : List String) : Name :=
    match ns with
    | [] => Name.anonymous
    | x :: ns => (conc ns).str x
  let leading := raw.rawStartPos.get raw
  if leading == '.' then
    let full := raw.drop 1
    let xs := full.splitOn "."
    return conc xs.reverse
  let name := raw
  let mut ns ← M.Context.currentNamePrefixRev <$> readThe M.Context
  let trie ← M.State.types <$> getThe M.State
  repeat
    let n := conc (name :: ns)
    if let some t := trie.find? n then
      if t == name then
        return n
    if ns.isEmpty then
      break
    ns := ns.tail
  error s!"{decl_name%}: {raw} cannot be resolved"

def registerType (raw : String) : M Unit := do
  let x ← wrapName raw
  modifyThe M.State (fun s => { s with types := s.types.insert x raw })

@[always_inline]
instance : MonadRef M where
  getRef := fun c => return c.ref
  withRef stx x := fun c => x {c with ref := stx}

@[always_inline]
instance : MonadQuotation M where
  getCurrMacroScope := fun c => return c.currentMacroScope
  getContext := return .anonymous
  withFreshMacroScope := M.withFreshMacroScope

def read_proto (srcFile : FilePath) : IO FileDescriptorSet := do
  let bin ← IO.FS.withTempFile fun h tmp => do
    _ ← IO.Process.run { cmd := "protoc", args := #[srcFile.toString, "-o", tmp.toString] }
    h.readBinToEnd -- TODO: may be too large, make it incremental
  let data ← match (Binary.Get.run (Binary.getThe Encoding.Message) bin |>.toExcept) with
    | .ok data => pure data
    | .error e => error s!"failed to parse protoc output: {e}"
  let desc ← match FileDescriptorSet.fromMessage data with
    | .ok d => pure d
    | .error e => error s!"failed to parse protoc output: {e}"

-- proto3

local macro "get!! " src:term:max " ! " err:term : term =>
  ``(Option.getDM $src (error s!"{decl_name%}: {$err}"))

local macro "get!! " src:term:max : term => ``(Option.getDM $src (error s!"{decl_name%}"))

local macro "is_true!! " v:term:max : term => ``(Option.getD $v false)

open Parser Term in
local syntax:min term "&." noWs (fieldIdx <|> rawIdent) argument* : term

local macro_rules
  | `($x&.%$tk$f $args*) => `($x >>= (fun x => x |>.%$tk$f $args*))

local syntax ppRealGroup(ppRealFill(ppIndent("if! " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

local macro_rules
  | `(if! $c then $t else $e) => `(if (Option.getD $c false) then $t else $e)

local prefix:min "!! " => Option.getD (dflt := false)

-- enum TestE [allow_alias = true] {
--   A = 1;
--   B = 1;
-- }

-- def output : M Unit := do
--   let x ← read_proto "Test/A.proto"
--   println! "{repr x}"

-- #eval output.run

def compile_enum (e : EnumDescriptorProto) : M (Array Command) := do
  let enumName ← get!! e.name
  registerType enumName
  let typeName ← wrapName enumName
  let typeId := mkIdent typeName
  let vNames ← e.value.mapM fun v => get!! v.name
  let vIds := vNames.map fun x => Lean.mkIdent (Name.mkStr1 x)
  let vNums ← e.value.mapM fun v => get!! v.number
  let vNumsQ := vNums.map fun x => quote x.toUInt32.toNat
  let commands ← IO.mkRef #[]
  let commitM (c : M Command) := c >>= fun x => commands.modify fun cs => cs.push x
  let enum_options_stx ← do
    let mut es := #[]
    if !! e.options&.allow_alias then
      es := es.push (← `(options_entry| allow_alias = true))
    `(options| [$es,*])
  commitM `(enum $typeId $enum_options_stx { $[$vIds = $vNumsQ;]* })
  if !! e.options&.deprecated then
    commitM `(attribute [deprecated "protobuf: deprecated enum"] $typeId)
  for v in e.value, fieldNameId in vIds do
    if !! v.options&.deprecated then
      commitM `(attribute [deprecated "protobuf: deprecated field"] $fieldNameId)
  commands.get

-- def compile_message_field (field : FieldDescriptorProto) : M (Array Command) := do
--   sorry

partial def compile_message (msg : DescriptorProto) : M (Array Command) := withNewNameLevel? msg.name do
  let es ← msg.enum_type.flatMapM compile_enum
  let ms ← msg.nested_type.flatMapM compile_message
  -- return es ++ ms
  let msgName ← get!! msg.name
  registerType msgName
  let typeName ← wrapName msgName
  let typeId := mkIdent typeName
  let names ← msg.field.mapM fun v => get!! v.name
  let ids := names.map fun x => Lean.mkIdent (Name.mkStr1 x)
  let types ← msg.field.mapM fun field => do
    let t := field.type
    pure ()
  let nums ← msg.field.mapM fun v => get!! v.number
  let numsQ := nums.map fun x => quote x.toUInt32.toNat
  let commands ← IO.mkRef #[]
  let commitM (c : M Command) := c >>= fun x => commands.modify fun cs => cs.push x

  commitM `(message $typeId { $[A $ids:ident = $numsQ;]* })
  if !! msg.options&.deprecated then
    commitM `(attribute [deprecated "protobuf: deprecated message"] $typeId)
  let o := msg.options&.deprecated
  let o := msg.options&.map_entry
  sorry

def compile_file (file : FileDescriptorProto) : M (Array Command) := withPackageName (file.package.getD "") do
  let es ← file.enum_type.flatMapM compile_enum
  let ms ← file.message_type.flatMapM compile_message
  return es ++ ms

def compile_proto (desc : FileDescriptorSet) : M (Array Command) := do
  let names ← desc.file.mapM fun x => get!! x.name
  let deps := names.zip <| desc.file.map fun x => x.dependency
  let deps := Std.HashMap.ofList deps.toList
  let sortedNames := names.topoSortSCCHash deps |>.flatten
  let sorted := desc.file.toList.mergeSort (fun x y => sortedNames.idxOf x.name.get! ≤ sortedNames.idxOf y.name.get!)
  sorted.toArray.flatMapM compile_file

elab "#test" : command => do
  let x ← read_proto "Test/A.proto"
  let commands ← compile_proto x |>.run
  Elab.Command.runTermElabM fun _ => do
    logInfo m!"{commands}"
  commands.forM Elab.Command.elabCommand

-- #test

-- #check test.a.T.N
