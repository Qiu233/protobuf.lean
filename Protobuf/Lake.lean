module

public import Lean
public meta import Lake
public meta import Protobuf.Internal.Desc
public import Protobuf.Encoding.Builder
public import Protobuf.Encoding.Unwire
import Protobuf.Internal.Notation.Enum
import Protobuf.Internal.Notation.Message
import Protobuf.Internal.Notation.Mutual
import all Lean.Elab.App
public import Protobuf.Utils

open Lake DSL System
open Lean

public meta section

open Protobuf Internal Desc Encoding Notation

private def packagePrefixRev (pkg : String) : List String :=
  let pkg := pkg.trim
  if pkg.isEmpty then
    []
  else
    (pkg.splitOn ".").reverse

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
private def withNamePrefix (prefixRev : List String) (x : M α) : M α := fun c =>
  x { c with currentNamePrefixRev := prefixRev }

private def nameFromPrefixRev (prefixRev : List String) (raw : String) : Name :=
  let rec go (ns : List String) : Name :=
    match ns with
    | [] => Name.anonymous
    | x :: ns => (go ns).str x
  (go prefixRev).str raw

private def builtinIdent (s : String) : TSyntax `ident :=
  mkIdent (Name.mkStr1 s)

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
    _ ← IO.Process.run { cmd := "protoc", args := #[srcFile.toString, "--descriptor_set_out", tmp.toString] }
    h.readBinToEnd -- TODO: may be too large, make it incremental
  let data ← match (Binary.Get.run (Binary.getThe Encoding.Message) bin |>.toExcept) with
    | .ok data => pure data
    | .error e => error s!"failed to parse protoc output: {e}"
  let desc ← match FileDescriptorSet.fromMessage data with
    | .ok d => pure d
    | .error e => error s!"failed to parse protoc output: {e}"
  return desc

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

structure DeclOutput where
  decl : Command
  extra : Array Command := #[]

def compile_enum (e : EnumDescriptorProto) : M DeclOutput := do
  let enumName ← get!! e.name
  registerType enumName
  let typeName ← wrapName enumName
  let typeId := mkIdent typeName
  let vNames ← e.value.mapM fun v => get!! v.name
  let vIds := vNames.map fun x => Lean.mkIdent (Name.mkStr1 x)
  let vNums ← e.value.mapM fun v => get!! v.number
  let vNumsQ := vNums.map fun x => quote x.toUInt32.toNat
  let extras ← IO.mkRef #[]
  let commitM (c : M Command) := c >>= fun x => extras.modify fun cs => cs.push x
  let enum_options_stx ← do
    let mut es := #[]
    if !! e.options&.allow_alias then
      es := es.push (← `(options_entry| allow_alias = true))
    `(options| [$es,*])
  let decl ← `(enum $typeId $enum_options_stx { $[$vIds = $vNumsQ;]* })
  if !! e.options&.deprecated then
    commitM `(attribute [deprecated "protobuf: deprecated enum"] $typeId)
  for v in e.value, fieldNameId in vIds do
    if !! v.options&.deprecated then
      commitM `(attribute [deprecated "protobuf: deprecated field"] $fieldNameId)
  return { decl, extra := (← extras.get) }

structure OneofGroup where
  name : String
  leanType : String
  fields : Array FieldDescriptorProto

structure MsgItem where
  prefixRev : List String
  name : String
  desc : DescriptorProto
  normalFields : Array FieldDescriptorProto
  oneofGroups : Array OneofGroup

structure EnumItem where
  prefixRev : List String
  name : String
  desc : EnumDescriptorProto

private def MsgItem.fullName (item : MsgItem) : Name :=
  nameFromPrefixRev item.prefixRev item.name

structure OneofItem where
  prefixRev : List String
  name : String
  leanType : String
  fields : Array FieldDescriptorProto

private def OneofItem.fullName (item : OneofItem) : Name :=
  nameFromPrefixRev item.prefixRev item.name

private def oneofIndexNat (idx : Int32) : M Nat := do
  if idx < 0 then
    error s!"{decl_name%}: negative oneof_index: {idx}"
  return idx.toUInt32.toNat

private def splitMessageFields (msg : DescriptorProto) : M (Array FieldDescriptorProto × Array OneofGroup) := do
  let mut normalFields := #[]
  let mut groups : Std.HashMap Nat (Array FieldDescriptorProto) := {}
  for field in msg.field do
    if let some idx := field.oneof_index then
      if field.proto3_optional.getD false then
        normalFields := normalFields.push field
      else
        let idxNat ← oneofIndexNat idx
        if idxNat >= msg.oneof_decl.size then
          error s!"{decl_name%}: oneof_index {idxNat} out of bounds"
        groups := groups.alter idxNat (some <| ·.getD #[] |>.push field)
    else
      normalFields := normalFields.push field
  let mut oneofGroups := #[]
  for i in List.range msg.oneof_decl.size do
    if let some fields := groups[i]? then
      if !fields.isEmpty then
        let decl := msg.oneof_decl[i]!
        let name ← get!! decl.name
        oneofGroups := oneofGroups.push { name, fields, leanType := s!"{name}_Type" }
  return (normalFields, oneofGroups)

private partial def collect_messages (prefixRev : List String) (msgs : Array DescriptorProto) : M (Array MsgItem) := do
  let mut out := #[]
  for msg in msgs do
    let name ← get!! msg.name
    let (normalFields, oneofGroups) ← splitMessageFields msg
    out := out.push { prefixRev, name, desc := msg, normalFields, oneofGroups }
    out := out ++ (← collect_messages (name :: prefixRev) msg.nested_type)
  return out

private partial def collect_enums (prefixRev : List String) (enums : Array EnumDescriptorProto) : M (Array EnumItem) := do
  let mut out := #[]
  for e in enums do
    let name ← get!! e.name
    out := out.push { prefixRev, name, desc := e }
  return out

private partial def collect_enums_in_messages (prefixRev : List String) (msgs : Array DescriptorProto) : M (Array EnumItem) := do
  let mut out := #[]
  for msg in msgs do
    let name ← get!! msg.name
    out := out ++ (← collect_enums (name :: prefixRev) msg.enum_type)
    out := out ++ (← collect_enums_in_messages (name :: prefixRev) msg.nested_type)
  return out

private def collect_oneofs_from_messages (msgs : Array MsgItem) : Array OneofItem :=
  msgs.foldl (init := #[]) fun acc msg =>
    msg.oneofGroups.foldl (init := acc) fun acc g =>
      acc.push { prefixRev := msg.name :: msg.prefixRev, name := g.name, fields := g.fields, leanType := g.leanType }

private def field_type_ident (field : FieldDescriptorProto) : M (TSyntax `ident) := do
  let t ← get!! field.type
  match t with
  | .«Unknown.Value» _ => error s!"{decl_name%}: unknown field type"
  | .TYPE_DOUBLE => pure <| builtinIdent "double"
  | .TYPE_FLOAT => pure <| builtinIdent "float"
  | .TYPE_INT64 => pure <| builtinIdent "int64"
  | .TYPE_UINT64 => pure <| builtinIdent "uint64"
  | .TYPE_INT32 => pure <| builtinIdent "int32"
  | .TYPE_FIXED64 => pure <| builtinIdent "fixed64"
  | .TYPE_FIXED32 => pure <| builtinIdent "fixed32"
  | .TYPE_BOOL => pure <| builtinIdent "bool"
  | .TYPE_STRING => pure <| builtinIdent "string"
  | .TYPE_GROUP => error s!"{decl_name%}: groups are not supported"
  | .TYPE_MESSAGE =>
      let raw ← get!! field.type_name
      let resolved ← resolveName raw
      pure <| mkIdent resolved
  | .TYPE_BYTES => pure <| builtinIdent "bytes"
  | .TYPE_UINT32 => pure <| builtinIdent "uint32"
  | .TYPE_ENUM =>
      let raw ← get!! field.type_name
      let resolved ← resolveName raw
      pure <| mkIdent resolved
  | .TYPE_SFIXED32 => pure <| builtinIdent "sfixed32"
  | .TYPE_SFIXED64 => pure <| builtinIdent "sfixed64"
  | .TYPE_SINT32 => pure <| builtinIdent "sint32"
  | .TYPE_SINT64 => pure <| builtinIdent "sint64"

private def field_modifier? (field : FieldDescriptorProto) : M (Option (TSyntax ``message_entry_modifier)) := do
  let label := field.label.getD .LABEL_OPTIONAL
  match label with
  | .«Unknown.Value» _ => error s!"{decl_name%}: unknown cardinality"
  | .LABEL_REPEATED => some <$> `(message_entry_modifier| repeated)
  | .LABEL_REQUIRED => some <$> `(message_entry_modifier| required)
  | .LABEL_OPTIONAL => some <$> `(message_entry_modifier| optional)

private def field_options? (field : FieldDescriptorProto) : M (Option (TSyntax ``options)) := do
  let mut entries := #[]
  if let some packed := field.options&.packed then
    entries := entries.push (← `(options_entry| packed = $(quote packed)))
  if !! field.options&.deprecated then
    entries := entries.push (← `(options_entry| deprecated = true))
  if entries.isEmpty then
    return none
  some <$> `(options| [$entries,*])

private def ensure_oneof_field_ok (field : FieldDescriptorProto) : M Unit := do
  let label := field.label.getD .LABEL_OPTIONAL
  match label with
  | .«Unknown.Value» _ => error s!"{decl_name%}: unknown cardinality"
  | .LABEL_REPEATED => error s!"{decl_name%}: oneof fields cannot be repeated"
  | .LABEL_REQUIRED => error s!"{decl_name%}: oneof fields cannot be required"
  | .LABEL_OPTIONAL => pure ()

private def compile_oneof (item : OneofItem) : M DeclOutput := do
  let oneofName := item.name
  registerType oneofName
  let typeName := nameFromPrefixRev item.prefixRev item.leanType
  let typeId := mkIdent typeName
  let names ← item.fields.mapM fun v => get!! v.name
  let ids := names.map fun x => Lean.mkIdent (Name.mkStr1 x)
  for field in item.fields do
    ensure_oneof_field_ok field
  let types ← item.fields.mapM field_type_ident
  let nums ← item.fields.mapM fun v => get!! v.number
  let numsQ := nums.map fun x => quote x.toUInt32.toNat
  let opts ← item.fields.mapM field_options?
  let noneMod? : Array (Option (TSyntax ``message_entry_modifier)) := ids.map (fun _ => Option.none)
  let decl ← `(oneof $typeId { $[ $[$noneMod?]? $types $ids:ident = $numsQ $[$opts]?;]* })
  return { decl }

partial def compile_message (item : MsgItem) : M DeclOutput := do
  let msg := item.desc
  if !msg.extension.isEmpty then
    error s!"{decl_name%}: extensions are not supported"
  let msgName := item.name
  registerType msgName
  let typeName := nameFromPrefixRev item.prefixRev msgName
  let typeId := mkIdent typeName
  let names ← item.normalFields.mapM fun v => get!! v.name
  let ids := names.map fun x => Lean.mkIdent (Name.mkStr1 x)
  let mods ← item.normalFields.mapM field_modifier?
  let types ← item.normalFields.mapM field_type_ident
  let nums ← item.normalFields.mapM fun v => get!! v.number
  let numsQ := nums.map fun x => quote x.toUInt32.toNat
  let opts ← item.normalFields.mapM field_options?
  let oneofNames := item.oneofGroups.map (·.name)
  let oneofIds := oneofNames.map fun x => Lean.mkIdent (Name.mkStr1 x)
  let oneofTypes := item.oneofGroups.map fun g =>
    mkIdent (nameFromPrefixRev (msgName :: item.prefixRev) g.leanType)
  let oneofNums := Array.replicate item.oneofGroups.size (quote (0 : Nat))
  let extras ← IO.mkRef #[]
  let commitM (c : M Command) := c >>= fun x => extras.modify fun cs => cs.push x
  let noneMod? : Array (Option (TSyntax ``message_entry_modifier)) := oneofIds.map (fun _ => Option.none)
  let decl ← `(message $typeId { $[$[$mods]? $types $ids:ident = $numsQ $[$opts]?;]* $[ $[$noneMod?]? $oneofTypes $oneofIds:ident = $oneofNums;]* })
  if !! msg.options&.deprecated then
    commitM `(attribute [deprecated "protobuf: deprecated message"] $typeId)
  for fieldName in names, field in item.normalFields do
    if !! field.options&.deprecated then
      let fieldId := mkIdent (typeName.str fieldName)
      commitM `(attribute [deprecated "protobuf: deprecated field"] $fieldId)
  return { decl, extra := (← extras.get) }

def compile_file (file : FileDescriptorProto) : M (Array Command) := do
  if let some stx := file.syntax then
    if stx != "proto3" then
      error s!"{stx} is not supported yet"
  else
    error "proto2 is not supported yet"
  let prefixRev := packagePrefixRev (file.package.getD "")
  let enumItems := (← collect_enums prefixRev file.enum_type) ++ (← collect_enums_in_messages prefixRev file.message_type)
  let msgItems ← collect_messages prefixRev file.message_type
  let oneofItems := collect_oneofs_from_messages msgItems

  for item in enumItems do
    withNamePrefix item.prefixRev (registerType item.name)
  for item in msgItems do
    withNamePrefix item.prefixRev (registerType item.name)
  for item in oneofItems do
    withNamePrefix item.prefixRev (registerType item.name)

  let mut enumsOut := #[]
  for item in enumItems do
    let out ← withNamePrefix item.prefixRev (compile_enum item.desc)
    enumsOut := enumsOut.push out.decl ++ out.extra

  let msgNames := msgItems.map (·.fullName)
  let oneofNames := oneofItems.map (·.fullName)
  let msgNameSet := msgNames.foldl (fun s n => s.insert n ()) (∅ : Std.HashMap Name PUnit)
  let oneofNameSet := oneofNames.foldl (fun s n => s.insert n ()) (∅ : Std.HashMap Name PUnit)
  let nodeNames := msgNames ++ oneofNames
  let mut deps : Std.HashMap Name (Array Name) := ∅
  for item in msgItems do
    let mut ds := #[]
    for field in item.normalFields do
      if field.type matches some .TYPE_MESSAGE then
        let raw ← get!! field.type_name
        let dep ← withNamePrefix item.prefixRev (resolveName raw)
        if msgNameSet.contains dep then
          ds := ds.push dep
    for g in item.oneofGroups do
      let oneofName := nameFromPrefixRev (item.name :: item.prefixRev) g.name
      if oneofNameSet.contains oneofName then
        ds := ds.push oneofName
    deps := deps.insert item.fullName ds
  for item in oneofItems do
    let mut ds := #[]
    for field in item.fields do
      if field.type matches some .TYPE_MESSAGE then
        let raw ← get!! field.type_name
        let dep ← withNamePrefix item.prefixRev (resolveName raw)
        if msgNameSet.contains dep then
          ds := ds.push dep
    deps := deps.insert item.fullName ds

  let sccs := nodeNames.topoSortSCCHash deps |>.reverse
  let msgMap := msgItems.foldl (fun m i => m.insert i.fullName i) (∅ : Std.HashMap Name MsgItem)
  let oneofMap := oneofItems.foldl (fun m i => m.insert i.fullName i) (∅ : Std.HashMap Name OneofItem)
  let mut out := #[]
  for scc in sccs do
    if scc.size == 1 then
      let name := scc[0]!
      if let some item := msgMap[name]? then
        let res ← withNamePrefix item.prefixRev (compile_message item)
        out := out.push res.decl ++ res.extra
      else if let some item := oneofMap[name]? then
        let res ← withNamePrefix item.prefixRev (compile_oneof item)
        out := out.push res.decl ++ res.extra
      else
        error s!"{decl_name%}: missing declaration for {name}"
    else
      let mut decls : Array Command := #[]
      let mut extras : Array Command := #[]
      for name in scc do
        if let some item := msgMap[name]? then
          let res ← withNamePrefix item.prefixRev (compile_message item)
          decls := decls.push res.decl
          extras := extras ++ res.extra
        else if let some item := oneofMap[name]? then
          let res ← withNamePrefix item.prefixRev (compile_oneof item)
          decls := decls.push res.decl
          extras := extras ++ res.extra
        else
          error s!"{decl_name%}: missing declaration for {name}"
      let declsStx : Array (TSyntax ``proto_decl) := decls.map (fun c => mkNode ``proto_decl #[c.raw])
      let mutualCmd ← `(proto_mutual { $[$declsStx]* })
      out := out.push mutualCmd ++ extras
  return enumsOut ++ out

def compile_proto (desc : FileDescriptorSet) : M (Array Command) := do
  let names ← desc.file.mapM fun x => get!! x.name
  let deps := names.zip <| desc.file.map fun x => x.dependency
  let deps := Std.HashMap.ofList deps.toList
  let sccs := names.topoSortSCCHash deps |>.reverse
  for scc in sccs do
    if scc.size > 1 then
      let cycle := scc.toList
      error s!"{decl_name%}: mutual recursion in file imports: {String.intercalate ", " cycle}"
  let sortedNames := sccs.flatten
  let sorted := desc.file.toList.mergeSort (fun x y => sortedNames.idxOf x.name.get! ≤ sortedNames.idxOf y.name.get!)
  sorted.toArray.flatMapM compile_file

private def renderCommands (cmds : Array Command) : IO String := do
  unsafe Lean.enableInitializersExecution
  let env ← Lean.importModules #[`Protobuf.Internal.Notation] {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<proto>", fileMap := default }
  let st : Core.State := { env := env }
  let mut out := ""
  for cmd in cmds do
    let (fmt, _) ← (Lean.PrettyPrinter.ppCommand cmd).toIO ctx st
    out := out ++ fmt.pretty ++ "\n\n"
  return out

def compile_proto_job (srcFile : FilePath) (targetLeanPath : FilePath) : FetchM (Job FilePath) := do
  let inputJob ← inputFile srcFile (text := true)
  inputJob.mapM fun srcFile => do
    let a ← buildArtifactUnlessUpToDate targetLeanPath (ext := "lean") (text := true) do
      let desc ← read_proto srcFile
      let commands ← compile_proto desc |>.run
      let body ← renderCommands commands
      let header := String.intercalate "\n"
          [ "module"
          , "meta import Protobuf.Internal.Notation"
          , "public import Protobuf.Encoding"
          , "open Protobuf Encoding Internal Notation"
          , ""
          ]
      IO.FS.writeFile targetLeanPath (header ++ body)
    return a.path

-- elab "#test" : command => do
--   let x ← read_proto "Test/A.proto"
--   let commands ← compile_proto x |>.run
--   Elab.Command.runTermElabM fun _ => do
--     logInfo m!"{commands}"
--   commands.forM Elab.Command.elabCommand

-- #test

-- def output : M Unit := do
--   let x ← read_proto "Test/A.proto"
--   println! "{repr x}"

-- #eval output.run

-- -- def load
-- #check Target

-- -- def compile_proto : Target FilePath
-- #check TextFilePath

-- #check buildArtifactUnlessUpToDate
-- #check LeanLibConfig
-- #check LeanLib

-- #check inputFile
-- #check inputFileCommand
-- #check inputFileAttr

-- -- public configuration ProtobufFileConfig (name : Name) where
-- --   /-- path to the `.proto` source file -/
-- --   path : FilePath := name.toString (escape := false)

-- -- public structure ConfigTarget (kind : Name) where
-- --   /-- The package the target belongs to. -/
-- --   pkg : Package
-- --   /-- The target's name. -/
-- --   name : Name
-- --   /-- The target's user-defined configuration. -/
-- --   config : ConfigType kind pkg.name name

-- -- #check elabInputfileCommand
-- -- attribute [command_elab] elabInputfileCommand

-- #check Target
-- #check LakeM
-- #check FetchM
-- #check SpawnM
-- #check ScriptM
-- #check getBuildDir

-- #check IO.FS.withTempFile

-- syntax (name := compileProtoCommand) "compile_proto_file " str " => " str : command

-- open Lean Elab Command in

-- @[command_elab compileProtoCommand]
-- def elabCommand : Command.CommandElab := fun stx => do
--   let `(compileProtoCommand| compile_proto_file $pathStx:str => $moduleStx:str) := stx | throwUnsupportedSyntax
--   let path := FilePath.mk pathStx.getString
--   let module := FilePath.mk moduleStx.getString
--   sorry
