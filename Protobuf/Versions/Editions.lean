module

import Protobuf.Notation
public import Protobuf.Internal.Desc
public import Protobuf.Utils
public import Protobuf.Versions.Basic

open Lean

public section

set_option hygiene false

namespace Protobuf.Versions.Editions

open Internal.Desc Encoding Notation

structure DeclOutput where
  decl : Command
  extra : Array Command := #[]

structure ResolvedFeatures where
  field_presence : FeatureSet.FieldPresence
  enum_type : FeatureSet.EnumType
  repeated_field_encoding : FeatureSet.RepeatedFieldEncoding
  utf8_validation : FeatureSet.Utf8Validation
  message_encoding : FeatureSet.MessageEncoding
  json_format : FeatureSet.JsonFormat

private def defaults_for_edition (ed : Edition) : M ResolvedFeatures := do
  match ed with
  | .EDITION_2023 | .EDITION_2024 =>
      return {
        field_presence := .EXPLICIT
        enum_type := .OPEN
        repeated_field_encoding := .PACKED
        utf8_validation := .VERIFY
        message_encoding := .LENGTH_PREFIXED
        json_format := .ALLOW
      }
  | _ =>
      throw s!"{decl_name%}: unsupported edition for editions syntax: {repr ed}"

private def merge_features (base : ResolvedFeatures) (over? : Option FeatureSet) : ResolvedFeatures :=
  match over? with
  | none => base
  | some f => {
      field_presence := f.field_presence.getD base.field_presence
      enum_type := f.enum_type.getD base.enum_type
      repeated_field_encoding := f.repeated_field_encoding.getD base.repeated_field_encoding
      utf8_validation := f.utf8_validation.getD base.utf8_validation
      message_encoding := f.message_encoding.getD base.message_encoding
      json_format := f.json_format.getD base.json_format
    }

private def resolve_file_features (file : FileDescriptorProto) : M ResolvedFeatures := do
  let ed ← file.edition.getDM (throw s!"{decl_name%}: editions syntax requires file.edition")
  let base ← defaults_for_edition ed
  return merge_features base (file.options&.features)

def compile_enum (e : EnumDescriptorProto) (features : ResolvedFeatures) : M DeclOutput := do
  match features.enum_type with
  | .«Unknown.Value» _ => throw s!"{decl_name%}: enum type is unknown"
  | .ENUM_TYPE_UNKNOWN =>
      throw s!"{decl_name%}: enum_type is unknown"
  | .CLOSED =>
      throw s!"{decl_name%}: enum_type = CLOSED is not supported"
  | .OPEN => pure ()
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
  features : ResolvedFeatures

structure MsgItem where
  prefixRev : List String
  name : String
  desc : DescriptorProto
  normalFields : Array FieldDescriptorProto
  oneofGroups : Array OneofGroup
  features : ResolvedFeatures

structure EnumItem where
  prefixRev : List String
  name : String
  desc : EnumDescriptorProto
  features : ResolvedFeatures

private def MsgItem.fullName (item : MsgItem) : Name :=
  Versions.nameFromPrefixRev item.prefixRev item.name

structure OneofItem where
  prefixRev : List String
  name : String
  leanType : String
  fields : Array FieldDescriptorProto
  features : ResolvedFeatures

private def OneofItem.fullName (item : OneofItem) : Name :=
  Versions.nameFromPrefixRev item.prefixRev item.name

private def oneofIndexNat (idx : Int32) : M Nat := do
  if idx < 0 then
    throw s!"{decl_name%}: negative oneof_index: {idx}"
  return idx.toUInt32.toNat

private def splitMessageFields (msg : DescriptorProto) (msgFeatures : ResolvedFeatures) :
    M (Array FieldDescriptorProto × Array OneofGroup) := do
  let mut normalFields := #[]
  let mut groups : Std.HashMap Nat (Array FieldDescriptorProto) := {}
  for field in msg.field do
    if let some idx := field.oneof_index then
      let idxNat ← oneofIndexNat idx
      if idxNat >= msg.oneof_decl.size then
        throw s!"{decl_name%}: oneof_index {idxNat} out of bounds"
      groups := groups.alter idxNat (some <| ·.getD #[] |>.push field)
    else
      normalFields := normalFields.push field
  let mut oneofGroups := #[]
  for i in List.range msg.oneof_decl.size do
    if let some fields := groups[i]? then
      if !fields.isEmpty then
        let decl := msg.oneof_decl[i]!
        let name ← get!! decl.name
        let features := merge_features msgFeatures (decl.options&.features)
        oneofGroups := oneofGroups.push { name, fields, leanType := s!"{name}_Type", features }
  return (normalFields, oneofGroups)

private partial def collect_messages (prefixRev : List String) (msgs : Array DescriptorProto)
    (parentFeatures : ResolvedFeatures) : M (Array MsgItem) := do
  let mut out := #[]
  for msg in msgs do
    let name ← get!! msg.name
    let msgFeatures := merge_features parentFeatures (msg.options&.features)
    let (normalFields, oneofGroups) ← splitMessageFields msg msgFeatures
    out := out.push { prefixRev, name, desc := msg, normalFields, oneofGroups, features := msgFeatures }
    out := out ++ (← collect_messages (name :: prefixRev) msg.nested_type msgFeatures)
  return out

private partial def collect_enums (prefixRev : List String) (enums : Array EnumDescriptorProto)
    (parentFeatures : ResolvedFeatures) : M (Array EnumItem) := do
  let mut out := #[]
  for e in enums do
    let name ← get!! e.name
    let features := merge_features parentFeatures (e.options&.features)
    out := out.push { prefixRev, name, desc := e, features }
  return out

private partial def collect_enums_in_messages (prefixRev : List String) (msgs : Array DescriptorProto)
    (parentFeatures : ResolvedFeatures) : M (Array EnumItem) := do
  let mut out := #[]
  for msg in msgs do
    let name ← get!! msg.name
    let msgFeatures := merge_features parentFeatures (msg.options&.features)
    out := out ++ (← collect_enums (name :: prefixRev) msg.enum_type msgFeatures)
    out := out ++ (← collect_enums_in_messages (name :: prefixRev) msg.nested_type msgFeatures)
  return out

private def collect_oneofs_from_messages (msgs : Array MsgItem) : Array OneofItem :=
  msgs.foldl (init := #[]) fun acc msg =>
    msg.oneofGroups.foldl (init := acc) fun acc g =>
      acc.push {
        prefixRev := msg.name :: msg.prefixRev
        name := g.name
        fields := g.fields
        leanType := g.leanType
        features := g.features
      }

private def field_type_ident (field : FieldDescriptorProto) : M (TSyntax `ident) := do
  let t ← get!! field.type
  match t with
  | .«Unknown.Value» _ => throw s!"{decl_name%}: unknown field type"
  | .TYPE_DOUBLE => pure <| Versions.builtinIdent "double"
  | .TYPE_FLOAT => pure <| Versions.builtinIdent "float"
  | .TYPE_INT64 => pure <| Versions.builtinIdent "int64"
  | .TYPE_UINT64 => pure <| Versions.builtinIdent "uint64"
  | .TYPE_INT32 => pure <| Versions.builtinIdent "int32"
  | .TYPE_FIXED64 => pure <| Versions.builtinIdent "fixed64"
  | .TYPE_FIXED32 => pure <| Versions.builtinIdent "fixed32"
  | .TYPE_BOOL => pure <| Versions.builtinIdent "bool"
  | .TYPE_STRING => pure <| Versions.builtinIdent "string"
  | .TYPE_GROUP => throw s!"{decl_name%}: groups are not supported"
  | .TYPE_MESSAGE =>
      let raw ← get!! field.type_name
      let resolved ← resolveName raw
      pure <| mkIdent resolved
  | .TYPE_BYTES => pure <| Versions.builtinIdent "bytes"
  | .TYPE_UINT32 => pure <| Versions.builtinIdent "uint32"
  | .TYPE_ENUM =>
      let raw ← get!! field.type_name
      let resolved ← resolveName raw
      pure <| mkIdent resolved
  | .TYPE_SFIXED32 => pure <| Versions.builtinIdent "sfixed32"
  | .TYPE_SFIXED64 => pure <| Versions.builtinIdent "sfixed64"
  | .TYPE_SINT32 => pure <| Versions.builtinIdent "sint32"
  | .TYPE_SINT64 => pure <| Versions.builtinIdent "sint64"

private def map_entry_names (item : MsgItem) : M (Array (String × DescriptorProto)) := do
  let mut out := #[]
  for nested in item.desc.nested_type do
    if !! nested.options&.map_entry then
      let nested_name ← get!! nested.name
      let full_name := Versions.nameFromPrefixRev (item.name :: item.prefixRev) nested_name
      out := out.push ("." ++ full_name.toString, nested)
  return out

private def is_map_entry (desc : DescriptorProto) : Bool :=
  !! desc.options&.map_entry

private def map_entry_fields (entry : DescriptorProto) : M (FieldDescriptorProto × FieldDescriptorProto) := do
  let key? := entry.field.find? fun f => f.number == some (1 : Int32)
  let value? := entry.field.find? fun f => f.number == some (2 : Int32)
  let key ← key?.getDM (throw s!"{decl_name%}: map entry is missing key field")
  let value ← value?.getDM (throw s!"{decl_name%}: map entry is missing value field")
  return (key, value)

private def map_entry_desc? (map_entries : Array (String × DescriptorProto)) (field : FieldDescriptorProto) :
    M (Option DescriptorProto) := do
  let t ← get!! field.type
  if t != .TYPE_MESSAGE then
    return none
  let raw_type ← get!! field.type_name
  return (map_entries.find? (fun (n, _) => n == raw_type)).map Prod.snd

private def map_field_type? (item : MsgItem) (map_entries : Array (String × DescriptorProto))
    (field : FieldDescriptorProto) : M (Option (TSyntax ``message_field_type)) := do
  let entry? ← map_entry_desc? map_entries field
  let some entry := entry? | return none
  let label := field.label.getD .LABEL_OPTIONAL
  if label != .LABEL_REPEATED then
    throw s!"{decl_name%}: map field must be repeated"
  let (key_field, value_field) ← map_entry_fields entry
  let key_type ← field_type_ident key_field
  let value_type ← field_type_ident value_field
  let m ← `(message_field_type_map| map<$key_type, $value_type>)
  some <$> `(message_field_type| $m:message_field_type_map)

private def ensure_message_encoding_supported (field : FieldDescriptorProto) (features : ResolvedFeatures) : M Unit := do
  match features.message_encoding with
  | .«Unknown.Value» _ =>
      throw s!"{decl_name%}: message_encoding is unknown"
  | .MESSAGE_ENCODING_UNKNOWN =>
      throw s!"{decl_name%}: message_encoding is unknown"
  | .LENGTH_PREFIXED => pure ()
  | .DELIMITED =>
      let t ← get!! field.type
      if t == .TYPE_MESSAGE then
        throw s!"{decl_name%}: message_encoding = DELIMITED is not supported"
      else
        pure ()

private def field_modifier? (field : FieldDescriptorProto) (features : ResolvedFeatures) :
    M (Option (TSyntax ``message_entry_modifier)) := do
  let label ← field.label.getDM (throw s!"modifier is absent") -- always present
  match label with
  | .«Unknown.Value» _ => throw s!"{decl_name%}: unknown cardinality"
  | .LABEL_REPEATED => some <$> `(message_entry_modifier| repeated)
  | .LABEL_REQUIRED => some <$> `(message_entry_modifier| required)
  | .LABEL_OPTIONAL =>
      match features.field_presence with
      | .«Unknown.Value» _ =>
          throw s!"{decl_name%}: field_presence is unknown"
      | .FIELD_PRESENCE_UNKNOWN =>
          throw s!"{decl_name%}: field_presence is unknown"
      | .LEGACY_REQUIRED => some <$> `(message_entry_modifier| required)
      | .EXPLICIT => some <$> `(message_entry_modifier| optional)
      | .IMPLICIT => return none

private def is_packable (field : FieldDescriptorProto) : M Bool := do
  let t ← get!! field.type
  match t with
  | .«Unknown.Value» _ => throw s!"{decl_name%}: unknown field type"
  | .TYPE_STRING | .TYPE_GROUP | .TYPE_MESSAGE | .TYPE_BYTES => pure false
  | _ => pure true

private def field_options? (field : FieldDescriptorProto) (features : ResolvedFeatures) : M (Option (TSyntax ``options)) := do
  let mut entries := #[]
  if let some packed := field.options&.packed then
    entries := entries.push (← `(options_entry| packed = $(quote packed)))
  else
    let label := field.label.getD .LABEL_OPTIONAL
    if label == .LABEL_REPEATED && (← is_packable field) then
      match features.repeated_field_encoding with
      | .«Unknown.Value» _ =>
          throw s!"{decl_name%}: repeated_field_encoding is unknown"
      | .REPEATED_FIELD_ENCODING_UNKNOWN =>
          throw s!"{decl_name%}: repeated_field_encoding is unknown"
      | .PACKED =>
          entries := entries.push (← `(options_entry| packed = true))
      | .EXPANDED => pure ()
  if !! field.options&.deprecated then
    entries := entries.push (← `(options_entry| deprecated = true))
  if entries.isEmpty then
    return none
  some <$> `(options| [$entries,*])

private def ensure_oneof_field_ok (field : FieldDescriptorProto) : M Unit := do
  let label := field.label.getD .LABEL_OPTIONAL
  match label with
  | .«Unknown.Value» _ => throw s!"{decl_name%}: unknown cardinality"
  | .LABEL_REPEATED => throw s!"{decl_name%}: oneof fields cannot be repeated"
  | .LABEL_REQUIRED => throw s!"{decl_name%}: oneof fields cannot be required"
  | .LABEL_OPTIONAL => pure ()

private def compile_oneof (item : OneofItem) : M DeclOutput := do
  let oneofName := item.name
  registerType oneofName
  let typeName := Versions.nameFromPrefixRev item.prefixRev item.leanType
  let typeId := mkIdent typeName
  let names ← item.fields.mapM fun v => get!! v.name
  let ids := names.map fun x => Lean.mkIdent (Name.mkStr1 x)
  for field in item.fields do
    ensure_oneof_field_ok field
    let fieldFeatures := merge_features item.features (field.options&.features)
    ensure_message_encoding_supported field fieldFeatures
  let types ← item.fields.mapM fun field => do
    let m ← `(message_field_type_normal| $(← field_type_ident field):ident)
    `(message_field_type| $m:message_field_type_normal)
  let nums ← item.fields.mapM fun v => get!! v.number
  let numsQ := nums.map fun x => quote x.toUInt32.toNat
  let opts ← item.fields.mapM fun field => do
    let fieldFeatures := merge_features item.features (field.options&.features)
    field_options? field fieldFeatures
  let noneMod? : Array (Option (TSyntax ``message_entry_modifier)) := ids.map (fun _ => Option.none)
  let decl ← `(oneof $typeId { $[ $[$noneMod?]? $types $ids:ident = $numsQ $[$opts]?;]* })
  return { decl }

partial def compile_message (item : MsgItem) : M DeclOutput := do
  let msg := item.desc
  if !! msg.options&.message_set_wire_format then
    throw s!"{decl_name%}: message_set_wire_format is not supported"
  if !msg.extension.isEmpty then
    throw s!"{decl_name%}: extensions are not supported"
  let msgName := item.name
  registerType msgName
  let typeName := Versions.nameFromPrefixRev item.prefixRev msgName
  let typeId := mkIdent typeName
  let map_entries ← map_entry_names item
  let mut names := #[]
  let mut ids := #[]
  let mut mods := #[]
  let mut types : Array (TSyntax ``message_field_type) := #[]
  let mut nums := #[]
  let mut opts := #[]
  for field in item.normalFields do
    let name ← get!! field.name
    let fieldFeatures := merge_features item.features (field.options&.features)
    ensure_message_encoding_supported field fieldFeatures
    names := names.push name
    ids := ids.push (Lean.mkIdent (Name.mkStr1 name))
    nums := nums.push (← get!! field.number)
    opts := opts.push (← field_options? field fieldFeatures)
    if let some map_type ← map_field_type? item map_entries field then
      types := types.push map_type
      mods := mods.push none
    else
      types := types.push (← `(message_field_type| $(← field_type_ident field):ident))
      mods := mods.push (← field_modifier? field fieldFeatures)
  let numsQ := nums.map fun x => quote x.toUInt32.toNat
  let oneofNames := item.oneofGroups.map (·.name)
  let oneofIds := oneofNames.map fun x => Lean.mkIdent (Name.mkStr1 x)
  let oneofTypes ← item.oneofGroups.mapM fun g => do
    let c := mkIdent (Versions.nameFromPrefixRev (msgName :: item.prefixRev) g.leanType)
    let m ← `(message_field_type_normal| $c:ident)
    `(message_field_type| $m:message_field_type_normal)
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
  let fileFeatures ← resolve_file_features file
  let prefixRev := Versions.packagePrefixRev (file.package.getD "")
  let enumItems := (← collect_enums prefixRev file.enum_type fileFeatures) ++
    (← collect_enums_in_messages prefixRev file.message_type fileFeatures)
  let msgItemsAll ← collect_messages prefixRev file.message_type fileFeatures
  let msgItems := msgItemsAll.filter (fun item => !is_map_entry item.desc)
  let oneofItems := collect_oneofs_from_messages msgItems

  for item in enumItems do
    withNamePrefix item.prefixRev (registerType item.name)
  for item in msgItems do
    withNamePrefix item.prefixRev (registerType item.name)
  for item in oneofItems do
    withNamePrefix item.prefixRev (registerType item.name)

  let mut enumsOut := #[]
  for item in enumItems do
    let out ← withNamePrefix item.prefixRev (compile_enum item.desc item.features)
    enumsOut := enumsOut.push out.decl ++ out.extra

  let msgNames := msgItems.map (·.fullName)
  let oneofNames := oneofItems.map (·.fullName)
  let msgNameSet := msgNames.foldl (fun s n => s.insert n ()) (∅ : Std.HashMap Name PUnit)
  let oneofNameSet := oneofNames.foldl (fun s n => s.insert n ()) (∅ : Std.HashMap Name PUnit)
  let nodeNames := msgNames ++ oneofNames
  let mut deps : Std.HashMap Name (Array Name) := ∅
  for item in msgItems do
    let mut ds := #[]
    let map_entries ← map_entry_names item
    for field in item.normalFields do
      if let some entry ← map_entry_desc? map_entries field then
        let (_, value_field) ← map_entry_fields entry
        if value_field.type matches some .TYPE_MESSAGE then
          let raw ← get!! value_field.type_name
          let dep ← withNamePrefix item.prefixRev (resolveName raw)
          if msgNameSet.contains dep then
            ds := ds.push dep
      else if field.type matches some .TYPE_MESSAGE then
        let raw ← get!! field.type_name
        let dep ← withNamePrefix item.prefixRev (resolveName raw)
        if msgNameSet.contains dep then
          ds := ds.push dep
    for g in item.oneofGroups do
      let oneofName := Versions.nameFromPrefixRev (item.name :: item.prefixRev) g.name
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
        throw s!"{decl_name%}: missing declaration for {name}"
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
          throw s!"{decl_name%}: missing declaration for {name}"
      let declsStx : Array (TSyntax ``proto_decl) := decls.map (fun c => mkNode ``proto_decl #[c.raw])
      let mutualCmd ← `(proto_mutual { $[$declsStx]* })
      out := out.push mutualCmd ++ extras
  return enumsOut ++ out
