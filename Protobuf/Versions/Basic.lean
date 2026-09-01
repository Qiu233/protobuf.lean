module

public import Lean.Data.NameTrie
public meta import Lean.Parser
import Protobuf.Notation.Syntax
public import Protobuf.Internal.Desc
public import Protobuf.Base64
public import Protobuf.Reflection

open System Lean

public section

namespace Protobuf.Versions

open Encoding Notation google.protobuf

private def hexDigit (n : Nat) : Char :=
  "0123456789abcdef".toList[n]!

private def hexEncode (bytes : ByteArray) : String :=
  String.ofList <| bytes.data.toList.flatMap fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

/--
An injective declaration name derived from the UTF-8 spelling of a proto file
name. This prevents private initializer collisions when `#load_proto_file`
emits several files into one Lean module.
-/
def fileDescriptorInitializerName (fileName : String) : Name :=
  Name.mkStr1 s!"protobuf.fileDescriptor.{hexEncode fileName.toUTF8}"

private partial def chunkString (size : Nat) (value : String) : Array String :=
  let rec go (rest : String.Slice) (out : Array String) : Array String :=
    if rest.isEmpty then
      out
    else
      go (rest.drop size) (out.push (rest.take size).toString)
  go value.toSlice #[]

def protoFullName (prefixRev : List String) (name : String) : String :=
  String.intercalate "." (prefixRev.reverse ++ [name])

def leanGeneratedTypeMemberNames : Array String :=
  /-
  Names synthesized by Lean for structures/inductives used by protobuf
  messages, enums, and oneofs. A protobuf declaration or member may legally
  use every one of these spellings, but Lean places them in the same namespace
  as projections, constructors, and nested protobuf types.
  -/
  #["mk", "rec", "recOn", "casesOn", "below", "brecOn", "noConfusion",
    "noConfusionType", "ctorIdx", "ctorElim", "ctorElimType", "_sizeOf_1",
    "_sizeOf_inst"]

private def schemaNameComponent (name : String) : String :=
  /-
  A leading `_root_` component is Lean's root-namespace qualifier, but it is
  also a legal protobuf package or top-level type identifier. Encode the
  protobuf component as one impossible-to-source Lean name component so it
  cannot be mistaken for the qualifier deliberately generated for built-in
  google.protobuf references.
  -/
  if name == "_root_" || leanGeneratedTypeMemberNames.contains name then
    s!"{name}.protobuf"
  else
    name

protected def packagePrefixRev (pkg : String) : List String :=
  let pkg := pkg.trimAscii.toString
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

abbrev M := ReaderT M.Context $ StateRefT M.State $ ExceptT String BaseIO

@[inline]
def M.run : M α → Except String α := fun x => (unsafe unsafeBaseIO (x {} |>.run' {}))

@[noinline, nospecialize]
def withNamePrefix (prefixRev : List String) (x : M α) : M α := fun c =>
  x { c with currentNamePrefixRev := prefixRev }

protected def nameFromPrefixRev (prefixRev : List String) (raw : String) : Name :=
  let rec go (ns : List String) : Name :=
    match ns with
    | [] => Name.anonymous
    | x :: ns => (go ns).str (schemaNameComponent x)
  (go prefixRev).str (schemaNameComponent raw)

protected def builtinIdent (s : String) : TSyntax `ident :=
  mkIdent (Name.mkStr1 s)

@[inline]
def wrapName : String → M Name := fun s c =>
  let rec go (ns : List String) : Name :=
    match ns with
    | [] => Name.anonymous
    | x :: ns => (go ns).str (schemaNameComponent x)
  return (go c.currentNamePrefixRev).str (schemaNameComponent s)

@[noinline, nospecialize]
def withNewNameLevel (n : String) (x : M α) : M α := fun c => x { c with currentNamePrefixRev := n :: c.currentNamePrefixRev }

@[noinline, nospecialize]
def withNewNameLevel? (n : Option String) (x : M α) : M α := fun c =>
  if let some n := n then
    x { c with currentNamePrefixRev := n :: c.currentNamePrefixRev }
  else
    x c

@[noinline, nospecialize]
def withPackageName (n : String) (x : M α) : M α := fun c =>
  let n := n.trimAscii.toString
  let xs := n.splitOn "."
  if xs.isEmpty then
    x c
  else
    x { c with currentNamePrefixRev := xs.reverse ++ c.currentNamePrefixRev }

@[noinline, nospecialize]
protected def M.withFreshMacroScope {α} (x : M α) : M α := do
  let fresh ← modifyGetThe M.State (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }))
  withReader (fun ctx => { ctx with currentMacroScope := fresh }) x

def resolveName (raw : String) : M Name := do
  -- TODO: fully check string validity
  if raw.isEmpty then
    throw s!"{decl_name%}: input is empty"
  let rec conc (ns : List String) : Name :=
    match ns with
    | [] => Name.anonymous
    | x :: ns => (conc ns).str (schemaNameComponent x)
  let leading := raw.rawStartPos.get raw
  if leading == '.' then
    let full := raw.drop 1
    let xs := full.split "." |>.toList.map String.Slice.toString
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
  throw s!"{decl_name%}: {raw} cannot be resolved"

def registerType (raw : String) : M Unit := do
  let x ← wrapName raw
  modifyThe M.State (fun s => { s with types := s.types.insert x raw })

def reservedFieldNames : List String :=
  leanGeneratedTypeMemberNames.toList

def reservedEnumValueNames : List String :=
  leanGeneratedTypeMemberNames.toList

/--
Choose the generated Lean component for a real protobuf oneof.

The historical `${oneof}_Type` spelling remains the inductive name unless a
legal nested message or enum already owns it.  The fallback stores `.` inside
one Lean name component, which no valid protobuf identifier can occupy.
-/
def syntheticOneofTypeComponent
    (msg : DescriptorProto) (oneofName : String) : String :=
  let legacy := s!"{oneofName}_Type"
  let occupied :=
    msg.nested_type.any (fun nested => nested.name == some legacy) ||
    msg.enum_type.any (fun e => e.name == some legacy)
  if occupied then s!"{legacy}.protobuf.oneof" else legacy

private def reservedLeanName (name : String) : String :=
  /-
  Appending `_` is not collision-free for fields: protoc accepts both
  `rec` and `rec_` in one message (with a JSON-name warning).  A dot
  cannot occur in a protobuf identifier, while `Name.mkStr1` still represents
  the result as one Lean name component (printed as, for example,
  `«rec.protobuf»`).  Thus this namespace is disjoint from every field
  name a valid schema can supply.
  -/
  s!"{name}.protobuf"

def sanitizeFieldName (name : String) : String :=
  if reservedFieldNames.contains name then
    reservedLeanName name
  else
    name

def sanitizeEnumValueName (name : String) : String :=
  if reservedEnumValueNames.contains name then
    reservedLeanName name
  else
    name

def sanitizeFieldDescriptor (field : FieldDescriptorProto) : FieldDescriptorProto :=
  match field.name with
  | some name =>
      let name' := sanitizeFieldName name
      if name' == name then field else { field with name := some name' }
  | none => field

def sanitizeEnumValueDescriptor (value : EnumValueDescriptorProto) : EnumValueDescriptorProto :=
  match value.name with
  | some name =>
      let name' := sanitizeEnumValueName name
      if name' == name then value else { value with name := some name' }
  | none => value

def sanitizeOneofDescriptor
    (oneofDecl : OneofDescriptorProto) : OneofDescriptorProto :=
  match oneofDecl.name with
  | some name =>
      /-
      A real oneof contributes a projection to its containing Lean structure,
      so it occupies exactly the same namespace as an ordinary field.
      -/
      let name' := sanitizeFieldName name
      if name' == name then
        oneofDecl
      else
        { oneofDecl with name := some name' }
  | none => oneofDecl

def sanitizeEnumDescriptor (e : EnumDescriptorProto) : EnumDescriptorProto :=
  { e with value := e.value.map sanitizeEnumValueDescriptor }

partial def sanitizeDescriptor (msg : DescriptorProto) : DescriptorProto :=
  { msg with
    field := msg.field.map sanitizeFieldDescriptor
    extension := msg.extension.map sanitizeFieldDescriptor
    oneof_decl := msg.oneof_decl.map sanitizeOneofDescriptor
    nested_type := msg.nested_type.map sanitizeDescriptor
    enum_type := msg.enum_type.map sanitizeEnumDescriptor
  }

def sanitizeFileDescriptor (file : FileDescriptorProto) : FileDescriptorProto :=
  { file with
    message_type := file.message_type.map sanitizeDescriptor
    enum_type := file.enum_type.map sanitizeEnumDescriptor
    extension := file.extension.map sanitizeFieldDescriptor
  }

def sanitizeFileDescriptorSet (desc : FileDescriptorSet) : FileDescriptorSet :=
  { desc with file := desc.file.map sanitizeFileDescriptor }

scoped macro "get!! " src:term:max " ! " err:term : term =>
  ``(Option.getDM $src (throw s!"{decl_name%}: {$err}"))

scoped macro "get!! " src:term:max : term =>
  ``(Option.getDM $src (throw s!"{decl_name%}"))

private def validateDescriptorFieldNumber
    (context : String) (field : FieldDescriptorProto) : M Nat := do
  let name ← get!! field.name ! s!"{context}: field name is absent"
  let number ← get!! field.number ! s!"{context}.{name}: field number is absent"
  let value := number.toInt
  if value ≤ 0 || value > 536870911 then
    throw s!"{context}.{name}: field number {value} is outside 1..536870911"
  let n := value.toNat
  if 19000 ≤ n && n ≤ 19999 then
    throw s!"{context}.{name}: field number {n} is in the reserved range 19000..19999"
  return n

private def validateDescriptorFields
    (context : String) (fields : Array FieldDescriptorProto)
    (requireUniqueNumbers : Bool := true) : M Unit := do
  let mut names : Array String := #[]
  let mut numbers : Array Nat := #[]
  for field in fields do
    let name ← get!! field.name ! s!"{context}: field name is absent"
    if name.isEmpty then
      throw s!"{context}: field name is empty"
    if names.contains name then
      throw s!"{context}: field name `{name}` is declared more than once"
    names := names.push name
    let number ← validateDescriptorFieldNumber context field
    if requireUniqueNumbers && numbers.contains number then
      throw s!"{context}: field number {number} is declared more than once"
    numbers := numbers.push number
    discard <| get!! field.label ! s!"{context}.{name}: field label is absent"
    discard <| get!! field.type ! s!"{context}.{name}: field type is absent"

private abbrev FieldNumberRange := Nat × Nat

@[inline]
private def fieldNumberRangesOverlap
    (left right : FieldNumberRange) : Bool :=
  left.1 < right.2 && right.1 < left.2

/--
Validate the half-open extension ranges stored in `DescriptorProto`.

The source-language upper bound is inclusive, but descriptor protos store
`end` exclusively. Thus `extensions 1 to max` is represented by
`[1, 536870912)`.
-/
private def validateMessageExtensionRanges
    (context : String) (msg : DescriptorProto) :
    M (Array FieldNumberRange) := do
  let mut ranges : Array FieldNumberRange := #[]
  for range in msg.extension_range do
    let start ← get!! range.start !
      s!"{context}: extension range start is absent"
    let finish ← get!! range.«end» !
      s!"{context}: extension range end is absent"
    let startValue := start.toInt
    let finishValue := finish.toInt
    if startValue ≤ 0 || finishValue ≤ startValue ||
        finishValue > 536870912 then
      throw s!"{context}: invalid extension range [{startValue}, {finishValue})"
    let current : FieldNumberRange :=
      (startValue.toNat, finishValue.toNat)
    for previous in ranges do
      if fieldNumberRangesOverlap current previous then
        throw s!"{context}: extension ranges [{current.1}, {current.2}) and [{previous.1}, {previous.2}) overlap"
    for field in msg.field do
      let number ← get!! field.number
      let value := number.toInt
      if startValue ≤ value && value < finishValue then
        let fieldName ← get!! field.name
        throw s!"{context}.{fieldName}: field number {value} is inside extension range [{startValue}, {finishValue})"
    for reserved in msg.reserved_range do
      let reservedStart ← get!! reserved.start !
        s!"{context}: reserved range start is absent"
      let reservedFinish ← get!! reserved.«end» !
        s!"{context}: reserved range end is absent"
      let reservedStartValue := reservedStart.toInt
      let reservedFinishValue := reservedFinish.toInt
      if reservedStartValue ≤ 0 ||
          reservedFinishValue ≤ reservedStartValue ||
          reservedFinishValue > 536870912 then
        throw s!"{context}: invalid reserved field range [{reservedStartValue}, {reservedFinishValue})"
      let reservedRange : FieldNumberRange :=
        (reservedStartValue.toNat, reservedFinishValue.toNat)
      if fieldNumberRangesOverlap current reservedRange then
        throw s!"{context}: extension range [{current.1}, {current.2}) overlaps reserved range [{reservedRange.1}, {reservedRange.2})"
    ranges := ranges.push current
  return ranges

private def isMapEntryDescriptor (msg : DescriptorProto) : Bool :=
  (msg.options >>= (·.map_entry)).getD false

/--
The spelling used by `protoc` for the synthetic message corresponding to a
map field.  This intentionally mirrors `DescriptorBuilder::ToCamelCase`:
underscores are removed and capitalize the following ASCII character.
-/
private def expectedMapEntryName (fieldName : String) : String :=
  let sourceName :=
    /-
    Descriptor validation currently runs after helper-name sanitization.  Map
    entry names, unlike field names, are not sanitized, so recover the only
    possible source spelling before applying protoc's naming rule.
    -/
    (reservedFieldNames.find? fun raw => sanitizeFieldName raw == fieldName).getD fieldName
  let (stem, _) := sourceName.foldl (fun (out, capitalizeNext) c =>
    if c == '_' then
      (out, true)
    else if capitalizeNext then
      (out.push c.toUpper, false)
    else
      (out.push c, false)) ("", true)
  stem ++ "Entry"

private def validateSyntheticMapField
    (context role expectedName : String) (expectedNumber : Int32)
    (field : FieldDescriptorProto) : M FieldDescriptorProto.Type := do
  let name ← get!! field.name ! s!"{context}: map {role} field name is absent"
  if name != expectedName then
    throw s!"{context}: map {role} field must be named `{expectedName}`, got `{name}`"
  let number ← get!! field.number ! s!"{context}.{name}: map field number is absent"
  if number != expectedNumber then
    throw s!"{context}.{name}: map {role} field must have number {expectedNumber}, got {number}"
  let label ← get!! field.label ! s!"{context}.{name}: map field label is absent"
  if label != .LABEL_OPTIONAL then
    throw s!"{context}.{name}: map {role} field must have label LABEL_OPTIONAL"
  if field.extendee.isSome then
    throw s!"{context}.{name}: synthetic map fields cannot set extendee"
  if field.oneof_index.isSome then
    throw s!"{context}.{name}: synthetic map fields cannot belong to a oneof"
  if field.default_value.isSome then
    throw s!"{context}.{name}: synthetic map fields cannot have explicit defaults"
  if field.proto3_optional.getD false then
    throw s!"{context}.{name}: synthetic map fields cannot set proto3_optional"
  get!! field.type ! s!"{context}.{name}: map field type is absent"

private def validateMapKeyType
    (context : String) (field : FieldDescriptorProto)
    (fieldType : FieldDescriptorProto.Type) : M Unit := do
  let legal :=
    match fieldType with
    | .TYPE_BOOL
    | .TYPE_INT32 | .TYPE_INT64
    | .TYPE_SINT32 | .TYPE_SINT64
    | .TYPE_UINT32 | .TYPE_UINT64
    | .TYPE_FIXED32 | .TYPE_FIXED64
    | .TYPE_SFIXED32 | .TYPE_SFIXED64
    | .TYPE_STRING => true
    | _ => false
  if !legal then
    throw s!"{context}.key: illegal map key type {
      FieldDescriptorProto.Type.«protobuf.internal».toInt32 fieldType}"
  if field.type_name.isSome then
    throw s!"{context}.key: scalar map key cannot set type_name"

private def validateMapValueType
    (context : String) (field : FieldDescriptorProto)
    (fieldType : FieldDescriptorProto.Type) : M Unit := do
  match fieldType with
  | .TYPE_MESSAGE | .TYPE_ENUM =>
      let typeName ← get!! field.type_name !
        s!"{context}.value: message or enum map value must set type_name"
      if typeName.isEmpty then
        throw s!"{context}.value: map value type_name is empty"
  | .TYPE_GROUP =>
      throw s!"{context}.value: group is not a legal map value type"
  | .TYPE_DOUBLE | .TYPE_FLOAT
  | .TYPE_INT64 | .TYPE_UINT64 | .TYPE_INT32
  | .TYPE_FIXED64 | .TYPE_FIXED32 | .TYPE_BOOL | .TYPE_STRING
  | .TYPE_BYTES | .TYPE_UINT32
  | .TYPE_SFIXED32 | .TYPE_SFIXED64 | .TYPE_SINT32 | .TYPE_SINT64 =>
      if field.type_name.isSome then
        throw s!"{context}.value: scalar map value cannot set type_name"
  | .«Unknown.Value» value =>
      throw s!"{context}.value: unknown map value type {value}"

private def validateMapEntryDescriptor
    (parentContext : String) (parent entry : DescriptorProto) : M Unit := do
  let entryName ← get!! entry.name ! s!"{parentContext}: map entry name is absent"
  let context := parentContext ++ "." ++ entryName
  if !entry.extension.isEmpty || !entry.extension_range.isEmpty then
    throw s!"{context}: map entry cannot declare extensions or extension ranges"
  if !entry.nested_type.isEmpty || !entry.enum_type.isEmpty then
    throw s!"{context}: map entry cannot declare nested messages or enums"
  if !entry.oneof_decl.isEmpty then
    throw s!"{context}: map entry cannot declare oneofs"
  if entry.field.size != 2 then
    throw s!"{context}: map entry must contain exactly two fields"

  let keyType ← validateSyntheticMapField context "key" "key" 1 entry.field[0]!
  let valueType ← validateSyntheticMapField context "value" "value" 2 entry.field[1]!
  validateMapKeyType context entry.field[0]! keyType
  validateMapValueType context entry.field[1]! valueType
  if valueType == .TYPE_MESSAGE then
    let valueTypeName ← get!! entry.field[1]!.type_name
    if parent.nested_type.any fun nested =>
        isMapEntryDescriptor nested &&
          nested.name.any fun nestedName =>
            valueTypeName == "." ++ parentContext ++ "." ++ nestedName then
      throw s!"{context}.value: map values cannot be another map"

private def validateEnumDescriptor
    (context : String) (requireFirstZero : Bool)
    (e : EnumDescriptorProto) : M Unit := do
  let enumName ← get!! e.name ! s!"{context}: enum name is absent"
  if e.value.isEmpty then
    throw s!"{context}.{enumName}: enum declaration has no values"
  let allowAlias := (e.options >>= (·.allow_alias)).getD false
  let mut names : Array String := #[]
  let mut numbers : Array Int32 := #[]
  for value in e.value do
    let name ← get!! value.name ! s!"{context}.{enumName}: enum value name is absent"
    if names.contains name then
      throw s!"{context}.{enumName}: enum value `{name}` is declared more than once"
    names := names.push name
    let number ← get!! value.number !
      s!"{context}.{enumName}.{name}: enum value number is absent"
    if numbers.contains number && !allowAlias then
      throw s!"{context}.{enumName}: enum numeric value {number} is declared more than once without allow_alias"
    numbers := numbers.push number
  let mut reservedRanges : Array (Int32 × Int32) := #[]
  for range in e.reserved_range do
    let start ← get!! range.start ! s!"{context}.{enumName}: reserved range start is absent"
    let finish ← get!! range.«end» ! s!"{context}.{enumName}: reserved range end is absent"
    -- EnumDescriptorProto ranges are inclusive at both ends, unlike message
    -- reserved ranges whose end is exclusive.
    if finish < start then
      throw s!"{context}.{enumName}: invalid reserved enum range [{start}, {finish}]"
    let current := (start, finish)
    for previous in reservedRanges do
      if current.1 ≤ previous.2 && previous.1 ≤ current.2 then
        throw s!"{context}.{enumName}: reserved enum ranges [{current.1}, {current.2}] and [{previous.1}, {previous.2}] overlap"
    for value in e.value do
      let number ← get!! value.number
      if start ≤ number && number ≤ finish then
        let valueName ← get!! value.name
        throw s!"{context}.{enumName}.{valueName}: enum numeric value {number} is reserved"
    reservedRanges := reservedRanges.push current
  let mut reservedNames : Array String := #[]
  for reservedName in e.reserved_name do
    if reservedNames.contains reservedName then
      throw s!"{context}.{enumName}: enum value name `{reservedName}` is reserved more than once"
    reservedNames := reservedNames.push reservedName
    let leanName := sanitizeEnumValueName reservedName
    if e.value.any (fun value =>
        value.name == some reservedName || value.name == some leanName) then
      throw s!"{context}.{enumName}: enum value name `{reservedName}` is reserved"
  if requireFirstZero then
    let first ← get!! e.value[0]!.number !
      s!"{context}.{enumName}: first enum value number is absent"
    if first != 0 then
      throw s!"{context}.{enumName}: the first value of an open enum must be zero"

private def validateMessageOneofs
    (context : String) (msg : DescriptorProto) : M Unit := do
  let mut oneofNames : Array String := #[]
  for oneofDecl in msg.oneof_decl do
    let oneofName ← get!! oneofDecl.name !
      s!"{context}: oneof name is absent"
    if oneofName.isEmpty then
      throw s!"{context}: oneof name is empty"
    if oneofNames.contains oneofName then
      throw s!"{context}: oneof name `{oneofName}` is declared more than once"
    if msg.field.any fun field => field.name == some oneofName then
      throw s!"{context}: oneof name `{oneofName}` conflicts with a field name"
    oneofNames := oneofNames.push oneofName

  let mut memberCounts : Array Nat :=
    Array.replicate msg.oneof_decl.size 0
  let mut syntheticOneofs : Array Bool :=
    Array.replicate msg.oneof_decl.size false
  for field in msg.field do
    if let some index := field.oneof_index then
      let value := index.toInt
      let fieldName := field.name.getD "<unnamed>"
      if value < 0 || value.toNat ≥ msg.oneof_decl.size then
        throw s!"{context}.{fieldName}: oneof_index {value} is out of bounds"
      let indexNat := value.toNat
      memberCounts :=
        memberCounts.set! indexNat (memberCounts[indexNat]! + 1)
      if field.proto3_optional.getD false then
        syntheticOneofs := syntheticOneofs.set! indexNat true

  let mut sawSynthetic := false
  for index in [:msg.oneof_decl.size] do
    let oneofName ← get!! msg.oneof_decl[index]!.name !
      s!"{context}: oneof name is absent"
    if memberCounts[index]! == 0 then
      throw s!"{context}: oneof `{oneofName}` has no fields"
    if syntheticOneofs[index]! then
      sawSynthetic := true
    else if sawSynthetic then
      throw s!"{context}: real oneof `{oneofName}` appears after a synthetic oneof; synthetic oneofs must be ordered after all real oneofs"

private partial def validateMessageDescriptor
    (prefixName : String) (requireFirstEnumZero : Bool)
    (msg : DescriptorProto) : M Unit := do
  let name ← get!! msg.name ! s!"{prefixName}: message name is absent"
  let context := if prefixName.isEmpty then name else prefixName ++ "." ++ name
  validateDescriptorFields context msg.field
  validateMessageOneofs context msg
  let mut reservedRanges : Array FieldNumberRange := #[]
  for range in msg.reserved_range do
    let start ← get!! range.start ! s!"{context}: reserved range start is absent"
    let finish ← get!! range.«end» ! s!"{context}: reserved range end is absent"
    if start ≤ 0 || finish ≤ start || finish > 536870912 then
      throw s!"{context}: invalid reserved field range [{start}, {finish})"
    let current : FieldNumberRange :=
      (start.toInt.toNat, finish.toInt.toNat)
    for previous in reservedRanges do
      if fieldNumberRangesOverlap current previous then
        throw s!"{context}: reserved field ranges [{current.1}, {current.2}) and [{previous.1}, {previous.2}) overlap"
    for field in msg.field do
      let number ← get!! field.number
      if start ≤ number && number < finish then
        let fieldName ← get!! field.name
        throw s!"{context}.{fieldName}: field number {number} is reserved"
    reservedRanges := reservedRanges.push current
  let mut reservedNames : Array String := #[]
  for reservedName in msg.reserved_name do
    if reservedNames.contains reservedName then
      throw s!"{context}: field name `{reservedName}` is reserved more than once"
    reservedNames := reservedNames.push reservedName
    let leanName := sanitizeFieldName reservedName
    if msg.field.any (fun field =>
        field.name == some reservedName || field.name == some leanName) then
      throw s!"{context}: field name `{reservedName}` is reserved"
  discard <| validateMessageExtensionRanges context msg
  let mut typeNames : Array String := #[]
  for nested in msg.nested_type do
    let nestedName ← get!! nested.name ! s!"{context}: nested message name is absent"
    if typeNames.contains nestedName then
      throw s!"{context}: nested type name `{nestedName}` is declared more than once"
    typeNames := typeNames.push nestedName
  for e in msg.enum_type do
    let enumName ← get!! e.name ! s!"{context}: nested enum name is absent"
    if typeNames.contains enumName then
      throw s!"{context}: nested type name `{enumName}` is declared more than once"
    typeNames := typeNames.push enumName
  for nested in msg.nested_type do
    if isMapEntryDescriptor nested then
      validateMapEntryDescriptor context msg nested
  for nested in msg.nested_type do
    validateMessageDescriptor context requireFirstEnumZero nested
  for e in msg.enum_type do
    validateEnumDescriptor context requireFirstEnumZero e
  validateDescriptorFields s!"{context} extension" msg.extension
    (requireUniqueNumbers := false)

/--
Validate wire-level descriptor invariants before translating a descriptor into
Lean syntax.  This is also the trust boundary used by the standalone protoc
plugin: hand-crafted `CodeGeneratorRequest` values receive a generation error
instead of an invalid Lean file or a runtime-only failure.
-/
def validateFileDescriptor
    (file : FileDescriptorProto) (requireFirstEnumZero : Bool := false) : M Unit := do
  let fileName ← get!! file.name ! "file descriptor name is absent"
  let mut typeNames : Array String := #[]
  for msg in file.message_type do
    let name ← get!! msg.name ! s!"{fileName}: top-level message name is absent"
    if isMapEntryDescriptor msg then
      throw s!"{fileName}.{name}: map_entry messages must be nested in their containing message"
    if typeNames.contains name then
      throw s!"{fileName}: top-level type name `{name}` is declared more than once"
    typeNames := typeNames.push name
  for e in file.enum_type do
    let name ← get!! e.name ! s!"{fileName}: top-level enum name is absent"
    if typeNames.contains name then
      throw s!"{fileName}: top-level type name `{name}` is declared more than once"
    typeNames := typeNames.push name
  for msg in file.message_type do
    validateMessageDescriptor (file.package.getD "") requireFirstEnumZero msg
  for e in file.enum_type do
    validateEnumDescriptor (file.package.getD "") requireFirstEnumZero e
  validateDescriptorFields s!"{fileName} extension" file.extension
    (requireUniqueNumbers := false)

private structure DescriptorDependencyInfo where
  direct : Array String
  optionOnly : Array String
  publicFiles : Array String

private abbrev DescriptorDependencyRegistry :=
  Std.HashMap String DescriptorDependencyInfo

private partial def validateDescriptorDependencyAcyclicFrom
    (registry : DescriptorDependencyRegistry) (fileName : String)
    (active completed : Std.HashMap String PUnit) :
    M (Std.HashMap String PUnit) := do
  if completed.contains fileName then
    return completed
  if active.contains fileName then
    throw s!"file import cycle contains `{fileName}`"
  let active := active.insert fileName ()
  let mut completed := completed
  if let some info := registry[fileName]? then
    for dependency in info.direct ++ info.optionOnly do
      completed ←
        validateDescriptorDependencyAcyclicFrom
          registry dependency active completed
  return completed.insert fileName ()

private def validateDescriptorDependencies
    (desc : FileDescriptorSet) : M DescriptorDependencyRegistry := do
  let mut fileNames : Std.HashMap String PUnit := {}
  for file in desc.file do
    let fileName ← get!! file.name ! "file descriptor name is absent"
    if fileNames.contains fileName then
      throw s!"file descriptor name `{fileName}` is declared more than once"
    fileNames := fileNames.insert fileName ()

  let mut registry : DescriptorDependencyRegistry := {}
  for file in desc.file do
    let fileName ← get!! file.name ! "file descriptor name is absent"
    let mut seen : Std.HashMap String PUnit := {}
    for dependency in file.dependency do
      if seen.contains dependency then
        throw s!"{fileName}: dependency `{dependency}` is listed more than once"
      if dependency == fileName then
        throw s!"{fileName}: file recursively imports itself"
      unless fileNames.contains dependency do
        throw s!"{fileName}: dependency `{dependency}` is absent from the descriptor set"
      seen := seen.insert dependency ()

    if !file.option_dependency.isEmpty then
      let supportsOptionImports :=
        file.«syntax» == some "editions" &&
          file.edition.any fun edition =>
            Edition.«protobuf.internal».toInt32 edition ≥
              Edition.«protobuf.internal».toInt32 Edition.EDITION_2024
      unless supportsOptionImports do
        throw s!"{fileName}: option imports are not supported before Edition 2024"
    for dependency in file.option_dependency do
      if seen.contains dependency then
        throw s!"{fileName}: dependency `{dependency}` is listed more than once across dependency and option_dependency"
      if dependency == fileName then
        throw s!"{fileName}: file recursively imports itself"
      unless fileNames.contains dependency do
        throw s!"{fileName}: option dependency `{dependency}` is absent from the descriptor set"
      seen := seen.insert dependency ()

    let dependencyAt
        (kind : String) (index : Int32) : M String := do
      let value := index.toInt
      if value < 0 || value.toNat ≥ file.dependency.size then
        throw s!"{fileName}: invalid {kind} dependency index {value}"
      return file.dependency[value.toNat]!
    let publicDependencies ← file.public_dependency.mapM
      (dependencyAt "public")
    if file.«syntax» == some "editions" &&
        file.edition == some .EDITION_2024 &&
        !file.weak_dependency.isEmpty then
      throw s!"{fileName}: weak imports are not supported in Edition 2024"
    for index in file.weak_dependency do
      discard <| dependencyAt "weak" index
    registry := registry.insert fileName {
      direct := file.dependency
      optionOnly := file.option_dependency
      publicFiles := publicDependencies
    }
  let mut completed : Std.HashMap String PUnit := {}
  for file in desc.file do
    let fileName ← get!! file.name ! "file descriptor name is absent"
    completed ←
      validateDescriptorDependencyAcyclicFrom registry fileName {} completed
  return registry

private partial def includePublicDependencyClosure
    (registry : DescriptorDependencyRegistry) (fileName : String)
    (initial : Std.HashMap String PUnit) : Std.HashMap String PUnit :=
  match registry[fileName]? with
  | none => initial
  | some info =>
      Id.run do
        let mut visible := initial
        for dependency in info.publicFiles do
          unless visible.contains dependency do
            visible := visible.insert dependency ()
            visible :=
              includePublicDependencyClosure registry dependency visible
        return visible

private def visibleDescriptorFiles
    (registry : DescriptorDependencyRegistry) (fileName : String) :
    Std.HashMap String PUnit :=
  Id.run do
    let mut visible : Std.HashMap String PUnit := {}
    visible := visible.insert fileName ()
    if let some info := registry[fileName]? then
      for dependency in info.direct do
        visible := visible.insert dependency ()
        visible :=
          includePublicDependencyClosure registry dependency visible
    return visible

private def validateDescriptorTargetVisibility
    (dependencies : DescriptorDependencyRegistry)
    (sourceFile targetFile : String) (targetExported : Bool)
    (context : String) : M Unit := do
  if sourceFile == targetFile then
    return
  unless (visibleDescriptorFiles dependencies sourceFile).contains targetFile do
    throw s!"{context}: target is defined in `{targetFile}`, which is not imported by `{sourceFile}`"
  unless targetExported do
    throw s!"{context}: target is local to `{targetFile}` and cannot be imported by `{sourceFile}`"

private def qualifyProtoSymbol (scope name : String) : String :=
  if scope.isEmpty then name else scope ++ "." ++ name

private def featureTargetDescription :
    FieldOptions.OptionTargetType → String
  | .TARGET_TYPE_FILE => "file"
  | .TARGET_TYPE_EXTENSION_RANGE => "extension range"
  | .TARGET_TYPE_MESSAGE => "message"
  | .TARGET_TYPE_FIELD => "field"
  | .TARGET_TYPE_ONEOF => "oneof"
  | .TARGET_TYPE_ENUM => "enum"
  | .TARGET_TYPE_ENUM_ENTRY => "enum entry"
  | .TARGET_TYPE_SERVICE => "service"
  | .TARGET_TYPE_METHOD => "method"
  | .TARGET_TYPE_UNKNOWN => "unknown target"
  | .«Unknown.Value» number => s!"unknown target {number}"

private def featureEditionDescription : Edition → String
  | .EDITION_2023 => "2023"
  | .EDITION_2024 => "2024"
  | .EDITION_2026 => "2026"
  | edition => toString (Edition.«protobuf.internal».toInt32 edition)

/--
Validate only the built-in fields of `FeatureSet`.

Custom FeatureSet extensions are preserved in `Unknown.Fields` by the
bootstrap descriptor representation.  Empty sets and sets containing only
such extensions deliberately pass through this validator.
-/
private def validateBuiltinFeatureSet
    (file : FileDescriptorProto)
    (target : FieldOptions.OptionTargetType) (context : String)
    (features? : Option FeatureSet) : M Unit := do
  let some features := features? | return
  let validate
      (present : Bool) (featureName : String)
      (introduced : Edition) (allowed : Bool)
      (allowedTargets : String) : M Unit := do
    unless present do return
    unless file.«syntax» == some "editions" do
      throw s!"{context}: built-in feature `{featureName}` is only valid under editions syntax"
    let edition ← file.edition.getDM
      (throw s!"{context}: built-in feature `{featureName}` requires file.edition")
    if Edition.«protobuf.internal».toInt32 edition <
        Edition.«protobuf.internal».toInt32 introduced then
      throw s!"{context}: {featureName} is not supported before Edition {featureEditionDescription introduced}"
    unless allowed do
      throw s!"{context}: {featureName} can only be set on {allowedTargets}, not {featureTargetDescription target}"
  let validateKnownValue
      (known : Bool) (featureName : String) : M Unit := do
    unless known do
      throw s!"{context}: built-in feature `{featureName}` must have a known nonzero value"

  validate features.field_presence.isSome "field_presence"
    .EDITION_2023
    (target == .TARGET_TYPE_FILE || target == .TARGET_TYPE_FIELD)
    "files or message fields"
  validateKnownValue
    (match features.field_presence with
      | some .FIELD_PRESENCE_UNKNOWN
      | some (.«Unknown.Value» _) => false
      | _ => true)
    "field_presence"
  validate features.enum_type.isSome "enum_type"
    .EDITION_2023
    (target == .TARGET_TYPE_FILE || target == .TARGET_TYPE_ENUM)
    "files or enums"
  validateKnownValue
    (match features.enum_type with
      | some .ENUM_TYPE_UNKNOWN
      | some (.«Unknown.Value» _) => false
      | _ => true)
    "enum_type"
  validate features.repeated_field_encoding.isSome
    "repeated_field_encoding" .EDITION_2023
    (target == .TARGET_TYPE_FILE || target == .TARGET_TYPE_FIELD)
    "files or message fields"
  validateKnownValue
    (match features.repeated_field_encoding with
      | some .REPEATED_FIELD_ENCODING_UNKNOWN
      | some (.«Unknown.Value» _) => false
      | _ => true)
    "repeated_field_encoding"
  validate features.utf8_validation.isSome "utf8_validation"
    .EDITION_2023
    (target == .TARGET_TYPE_FILE || target == .TARGET_TYPE_FIELD)
    "files or message fields"
  validateKnownValue
    (match features.utf8_validation with
      | some .UTF8_VALIDATION_UNKNOWN
      | some (.«Unknown.Value» _) => false
      | _ => true)
    "utf8_validation"
  validate features.message_encoding.isSome "message_encoding"
    .EDITION_2023
    (target == .TARGET_TYPE_FILE || target == .TARGET_TYPE_FIELD)
    "files or message fields"
  validateKnownValue
    (match features.message_encoding with
      | some .MESSAGE_ENCODING_UNKNOWN
      | some (.«Unknown.Value» _) => false
      | _ => true)
    "message_encoding"
  validate features.json_format.isSome "json_format"
    .EDITION_2023
    (target == .TARGET_TYPE_FILE || target == .TARGET_TYPE_MESSAGE ||
      target == .TARGET_TYPE_ENUM)
    "files, messages, or enums"
  validateKnownValue
    (match features.json_format with
      | some .JSON_FORMAT_UNKNOWN
      | some (.«Unknown.Value» _) => false
      | _ => true)
    "json_format"
  validate features.enforce_naming_style.isSome "enforce_naming_style"
    .EDITION_2024
    (target == .TARGET_TYPE_FILE ||
      target == .TARGET_TYPE_EXTENSION_RANGE ||
      target == .TARGET_TYPE_MESSAGE || target == .TARGET_TYPE_FIELD ||
      target == .TARGET_TYPE_ONEOF || target == .TARGET_TYPE_ENUM ||
      target == .TARGET_TYPE_ENUM_ENTRY ||
      target == .TARGET_TYPE_SERVICE || target == .TARGET_TYPE_METHOD)
    "files, extension ranges, messages, fields, oneofs, enums, enum entries, services, or methods"
  validateKnownValue
    (match features.enforce_naming_style with
      | some .ENFORCE_NAMING_STYLE_UNKNOWN
      | some (.«Unknown.Value» _) => false
      | _ => true)
    "enforce_naming_style"
  validate features.default_symbol_visibility.isSome
    "default_symbol_visibility" .EDITION_2024
    (target == .TARGET_TYPE_FILE) "files"
  validateKnownValue
    (match features.default_symbol_visibility with
      | some .DEFAULT_SYMBOL_VISIBILITY_UNKNOWN
      | some (.«Unknown.Value» _) => false
      | _ => true)
    "default_symbol_visibility"
  validate features.enforce_proto_limits.isSome "enforce_proto_limits"
    .EDITION_2026
    (target == .TARGET_TYPE_MESSAGE || target == .TARGET_TYPE_FIELD ||
      target == .TARGET_TYPE_ONEOF || target == .TARGET_TYPE_ENUM)
    "messages, fields, oneofs, or enums"
  validateKnownValue
    (match features.enforce_proto_limits with
      | some .PROTO_LIMITS_UNKNOWN
      | some (.«Unknown.Value» _) => false
      | _ => true)
    "enforce_proto_limits"

/--
Validate features written directly on an extension declaration.

Although extensions use `FieldOptions`, their presence is always explicit and
cannot be overridden at the field. File- or lexical-scope presence defaults
remain valid; callers pass only the extension field's own options here.
-/
private def validateExtensionBuiltinFeatures
    (file : FileDescriptorProto) (context : String)
    (features? : Option FeatureSet) : M Unit := do
  validateBuiltinFeatureSet file .TARGET_TYPE_FIELD context features?
  if let some presence := features? >>= (·.field_presence) then
    if presence == .LEGACY_REQUIRED then
      throw s!"{context}: extension fields cannot be required"
    else
      throw s!"{context}: extension fields cannot specify field_presence"

private def validateEnumBuiltinFeatures
    (file : FileDescriptorProto) (prefixName : String)
    (e : EnumDescriptorProto) : M Unit := do
  let enumName := e.name.getD "<unnamed>"
  let fullName := qualifyProtoSymbol prefixName enumName
  validateBuiltinFeatureSet file .TARGET_TYPE_ENUM
    s!"enum `{fullName}`" (e.options >>= (·.features))
  for value in e.value do
    let valueName := value.name.getD "<unnamed>"
    validateBuiltinFeatureSet file .TARGET_TYPE_ENUM_ENTRY
      s!"enum value `{fullName}.{valueName}`"
      (value.options >>= (·.features))

private partial def validateMessageBuiltinFeatures
    (file : FileDescriptorProto) (prefixName : String)
    (msg : DescriptorProto) : M Unit := do
  let messageName := msg.name.getD "<unnamed>"
  let fullName := qualifyProtoSymbol prefixName messageName
  validateBuiltinFeatureSet file .TARGET_TYPE_MESSAGE
    s!"message `{fullName}`" (msg.options >>= (·.features))
  for field in msg.field do
    let fieldName := field.name.getD "<unnamed>"
    validateBuiltinFeatureSet file .TARGET_TYPE_FIELD
      s!"field `{fullName}.{fieldName}`"
      (field.options >>= (·.features))
  for field in msg.extension do
    let fieldName := field.name.getD "<unnamed>"
    validateExtensionBuiltinFeatures file
      s!"extension field `{fullName}.{fieldName}`"
      (field.options >>= (·.features))
  for range in msg.extension_range do
    validateBuiltinFeatureSet file .TARGET_TYPE_EXTENSION_RANGE
      s!"extension range in message `{fullName}`"
      (range.options >>= (·.features))
  for oneofDecl in msg.oneof_decl do
    let oneofName := oneofDecl.name.getD "<unnamed>"
    validateBuiltinFeatureSet file .TARGET_TYPE_ONEOF
      s!"oneof `{fullName}.{oneofName}`"
      (oneofDecl.options >>= (·.features))
  for e in msg.enum_type do
    validateEnumBuiltinFeatures file fullName e
  for nested in msg.nested_type do
    validateMessageBuiltinFeatures file fullName nested

private def validateFileBuiltinFeatures
    (file : FileDescriptorProto) : M Unit := do
  let fileName := file.name.getD "<unnamed>"
  let packageName := file.package.getD ""
  validateBuiltinFeatureSet file .TARGET_TYPE_FILE
    s!"file `{fileName}`" (file.options >>= (·.features))
  for field in file.extension do
    let fieldName := field.name.getD "<unnamed>"
    validateExtensionBuiltinFeatures file
      s!"file extension `{qualifyProtoSymbol packageName fieldName}`"
      (field.options >>= (·.features))
  for e in file.enum_type do
    validateEnumBuiltinFeatures file packageName e
  for msg in file.message_type do
    validateMessageBuiltinFeatures file packageName msg
  for service in file.service do
    let serviceName := service.name.getD "<unnamed>"
    let serviceFullName := qualifyProtoSymbol packageName serviceName
    validateBuiltinFeatureSet file .TARGET_TYPE_SERVICE
      s!"service `{serviceFullName}`"
      (service.options >>= (·.features))
    for method in service.method do
      let methodName := method.name.getD "<unnamed>"
      validateBuiltinFeatureSet file .TARGET_TYPE_METHOD
        s!"method `{serviceFullName}.{methodName}`"
        (method.options >>= (·.features))

private def descriptorSupportsEdition2024Features
    (file : FileDescriptorProto) : Bool :=
  file.«syntax» == some "editions" &&
    file.edition.any fun edition =>
      Edition.«protobuf.internal».toInt32 edition ≥
        Edition.«protobuf.internal».toInt32 Edition.EDITION_2024

private partial def validateMessageSymbolVisibilityFeatureSupport
    (fileName prefixName : String) (messages : Array DescriptorProto) :
    M Unit := do
  for msg in messages do
    let name := msg.name.getD "<unnamed>"
    let fullName := qualifyProtoSymbol prefixName name
    if msg.visibility.isSome then
      throw s!"{fileName}: explicit symbol visibility on message `{fullName}` is not supported before Edition 2024"
    for e in msg.enum_type do
      let enumName := e.name.getD "<unnamed>"
      if e.visibility.isSome then
        throw s!"{fileName}: explicit symbol visibility on enum `{qualifyProtoSymbol fullName enumName}` is not supported before Edition 2024"
    validateMessageSymbolVisibilityFeatureSupport
      fileName fullName msg.nested_type

private def validateSymbolVisibilityFeatureSupport
    (file : FileDescriptorProto) : M Unit := do
  if descriptorSupportsEdition2024Features file then
    return
  let fileName := file.name.getD "<unnamed>"
  for e in file.enum_type do
    let enumName := e.name.getD "<unnamed>"
    if e.visibility.isSome then
      throw s!"{fileName}: explicit symbol visibility on enum `{qualifyProtoSymbol (file.package.getD "") enumName}` is not supported before Edition 2024"
  validateMessageSymbolVisibilityFeatureSupport
    fileName (file.package.getD "") file.message_type

private def descriptorDefaultSymbolVisibility
    (file : FileDescriptorProto) :
    M FeatureSet.VisibilityFeature.DefaultSymbolVisibility := do
  if let some value :=
      file.options >>= (·.features) >>= (·.default_symbol_visibility) then
    match value with
    | .«Unknown.Value» number =>
        throw s!"{file.name.getD "<unnamed>"}: unknown default_symbol_visibility {number}"
    | .DEFAULT_SYMBOL_VISIBILITY_UNKNOWN =>
        throw s!"{file.name.getD "<unnamed>"}: default_symbol_visibility is unknown"
    | value => return value
  if file.edition == some .EDITION_2024 then
    return .EXPORT_TOP_LEVEL
  return .EXPORT_ALL

private def descriptorSymbolIsExported
    (defaultVisibility : FeatureSet.VisibilityFeature.DefaultSymbolVisibility)
    (topLevel : Bool) (visibility : Option SymbolVisibility)
    (allowStrictNestedExport : Bool)
    (context : String) : M Bool := do
  match visibility.getD .VISIBILITY_UNSET with
  | .«Unknown.Value» number =>
      throw s!"{context}: unknown symbol visibility {number}"
  | .VISIBILITY_LOCAL => return false
  | .VISIBILITY_EXPORT =>
      if defaultVisibility == .STRICT && !topLevel &&
          !allowStrictNestedExport then
        throw s!"{context}: nested symbols cannot be explicitly exported when default_symbol_visibility is STRICT"
      return true
  | .VISIBILITY_UNSET =>
      match defaultVisibility with
      | .EXPORT_ALL => return true
      | .EXPORT_TOP_LEVEL => return topLevel
      | .LOCAL_ALL | .STRICT => return false
      | .DEFAULT_SYMBOL_VISIBILITY_UNKNOWN =>
          throw s!"{context}: default_symbol_visibility is unknown"
      | .«Unknown.Value» number =>
          throw s!"{context}: unknown default_symbol_visibility {number}"

private structure ExtensionTargetInfo where
  context : String
  fileName : String
  exported : Bool
  ranges : Array FieldNumberRange
  isMapEntry : Bool
deriving Inhabited

private structure EnumTargetInfo where
  context : String
  fileName : String
  exported : Bool
  firstNumber : Option Int32
  values : Array String
deriving Inhabited

private structure MapValueDefinition where
  context : String
  fileName : String
  field : FieldDescriptorProto

private structure DescriptorSetRegistry where
  messages : Std.HashMap String ExtensionTargetInfo := {}
  enums : Std.HashMap String EnumTargetInfo := {}
  /--
  Protobuf's relative lookup resolves the first component of a compound name
  before resolving the remainder.  Messages, enums, packages, and services are
  aggregates for that purpose.
  -/
  aggregates : Std.HashMap String PUnit := {}
  mapValues : Array MapValueDefinition := #[]

private def isEnumNamespaceMessage
    (defaultVisibility :
      FeatureSet.VisibilityFeature.DefaultSymbolVisibility)
    (topLevel : Bool) (msg : DescriptorProto) : Bool :=
  if !topLevel then
    false
  else
    let defaultToLocal :=
      defaultVisibility == .STRICT || defaultVisibility == .LOCAL_ALL
    let containerLocal :=
      msg.visibility == some .VISIBILITY_LOCAL ||
        (msg.visibility.getD .VISIBILITY_UNSET == .VISIBILITY_UNSET &&
          defaultToLocal)
    containerLocal && msg.reserved_range.size == 1 &&
      msg.reserved_range[0]!.start == some 1 &&
      msg.reserved_range[0]!.«end» == some 536870912

private def registerEnumTargets
    (fileName prefixName : String)
    (defaultVisibility :
      FeatureSet.VisibilityFeature.DefaultSymbolVisibility)
    (topLevel allowStrictNestedExport : Bool)
    (enums : Array EnumDescriptorProto)
    (initial : DescriptorSetRegistry) : M DescriptorSetRegistry := do
  let mut registry := initial
  for e in enums do
    let name ← get!! e.name !
      s!"{prefixName}: enum name is absent"
    let fullName :=
      if prefixName.isEmpty then name else prefixName ++ "." ++ name
    if registry.messages.contains fullName || registry.enums.contains fullName then
      throw s!"protobuf type `{fullName}` is declared more than once in the descriptor set"
    let firstNumber := e.value[0]? >>= fun value => value.number
    let values ← e.value.mapM fun value =>
      get!! value.name ! s!"{fullName}: enum value name is absent"
    let exported ← descriptorSymbolIsExported
      defaultVisibility topLevel e.visibility allowStrictNestedExport
      s!"enum `{fullName}`"
    registry := {
      registry with
      enums := registry.enums.insert fullName {
        context := fullName
        fileName
        exported
        firstNumber
        values
      }
      aggregates := registry.aggregates.insert fullName ()
    }
  return registry

private partial def registerMessageExtensionTargets
    (fileName prefixName : String)
    (defaultVisibility :
      FeatureSet.VisibilityFeature.DefaultSymbolVisibility)
    (topLevel : Bool) (messages : Array DescriptorProto)
    (initial : DescriptorSetRegistry) : M DescriptorSetRegistry := do
  let mut registry := initial
  for msg in messages do
    let name ← get!! msg.name !
      s!"{prefixName}: message name is absent"
    let fullName :=
      if prefixName.isEmpty then name else prefixName ++ "." ++ name
    if registry.messages.contains fullName || registry.enums.contains fullName then
      throw s!"protobuf type `{fullName}` is declared more than once in the descriptor set"
    let ranges ← validateMessageExtensionRanges fullName msg
    let mapEntry := isMapEntryDescriptor msg
    let exported ← descriptorSymbolIsExported
      defaultVisibility topLevel msg.visibility false
      s!"message `{fullName}`"
    registry := {
      registry with
      messages := registry.messages.insert fullName {
        context := fullName
        fileName
        exported
        ranges
        isMapEntry := mapEntry
      }
      aggregates := registry.aggregates.insert fullName ()
    }
    let allowStrictNestedEnumExport :=
      isEnumNamespaceMessage defaultVisibility topLevel msg
    registry ← registerEnumTargets
      fileName fullName defaultVisibility false
      allowStrictNestedEnumExport msg.enum_type registry
    if mapEntry then
      if let some valueField := msg.field[1]? then
        registry := {
          registry with
          mapValues := registry.mapValues.push {
            context := fullName
            fileName
            field := valueField
          }
        }
    registry ←
      registerMessageExtensionTargets
        fileName fullName defaultVisibility false msg.nested_type registry
  return registry

private structure ExtensionDefinition where
  fileName : String
  scope : String
  context : String
  field : FieldDescriptorProto

private partial def collectMessageExtensionDefinitions
    (fileName prefixName : String) (messages : Array DescriptorProto) :
    M (Array ExtensionDefinition) := do
  let mut definitions := #[]
  for msg in messages do
    let name ← get!! msg.name !
      s!"{prefixName}: message name is absent"
    let fullName :=
      if prefixName.isEmpty then name else prefixName ++ "." ++ name
    for field in msg.extension do
      definitions := definitions.push {
        fileName
        scope := fullName
        context := s!"{fullName} extension"
        field
      }
    definitions :=
      definitions ++
        (← collectMessageExtensionDefinitions
          fileName fullName msg.nested_type)
  return definitions

def protobufTypeNameCandidates (scope raw : String) : Array String :=
  if raw.startsWith "." then
    #[(raw.drop 1).toString]
  else
    Id.run do
      let rawParts := raw.splitOn "."
      let mut scopeParts :=
        if scope.isEmpty then [] else scope.splitOn "."
      let mut candidates := #[]
      repeat
        candidates :=
          candidates.push (String.intercalate "." (scopeParts ++ rawParts))
        if scopeParts.isEmpty then
          break
        scopeParts := scopeParts.take (scopeParts.length - 1)
      return candidates

def protobufTypeNameResolvesTo
    (scope raw target : String) : Bool :=
  let target :=
    if target.startsWith "." then (target.drop 1).toString else target
  (protobufTypeNameCandidates scope raw).contains target

private inductive RegisteredTypeTarget where
  | message (info : ExtensionTargetInfo)
  | «enum» (info : EnumTargetInfo)

private def registeredTypeAt?
    (registry : DescriptorSetRegistry) (fullName : String) :
    Option RegisteredTypeTarget :=
  match registry.messages[fullName]? with
  | some info => some (.message info)
  | none => registry.enums[fullName]?.map RegisteredTypeTarget.enum

private def resolveRegisteredType?
    (registry : DescriptorSetRegistry) (scope raw : String) :
    Option RegisteredTypeTarget := Id.run do
  if raw.startsWith "." then
    return registeredTypeAt? registry (raw.drop 1).toString

  let rawParts := raw.splitOn "."
  let firstPart := rawParts.head?.getD raw
  let compound := rawParts.length > 1
  let mut scopeParts :=
    if scope.isEmpty then [] else scope.splitOn "."
  repeat
    let firstFullName :=
      String.intercalate "." (scopeParts ++ [firstPart])
    if compound && registry.aggregates.contains firstFullName then
      /-
      Match DescriptorBuilder::LookupSymbolNoPlaceholder: once the innermost
      aggregate matching the first component is found, the remainder must
      resolve inside it.  Failure is final; an outer aggregate must not be
      selected instead.
      -/
      let fullName := String.intercalate "." (scopeParts ++ rawParts)
      return registeredTypeAt? registry fullName
    if !compound then
      if let some target := registeredTypeAt? registry firstFullName then
        return some target
    if scopeParts.isEmpty then
      break
    scopeParts := scopeParts.take (scopeParts.length - 1)
  return none

private def resolveExtensionTarget
    (dependencies : DescriptorDependencyRegistry)
    (registry : DescriptorSetRegistry)
    (sourceFile scope raw : String) : M String := do
  match resolveRegisteredType? registry scope raw with
  | some (.message target) =>
      validateDescriptorTargetVisibility dependencies
        sourceFile target.fileName target.exported
        s!"extension extendee `{raw}`"
      return target.context
  | some (.enum _) | none =>
      throw s!"extension extendee `{raw}` does not name a message in the descriptor set"

/--
Resolve by protobuf lexical scope before checking import visibility.  A symbol
found in the nearest scope shadows outer symbols even when it is local or its
file was not imported; the subsequent visibility check must diagnose that
reference rather than silently selecting a different type.
-/
private def resolveRegisteredTypeForFile?
    (dependencies : DescriptorDependencyRegistry)
    (registry : DescriptorSetRegistry) (sourceFile scope raw : String) :
    Option RegisteredTypeTarget :=
  let _ := dependencies
  let _ := sourceFile
  resolveRegisteredType? registry scope raw

private structure FieldTypeDefinition where
  fileName : String
  scope : String
  context : String
  field : FieldDescriptorProto

private partial def collectMessageFieldTypeDefinitions
    (fileName prefixName : String) (messages : Array DescriptorProto) :
    M (Array FieldTypeDefinition) := do
  let mut definitions := #[]
  for msg in messages do
    let name ← get!! msg.name !
      s!"{prefixName}: message name is absent"
    let fullName :=
      if prefixName.isEmpty then name else prefixName ++ "." ++ name
    for field in msg.field do
      definitions := definitions.push {
        fileName
        scope := fullName
        context := fullName
        field
      }
    for field in msg.extension do
      definitions := definitions.push {
        fileName
        scope := fullName
        context := s!"{fullName} extension"
        field
      }
    definitions :=
      definitions ++
        (← collectMessageFieldTypeDefinitions
          fileName fullName msg.nested_type)
  return definitions

private def requiredTypeName
    (definition : FieldTypeDefinition) (fieldName : String) : M String := do
  let rawType ← get!! definition.field.type_name !
    s!"{definition.context}.{fieldName}: field type requires type_name"
  if rawType.isEmpty then
    throw s!"{definition.context}.{fieldName}: field type_name is empty"
  return rawType

private def validateRegisteredFieldTypeTarget
    (dependencies : DescriptorDependencyRegistry)
    (registry : DescriptorSetRegistry) (definition : FieldTypeDefinition) :
    M Unit := do
  let fieldName ← get!! definition.field.name !
    s!"{definition.context}: field name is absent"
  let fieldType ← get!! definition.field.type !
    s!"{definition.context}.{fieldName}: field type is absent"
  match fieldType with
  | .TYPE_MESSAGE | .TYPE_GROUP =>
      let rawType ← requiredTypeName definition fieldName
      match resolveRegisteredTypeForFile? dependencies registry
          definition.fileName definition.scope rawType with
      | some (.message info) =>
          validateDescriptorTargetVisibility dependencies
            definition.fileName info.fileName info.exported
            s!"{definition.context}.{fieldName}"
      | some (.enum info) =>
          throw s!"{definition.context}.{fieldName}: message field type_name `{rawType}` names enum `{info.context}`"
      | none =>
          throw s!"{definition.context}.{fieldName}: message field type_name `{rawType}` cannot be resolved in the descriptor set"
  | .TYPE_ENUM =>
      let rawType ← requiredTypeName definition fieldName
      match resolveRegisteredTypeForFile? dependencies registry
          definition.fileName definition.scope rawType with
      | some (.enum info) =>
          validateDescriptorTargetVisibility dependencies
            definition.fileName info.fileName info.exported
            s!"{definition.context}.{fieldName}"
          if let some rawDefault := definition.field.default_value then
            let defaultName ← rawDefault.toString?.getDM
              (throw s!"{definition.context}.{fieldName}: enum default contains invalid UTF-8")
            unless info.values.contains defaultName do
              throw s!"{definition.context}.{fieldName}: enum default `{defaultName}` is not a value of `{info.context}`"
      | some (.message info) =>
          throw s!"{definition.context}.{fieldName}: enum field type_name `{rawType}` names message `{info.context}`"
      | none =>
          throw s!"{definition.context}.{fieldName}: enum field type_name `{rawType}` cannot be resolved in the descriptor set"
  | .TYPE_DOUBLE | .TYPE_FLOAT
  | .TYPE_INT64 | .TYPE_UINT64 | .TYPE_INT32
  | .TYPE_FIXED64 | .TYPE_FIXED32 | .TYPE_BOOL | .TYPE_STRING
  | .TYPE_BYTES | .TYPE_UINT32
  | .TYPE_SFIXED32 | .TYPE_SFIXED64 | .TYPE_SINT32 | .TYPE_SINT64 =>
      if let some rawType := definition.field.type_name then
        throw s!"{definition.context}.{fieldName}: scalar field cannot set type_name `{rawType}`"
  | .«Unknown.Value» value =>
      throw s!"{definition.context}.{fieldName}: unknown field type {value}"

private def validateRegisteredFieldTypeTargets
    (desc : FileDescriptorSet) (dependencies : DescriptorDependencyRegistry)
    (registry : DescriptorSetRegistry) : M Unit := do
  let mut definitions : Array FieldTypeDefinition := #[]
  for file in desc.file do
    let packageName := file.package.getD ""
    let fileName ← get!! file.name ! "file descriptor name is absent"
    for field in file.extension do
      definitions := definitions.push {
        fileName
        scope := packageName
        context := s!"{fileName} extension"
        field
      }
    definitions :=
      definitions ++
        (← collectMessageFieldTypeDefinitions
          fileName packageName file.message_type)
  for definition in definitions do
    validateRegisteredFieldTypeTarget dependencies registry definition

private partial def validateRegisteredMapEntryOwners
    (registry : DescriptorSetRegistry) (prefixName : String)
    (messages : Array DescriptorProto) : M Unit := do
  for msg in messages do
    let messageName ← get!! msg.name !
      s!"{prefixName}: message name is absent"
    let messageFullName :=
      if prefixName.isEmpty then messageName
      else prefixName ++ "." ++ messageName
    for entry in msg.nested_type do
      if isMapEntryDescriptor entry then
        let entryName ← get!! entry.name !
          s!"{messageFullName}: map entry name is absent"
        let entryFullName := messageFullName ++ "." ++ entryName
        let owners := msg.field.filter fun field =>
          match field.type_name >>= fun rawType =>
              resolveRegisteredType? registry messageFullName rawType with
          | some (.message info) => info.context == entryFullName
          | _ => false
        if owners.size != 1 then
          throw s!"{entryFullName}: map entry must be referenced by exactly one field in {messageFullName}"
        let owner := owners[0]!
        let ownerName ← get!! owner.name !
          s!"{messageFullName}: map field name is absent"
        if owner.type != some .TYPE_MESSAGE then
          throw s!"{messageFullName}.{ownerName}: map field must have type TYPE_MESSAGE"
        if owner.label != some .LABEL_REPEATED then
          throw s!"{messageFullName}.{ownerName}: map field must have label LABEL_REPEATED"
        if owner.extendee.isSome || owner.oneof_index.isSome ||
            owner.default_value.isSome || owner.proto3_optional.getD false then
          throw s!"{messageFullName}.{ownerName}: map field cannot be an extension, oneof member, defaulted, or proto3_optional"
        let expectedName := expectedMapEntryName ownerName
        if entryName != expectedName then
          throw s!"{entryFullName}: map entry name must be `{expectedName}` for field `{ownerName}`"
    validateRegisteredMapEntryOwners registry messageFullName msg.nested_type

private def validateRegisteredMessageReference
    (dependencies : DescriptorDependencyRegistry)
    (registry : DescriptorSetRegistry)
    (sourceFile scope context rawType : String) :
    M Unit := do
  if rawType.isEmpty then
    throw s!"{context}: message type name is empty"
  match resolveRegisteredTypeForFile? dependencies registry
      sourceFile scope rawType with
  | some (.message info) =>
      validateDescriptorTargetVisibility dependencies
        sourceFile info.fileName info.exported context
  | some (.enum info) =>
      throw s!"{context}: message type name `{rawType}` names enum `{info.context}`"
  | none =>
      throw s!"{context}: message type name `{rawType}` cannot be resolved in the descriptor set"

private def validateRegisteredServiceMethodTargets
    (desc : FileDescriptorSet)
    (dependencies : DescriptorDependencyRegistry)
    (registry : DescriptorSetRegistry) : M Unit := do
  for file in desc.file do
    let packageName := file.package.getD ""
    let fileName ← get!! file.name ! "file descriptor name is absent"
    for service in file.service do
      let serviceName ← get!! service.name !
        s!"{fileName}: service name is absent"
      let serviceScope :=
        if packageName.isEmpty then serviceName
        else packageName ++ "." ++ serviceName
      for method in service.method do
        let methodName ← get!! method.name !
          s!"{serviceScope}: method name is absent"
        let inputType ← get!! method.input_type !
          s!"{serviceScope}.{methodName}: method input_type is absent"
        validateRegisteredMessageReference dependencies registry
          fileName serviceScope
          s!"{serviceScope}.{methodName} input_type" inputType
        let outputType ← get!! method.output_type !
          s!"{serviceScope}.{methodName}: method output_type is absent"
        validateRegisteredMessageReference dependencies registry
          fileName serviceScope
          s!"{serviceScope}.{methodName} output_type" outputType

private def validateRegisteredMapValueTargets
    (dependencies : DescriptorDependencyRegistry)
    (registry : DescriptorSetRegistry) : M Unit := do
  for definition in registry.mapValues do
    match definition.field.type, definition.field.type_name with
    | some .TYPE_ENUM, some rawType =>
        match resolveRegisteredTypeForFile? dependencies registry
            definition.fileName definition.context rawType with
        | some (.enum info) =>
            if info.firstNumber != some 0 then
              throw s!"{definition.context}.value: map value enum `{info.context}` must define numeric value 0 as its first value"
        | some (.message info) =>
            throw s!"{definition.context}.value: TYPE_ENUM names message `{info.context}`"
        | none => pure ()
    | some .TYPE_MESSAGE, some rawType =>
        match resolveRegisteredTypeForFile? dependencies registry
            definition.fileName definition.context rawType with
        | some (.message info) =>
            if info.isMapEntry then
              throw s!"{definition.context}.value: map values cannot be another map"
        | some (.enum info) =>
            throw s!"{definition.context}.value: TYPE_MESSAGE names enum `{info.context}`"
        | none => pure ()
    | _, _ => pure ()

@[inline]
private def isProtoIdentStart (c : Char) : Bool :=
  let n := c.toNat
  c == '_' || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122)

@[inline]
private def isProtoIdentRest (c : Char) : Bool :=
  isProtoIdentStart c || let n := c.toNat; 48 ≤ n && n ≤ 57

private def isProtoSimpleIdent (value : String) : Bool :=
  match value.toList with
  | [] => false
  | first :: rest =>
      isProtoIdentStart first && rest.all isProtoIdentRest

private def validateProtoSimpleIdent
    (context value : String) : M Unit := do
  unless isProtoSimpleIdent value do
    throw s!"{context}: invalid protobuf identifier {value.quote}; expected [A-Za-z_][A-Za-z0-9_]*"

private def validateProtoFullIdent
    (context value : String) (allowLeadingDot : Bool := false) :
    M Unit := do
  let body :=
    if allowLeadingDot && value.startsWith "." then
      (value.drop 1).toString
    else
      value
  if body.isEmpty then
    throw s!"{context}: invalid protobuf full identifier {value.quote}"
  for component in body.splitOn "." do
    validateProtoSimpleIdent context component

private def validateRawFieldIdentifiers
    (context : String) (field : FieldDescriptorProto) : M Unit := do
  if let some name := field.name then
    validateProtoSimpleIdent (context ++ " field name") name
  if let some typeName := field.type_name then
    validateProtoFullIdent
      (context ++ " field type_name") typeName (allowLeadingDot := true)
  if let some extendee := field.extendee then
    validateProtoFullIdent
      (context ++ " field extendee") extendee (allowLeadingDot := true)
  if field.type == some .TYPE_ENUM then
    if let some rawDefault := field.default_value then
      let defaultName ← rawDefault.toString?.getDM
        (throw s!"{context} field enum default contains invalid UTF-8")
      -- Proto source accepts an unqualified enum value identifier here, and
      -- protoc stores that exact simple name in `default_value`.
      validateProtoSimpleIdent
        (context ++ " field enum default") defaultName

private def validateRawEnumIdentifiers
    (context : String) (e : EnumDescriptorProto) : M Unit := do
  let enumContext :=
    match e.name with
    | some name => context ++ " enum " ++ name.quote
    | none => context ++ " enum"
  if let some name := e.name then
    validateProtoSimpleIdent (context ++ " enum name") name
  for value in e.value do
    if let some name := value.name then
      validateProtoSimpleIdent (enumContext ++ " value name") name

private partial def validateRawMessageIdentifiers
    (context : String) (msg : DescriptorProto) : M Unit := do
  let messageContext :=
    match msg.name with
    | some name => context ++ " message " ++ name.quote
    | none => context ++ " message"
  if let some name := msg.name then
    validateProtoSimpleIdent (context ++ " message name") name
  for field in msg.field do
    validateRawFieldIdentifiers messageContext field
  for field in msg.extension do
    validateRawFieldIdentifiers (messageContext ++ " extension") field
  for oneofDecl in msg.oneof_decl do
    if let some name := oneofDecl.name then
      validateProtoSimpleIdent (messageContext ++ " oneof name") name
  for nested in msg.nested_type do
    validateRawMessageIdentifiers messageContext nested
  for e in msg.enum_type do
    validateRawEnumIdentifiers messageContext e

private def validateRawServiceIdentifiers
    (context : String) (service : ServiceDescriptorProto) : M Unit := do
  let serviceContext :=
    match service.name with
    | some name => context ++ " service " ++ name.quote
    | none => context ++ " service"
  if let some name := service.name then
    validateProtoSimpleIdent (context ++ " service name") name
  for method in service.method do
    let methodContext :=
      match method.name with
      | some name => serviceContext ++ " method " ++ name.quote
      | none => serviceContext ++ " method"
    if let some name := method.name then
      validateProtoSimpleIdent (serviceContext ++ " method name") name
    if let some inputType := method.input_type then
      validateProtoFullIdent
        (methodContext ++ " input_type") inputType (allowLeadingDot := true)
    if let some outputType := method.output_type then
      validateProtoFullIdent
        (methodContext ++ " output_type") outputType (allowLeadingDot := true)

/--
Validate source-language identifiers on the raw descriptor set.

This deliberately runs only at the whole-set boundary, before collision-proof
Lean names such as `rec.protobuf` are introduced by `sanitizeFileDescriptorSet`.
File paths, JSON names, defaults, and reserved-name strings are not protobuf
identifiers and are intentionally left untouched.
-/
private def validateRawFileDescriptorSetIdentifiers
    (desc : FileDescriptorSet) : M Unit := do
  for file in desc.file do
    let context :=
      match file.name with
      | some name => "file " ++ name.quote
      | none => "file descriptor"
    if let some packageName := file.package then
      unless packageName.isEmpty do
        validateProtoFullIdent (context ++ " package") packageName
    for msg in file.message_type do
      validateRawMessageIdentifiers context msg
    for e in file.enum_type do
      validateRawEnumIdentifiers context e
    for field in file.extension do
      validateRawFieldIdentifiers (context ++ " extension") field
    for service in file.service do
      validateRawServiceIdentifiers context service

private structure DescriptorSymbolInfo where
  context : String
  isPackage : Bool

private abbrev DescriptorSymbolRegistry :=
  Std.HashMap String DescriptorSymbolInfo

private def registerDescriptorSymbol
    (registry : DescriptorSymbolRegistry) (fullName context : String) :
    M DescriptorSymbolRegistry := do
  if let some previous := registry[fullName]? then
    throw s!"protobuf symbol `{fullName}` is declared more than once: {previous.context}; {context}"
  return registry.insert fullName { context, isPackage := false }

private def registerDescriptorPackageSymbols
    (registry : DescriptorSymbolRegistry)
    (packageName fileName : String) : M DescriptorSymbolRegistry := do
  if packageName.isEmpty then
    return registry
  let mut registry := registry
  let mut packagePrefix := ""
  for component in packageName.splitOn "." do
    packagePrefix := qualifyProtoSymbol packagePrefix component
    match registry[packagePrefix]? with
    | some info =>
        unless info.isPackage do
          throw s!"protobuf symbol `{packagePrefix}` is declared more than once: {info.context}; package `{packageName}` from `{fileName}`"
    | none =>
        registry := registry.insert packagePrefix {
          context := s!"package `{packagePrefix}` from `{fileName}`"
          isPackage := true
        }
  return registry

private def registerEnumDescriptorSymbols
    (scope : String) (e : EnumDescriptorProto)
    (initial : DescriptorSymbolRegistry) : M DescriptorSymbolRegistry := do
  let enumName ← get!! e.name ! s!"{scope}: enum name is absent"
  let enumFullName := qualifyProtoSymbol scope enumName
  let mut registry ←
    registerDescriptorSymbol initial enumFullName s!"enum `{enumFullName}`"
  /-
  Protobuf enum values follow C++ scoping: their symbols are siblings of the
  enum declaration, rather than children of the enum's full name.
  -/
  for value in e.value do
    let valueName ← get!! value.name !
      s!"{enumFullName}: enum value name is absent"
    let valueFullName := qualifyProtoSymbol scope valueName
    registry ← registerDescriptorSymbol registry valueFullName
      s!"enum value `{enumFullName}.{valueName}`"
  return registry

private partial def registerMessageDescriptorSymbols
    (scope : String) (msg : DescriptorProto)
    (initial : DescriptorSymbolRegistry) : M DescriptorSymbolRegistry := do
  let messageName ← get!! msg.name ! s!"{scope}: message name is absent"
  let messageFullName := qualifyProtoSymbol scope messageName
  let mut registry ←
    registerDescriptorSymbol initial messageFullName
      s!"message `{messageFullName}`"
  for field in msg.field do
    let fieldName ← get!! field.name !
      s!"{messageFullName}: field name is absent"
    let fieldFullName := qualifyProtoSymbol messageFullName fieldName
    registry ← registerDescriptorSymbol registry fieldFullName
      s!"field `{fieldFullName}`"
  for oneofDecl in msg.oneof_decl do
    let oneofName ← get!! oneofDecl.name !
      s!"{messageFullName}: oneof name is absent"
    let oneofFullName := qualifyProtoSymbol messageFullName oneofName
    registry ← registerDescriptorSymbol registry oneofFullName
      s!"oneof `{oneofFullName}`"
  for field in msg.extension do
    let fieldName ← get!! field.name !
      s!"{messageFullName}: extension field name is absent"
    let fieldFullName := qualifyProtoSymbol messageFullName fieldName
    registry ← registerDescriptorSymbol registry fieldFullName
      s!"extension field `{fieldFullName}`"
  for nested in msg.nested_type do
    registry ←
      registerMessageDescriptorSymbols messageFullName nested registry
  for e in msg.enum_type do
    registry ← registerEnumDescriptorSymbols messageFullName e registry
  return registry

private def validateDescriptorSymbolUniqueness
    (desc : FileDescriptorSet) : M Unit := do
  let mut registry : DescriptorSymbolRegistry := {}
  for file in desc.file do
    let fileName ← get!! file.name ! "file descriptor name is absent"
    let packageName := file.package.getD ""
    registry ←
      registerDescriptorPackageSymbols registry packageName fileName
    for msg in file.message_type do
      registry ← registerMessageDescriptorSymbols packageName msg registry
    for e in file.enum_type do
      registry ← registerEnumDescriptorSymbols packageName e registry
    for field in file.extension do
      let fieldName ← get!! field.name !
        s!"{fileName}: extension field name is absent"
      let fieldFullName := qualifyProtoSymbol packageName fieldName
      registry ← registerDescriptorSymbol registry fieldFullName
        s!"extension field `{fieldFullName}` from `{fileName}`"
    for service in file.service do
      let serviceName ← get!! service.name !
        s!"{fileName}: service name is absent"
      let serviceFullName := qualifyProtoSymbol packageName serviceName
      registry ← registerDescriptorSymbol registry serviceFullName
        s!"service `{serviceFullName}`"
      for method in service.method do
        let methodName ← get!! method.name !
          s!"{serviceFullName}: method name is absent"
        let methodFullName := qualifyProtoSymbol serviceFullName methodName
        registry ← registerDescriptorSymbol registry methodFullName
          s!"method `{methodFullName}`"

private def buildDescriptorSetRegistry
    (desc : FileDescriptorSet) : M DescriptorSetRegistry := do
  let mut registry : DescriptorSetRegistry := {}
  for file in desc.file do
    let fileName ← get!! file.name ! "file descriptor name is absent"
    let packageName := file.package.getD ""
    unless packageName.isEmpty do
      let mut packagePrefix := ""
      for component in packageName.splitOn "." do
        packagePrefix := qualifyProtoSymbol packagePrefix component
        registry := {
          registry with
          aggregates := registry.aggregates.insert packagePrefix ()
        }
    validateFileBuiltinFeatures file
    validateSymbolVisibilityFeatureSupport file
    let defaultVisibility ← descriptorDefaultSymbolVisibility file
    registry ←
      registerEnumTargets fileName packageName
        defaultVisibility true false file.enum_type registry
    registry ← registerMessageExtensionTargets
      fileName packageName defaultVisibility true
      file.message_type registry
    for service in file.service do
      let serviceName ← get!! service.name !
        s!"{fileName}: service name is absent"
      let serviceFullName := qualifyProtoSymbol packageName serviceName
      registry := {
        registry with
        aggregates := registry.aggregates.insert serviceFullName ()
      }
  return registry

private def registeredTypeTargetName
    (target : RegisteredTypeTarget) : String :=
  match target with
  | .message info => info.context
  | .enum info => info.context

private def registeredTypeTargetInferredFieldType
    (target : RegisteredTypeTarget) : FieldDescriptorProto.Type :=
  match target with
  | .message _ => .TYPE_MESSAGE
  | .enum _ => .TYPE_ENUM

private def validateRegisteredTypeTargetVisibility
    (dependencies : DescriptorDependencyRegistry)
    (sourceFile context : String) (target : RegisteredTypeTarget) : M Unit :=
  match target with
  | .message info =>
      validateDescriptorTargetVisibility dependencies
        sourceFile info.fileName info.exported context
  | .enum info =>
      validateDescriptorTargetVisibility dependencies
        sourceFile info.fileName info.exported context

private def normalizeFieldDescriptor
    (dependencies : DescriptorDependencyRegistry)
    (registry : DescriptorSetRegistry)
    (fileName scope : String) (field : FieldDescriptorProto) :
    M FieldDescriptorProto := do
  let fieldName := field.name.getD "<unnamed>"
  let context := scope ++ "." ++ fieldName
  let resolvedType? ←
    match field.type_name with
    | none => pure none
    | some rawType =>
        match resolveRegisteredTypeForFile?
            dependencies registry fileName scope rawType with
        | some target =>
            validateRegisteredTypeTargetVisibility
              dependencies fileName context target
            pure (some target)
        | none => pure none
  let fieldType ←
    match field.type with
    | some fieldType => pure fieldType
    | none =>
        match resolvedType?, field.type_name with
        | some target, _ =>
            pure (registeredTypeTargetInferredFieldType target)
        | none, none => pure .TYPE_DOUBLE
        | none, some rawType =>
            throw s!"{context}: field type_name `{rawType}` cannot be resolved in the descriptor set"
  let canonicalTypeName :=
    resolvedType?.map fun target =>
      "." ++ registeredTypeTargetName target
  let canonicalExtendee ←
    match field.extendee with
    | none => pure none
    | some rawExtendee =>
        let target ← resolveExtensionTarget dependencies
          registry fileName scope rawExtendee
        pure (some ("." ++ target))
  return {
    field with
    label := some (field.label.getD .LABEL_OPTIONAL)
    type := some fieldType
    type_name := canonicalTypeName.orElse fun _ => field.type_name
    extendee := canonicalExtendee
  }

private partial def normalizeMessageDescriptor
    (dependencies : DescriptorDependencyRegistry)
    (registry : DescriptorSetRegistry)
    (fileName prefixName : String) (msg : DescriptorProto) :
    M DescriptorProto := do
  let messageName ← get!! msg.name ! s!"{prefixName}: message name is absent"
  let fullName := qualifyProtoSymbol prefixName messageName
  let fields ← msg.field.mapM
    (normalizeFieldDescriptor dependencies registry fileName fullName)
  let extensions ← msg.extension.mapM
    (normalizeFieldDescriptor dependencies registry fileName fullName)
  let nested ← msg.nested_type.mapM
    (normalizeMessageDescriptor
      dependencies registry fileName fullName)
  return {
    msg with
    field := fields
    extension := extensions
    nested_type := nested
  }

private def normalizeServiceDescriptor
    (dependencies : DescriptorDependencyRegistry)
    (registry : DescriptorSetRegistry)
    (fileName packageName : String) (service : ServiceDescriptorProto) :
    M ServiceDescriptorProto := do
  let serviceName ← get!! service.name !
    s!"{fileName}: service name is absent"
  let serviceScope := qualifyProtoSymbol packageName serviceName
  let methods ← service.method.mapM fun method => do
    let methodName := method.name.getD "<unnamed>"
    let normalizeMethodType
        (role : String) (rawType? : Option String) :
        M (Option String) := do
      let some rawType := rawType? | return none
      match resolveRegisteredTypeForFile?
          dependencies registry fileName serviceScope rawType with
      | some target =>
          validateRegisteredTypeTargetVisibility dependencies fileName
            s!"{serviceScope}.{methodName} {role}" target
          return some ("." ++ registeredTypeTargetName target)
      | none => return some rawType
    return {
      method with
      input_type := ← normalizeMethodType "input_type" method.input_type
      output_type := ← normalizeMethodType "output_type" method.output_type
    }
  return { service with method := methods }

def normalizeFileDescriptorSet
    (desc : FileDescriptorSet) : M FileDescriptorSet := do
  validateRawFileDescriptorSetIdentifiers desc
  let dependencies ← validateDescriptorDependencies desc
  validateDescriptorSymbolUniqueness desc
  let registry ← buildDescriptorSetRegistry desc
  let files ← desc.file.mapM fun file => do
    let fileName ← get!! file.name ! "file descriptor name is absent"
    let packageName := file.package.getD ""
    let messages ← file.message_type.mapM
      (normalizeMessageDescriptor
        dependencies registry fileName packageName)
    let extensions ← file.extension.mapM
      (normalizeFieldDescriptor
        dependencies registry fileName packageName)
    let services ← file.service.mapM
      (normalizeServiceDescriptor
        dependencies registry fileName packageName)
    return {
      file with
      message_type := messages
      extension := extensions
      service := services
    }
  return { file := files }

/--
Validate descriptor relationships that can only be checked with the complete
descriptor set.

This is compile-time metadata validation, not a runtime descriptor registry.
It resolves every file- and message-scoped extension against the set's message
declarations, checks the target's extension ranges, and enforces the protobuf
rule that a field number is globally unique within its extendee.  The same
static type registry checks map values that name imported enums or messages.
-/
private def validateNormalizedFileDescriptorSet
    (desc : FileDescriptorSet) : M Unit := do
  validateRawFileDescriptorSetIdentifiers desc
  let dependencies ← validateDescriptorDependencies desc
  validateDescriptorSymbolUniqueness desc
  let registry ← buildDescriptorSetRegistry desc
  validateRegisteredFieldTypeTargets desc dependencies registry
  for file in desc.file do
    validateRegisteredMapEntryOwners registry
      (file.package.getD "") file.message_type
  validateRegisteredServiceMethodTargets desc dependencies registry
  validateRegisteredMapValueTargets dependencies registry
  let targets := registry.messages

  let mut definitions : Array ExtensionDefinition := #[]
  for file in desc.file do
    let packageName := file.package.getD ""
    let fileName ← get!! file.name ! "file descriptor name is absent"
    for field in file.extension do
      definitions := definitions.push {
        fileName
        scope := packageName
        context := s!"{fileName} extension"
        field
      }
    definitions :=
      definitions ++
        (← collectMessageExtensionDefinitions
          fileName packageName file.message_type)

  let mut occupied : Std.HashMap (String × Nat) String := {}
  for definition in definitions do
    let fieldName ← get!! definition.field.name !
      s!"{definition.context}: extension field name is absent"
    let fieldNumber ←
      validateDescriptorFieldNumber definition.context definition.field
    let rawExtendee ← get!! definition.field.extendee !
      s!"{definition.context}.{fieldName}: extendee is absent"
    let extendee ←
      resolveExtensionTarget dependencies registry definition.fileName
        definition.scope rawExtendee
    let target := targets[extendee]!
    validateDescriptorTargetVisibility dependencies
      definition.fileName target.fileName target.exported
      s!"{definition.context}.{fieldName}"
    unless target.ranges.any fun range =>
        range.1 ≤ fieldNumber && fieldNumber < range.2 do
      throw s!"{definition.context}.{fieldName}: extension number {fieldNumber} is outside every extension range of `{extendee}`"
    let key := (extendee, fieldNumber)
    if let some previous := occupied[key]? then
      throw s!"{definition.context}.{fieldName}: extension number {fieldNumber} for `{extendee}` is already declared by {previous}"
    occupied := occupied.insert key s!"{definition.context}.{fieldName}"

def prepareFileDescriptorSet
    (desc : FileDescriptorSet) : M FileDescriptorSet := do
  let desc ← normalizeFileDescriptorSet desc
  validateNormalizedFileDescriptorSet desc
  return desc

def validateFileDescriptorSet (desc : FileDescriptorSet) : M Unit := do
  discard <| prepareFileDescriptorSet desc

def checkFieldName (name : String) : M String := do
  return sanitizeFieldName name

def checkEnumValueName (name : String) : M String := do
  return sanitizeEnumValueName name

@[always_inline]
instance : MonadRef M where
  getRef := fun c => return c.ref
  withRef stx x := fun c => x {c with ref := stx}

@[always_inline]
instance : MonadQuotation M where
  getCurrMacroScope := fun c => return c.currentMacroScope
  getContext := return .anonymous
  withFreshMacroScope := M.withFreshMacroScope

scoped macro "is_true!! " v:term:max : term => ``(Option.getD $v false)

open Parser Term in
scoped syntax:min term "&." noWs (fieldIdx <|> rawIdent) argument* : term

scoped macro_rules
  | `($x&.%$tk$f $args*) => `($x >>= (fun x => x |>.%$tk$f $args*))

scoped syntax ppRealGroup(ppRealFill(ppIndent("if! " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

scoped macro_rules
  | `(if! $c then $t else $e) => `(if (Option.getD $c false) then $t else $e)

scoped prefix:min "!! " => Option.getD (dflt := false)

private def octalDigit? (b : UInt8) : Option Nat :=
  let n := b.toNat
  if 48 ≤ n && n ≤ 55 then some (n - 48) else none

private def hexDigit? (b : UInt8) : Option Nat :=
  let n := b.toNat
  if 48 ≤ n && n ≤ 57 then
    some (n - 48)
  else if 65 ≤ n && n ≤ 70 then
    some (n - 65 + 10)
  else if 97 ≤ n && n ≤ 102 then
    some (n - 97 + 10)
  else
    none

/--
Decode the C-escaped representation used by
`google.protobuf.FieldDescriptorProto.default_value` for `bytes` fields.
-/
partial def decodeBytesDefault (raw : String) : Except String ByteArray := do
  let rec takeDigits (digit? : UInt8 → Option Nat) (radix fuel : Nat)
      (input : List UInt8) (value : Nat) : Nat × List UInt8 :=
    match fuel, input with
    | 0, _ => (value, input)
    | _, [] => (value, [])
    | fuel + 1, b :: rest =>
        match digit? b with
        | none => (value, input)
        | some digit => takeDigits digit? radix fuel rest (value * radix + digit)
  let rec loop (input : List UInt8) (out : ByteArray) : Except String ByteArray := do
    match input with
    | [] => return out
    | b :: rest =>
        if b != 92 then
          loop rest (out.push b)
        else
          match rest with
          | [] => throw "unterminated escape in bytes default"
          | esc :: tail =>
              let simple? :=
                match esc.toNat with
                | 97 => some 7   -- \a
                | 98 => some 8   -- \b
                | 102 => some 12 -- \f
                | 110 => some 10 -- \n
                | 114 => some 13 -- \r
                | 116 => some 9  -- \t
                | 118 => some 11 -- \v
                | 92 => some 92  -- \\
                | 63 => some 63  -- \?
                | 39 => some 39  -- \'
                | 34 => some 34  -- \"
                | _ => none
              match simple? with
              | some value => loop tail (out.push value.toUInt8)
              | none =>
                  if let some first := octalDigit? esc then
                    let (value, remaining) := takeDigits octalDigit? 8 2 tail first
                    if value > 255 then
                      throw s!"octal escape is out of byte range in default: {value}"
                    loop remaining (out.push value.toUInt8)
                  else if esc == 120 || esc == 88 then -- \x or \X
                    match tail with
                    | [] => throw "hex escape has no digits in bytes default"
                    | firstByte :: hexTail =>
                        let some first := hexDigit? firstByte
                          | throw "hex escape has no digits in bytes default"
                        let (value, remaining) := takeDigits hexDigit? 16 1 hexTail first
                        loop remaining (out.push value.toUInt8)
                  else
                    throw s!"unknown escape in bytes default: \\{Char.ofNat esc.toNat}"
  loop raw.toUTF8.data.toList ByteArray.empty

private inductive DescriptorFloatMagnitude where
  | decimal (mantissa : Nat) (exponent10 : Int)
  | binary (mantissa : Nat) (exponent2 : Int)
  | infinity
  | nan

private structure DescriptorFloatValue where
  negative : Bool
  magnitude : DescriptorFloatMagnitude

private def descriptorFloatDigitValue? (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then
    some (n - 48)
  else if 65 ≤ n && n ≤ 70 then
    some (n - 65 + 10)
  else if 97 ≤ n && n ≤ 102 then
    some (n - 97 + 10)
  else
    none

private def takeDescriptorFloatDigits
    (radix : Nat) : List Char → Nat → Nat → Nat × Nat × List Char
  | [], value, count => (value, count, [])
  | c :: rest, value, count =>
      match descriptorFloatDigitValue? c with
      | some digit =>
          if digit < radix then
            takeDescriptorFloatDigits radix rest
              (value * radix + digit) (count + 1)
          else
            (value, count, c :: rest)
      | none => (value, count, c :: rest)

private def parseDescriptorFloatExponent? (input : List Char) : Option Int := do
  let (negative, input) :=
    match input with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, input)
  let (magnitude, count, rest) :=
    takeDescriptorFloatDigits 10 input 0 0
  if count == 0 || !rest.isEmpty then
    none
  else
    let value := Int.ofNat magnitude
    pure (if negative then -value else value)

private def parseDescriptorDecimalFloat?
    (body : List Char) : Option DescriptorFloatMagnitude := do
  let (whole, wholeCount, rest) :=
    takeDescriptorFloatDigits 10 body 0 0
  let (mantissa, fractionalCount, rest) :=
    match rest with
    | '.' :: tail =>
        let (value, count, tail) :=
          takeDescriptorFloatDigits 10 tail whole 0
        (value, count, tail)
    | _ => (whole, 0, rest)
  if wholeCount + fractionalCount == 0 then
    none
  else
    let exponent ←
      match rest with
      | [] => some 0
      | 'e' :: tail | 'E' :: tail =>
          parseDescriptorFloatExponent? tail
      | _ => none
    pure (.decimal mantissa (exponent - Int.ofNat fractionalCount))

private def parseDescriptorHexFloat?
    (body : List Char) : Option DescriptorFloatMagnitude := do
  let (whole, wholeCount, rest) :=
    takeDescriptorFloatDigits 16 body 0 0
  let (mantissa, fractionalCount, rest) :=
    match rest with
    | '.' :: tail =>
        let (value, count, tail) :=
          takeDescriptorFloatDigits 16 tail whole 0
        (value, count, tail)
    | _ => (whole, 0, rest)
  if wholeCount + fractionalCount == 0 then
    none
  else
    let exponent ←
      match rest with
      | [] => some 0
      | 'p' :: tail | 'P' :: tail =>
          parseDescriptorFloatExponent? tail
      | _ => none
    pure (.binary mantissa (exponent - Int.ofNat (4 * fractionalCount)))

private def isDescriptorNanPayload (body : List Char) : Bool :=
  match body with
  | 'n' :: 'a' :: 'n' :: '(' :: rest =>
      match rest.reverse with
      | ')' :: payloadRev =>
          payloadRev.all fun c =>
            let n := c.toNat
            (48 ≤ n && n ≤ 57) ||
              (65 ≤ n && n ≤ 90) ||
              (97 ≤ n && n ≤ 122) ||
              c == '_'
      | _ => false
  | _ => false

/--
Parse the numeric text carried by `FieldDescriptorProto.default_value`.

This is deliberately separate from the `.proto` source-token parser.  In the
C++ descriptor implementation integer-shaped floating defaults are parsed as
decimal (`"077"` is 77, not source-level octal), leading zeroes are accepted,
and hexadecimal floating syntax is accepted by `NoLocaleStrtod`.  A protoc
request normally contains an already canonical spelling, but the public
descriptor API and the plugin boundary also have to handle handcrafted input
without silently changing its value.
-/
private def parseDescriptorFloat? (raw : String) :
    Option DescriptorFloatValue := do
  let (negative, body) :=
    match raw.toList with
    | '-' :: rest => (true, rest)
    | '+' :: _ => (false, [])
    | rest => (false, rest)
  if body.isEmpty then
    none
  else
    let lower := (String.ofList body).toLower.toList
    let magnitude ←
      if lower == "inf".toList || lower == "infinity".toList then
        some .infinity
      else if lower == "nan".toList || isDescriptorNanPayload lower then
        some .nan
      else
        match body with
        | '0' :: 'x' :: rest | '0' :: 'X' :: rest =>
            parseDescriptorHexFloat? rest
        | _ =>
            parseDescriptorDecimalFloat? body
    pure { negative, magnitude }

private def descriptorSpecialFloatSyntax
    (negative nan : Bool) : M (TSyntax `options_value) := do
  let name :=
    if nan then
      `protobuf_nan
    else if negative then
      `protobuf_neg_inf
    else
      `protobuf_inf
  let id := Lean.mkIdent name
  `(options_value| $id:ident)

private def descriptorSignedNatSyntax
    (negative : Bool) (value : Nat) : M (TSyntax `options_value) := do
  let lit : TSyntax `num := ⟨Lean.Syntax.mkNumLit value.repr⟩
  if negative then
    `(options_value| -$lit:num)
  else
    `(options_value| $lit:num)

private def descriptorSignedScientificSyntax
    (negative : Bool) (mantissa : Nat) (exponent10 : Int) :
    M (TSyntax `options_value) := do
  let spelling := s!"{mantissa}e{exponent10}"
  let lit : TSyntax `scientific :=
    ⟨Lean.Syntax.mkScientificLit spelling⟩
  if negative then
    `(options_value| -$lit:scientific)
  else
    `(options_value| $lit:scientific)

private partial def cancelDescriptorDecimalZeros
    (mantissa : Nat) (exponent10 : Int) : Nat × Int :=
  if mantissa != 0 && mantissa % 10 == 0 then
    cancelDescriptorDecimalZeros (mantissa / 10) (exponent10 + 1)
  else
    (mantissa, exponent10)

private partial def cancelDescriptorBinaryDenominator
    (mantissa denominatorExponent : Nat) : Nat × Nat :=
  if denominatorExponent != 0 && mantissa % 2 == 0 then
    cancelDescriptorBinaryDenominator
      (mantissa / 2) (denominatorExponent - 1)
  else
    (mantissa, denominatorExponent)

private def descriptorBinaryFloatSyntax
    (negative : Bool) (mantissa : Nat) (exponent2 : Int) :
    M (TSyntax `options_value) := do
  if mantissa == 0 then
    descriptorSignedNatSyntax negative 0
  else
    match exponent2 with
    | .ofNat exponent =>
        descriptorSignedNatSyntax negative (mantissa * 2 ^ exponent)
    | .negSucc predecessor =>
        let denominatorExponent := predecessor + 1
        let (mantissa, denominatorExponent) :=
          cancelDescriptorBinaryDenominator mantissa denominatorExponent
        if denominatorExponent == 0 then
          descriptorSignedNatSyntax negative mantissa
        else
          /-
          `m / 2^k = (m * 5^k) / 10^k`.  This exact decimal
          representation denotes the already-rounded target value, so Lean
          elaboration preserves its IEEE-754 bits without retaining a runtime
          descriptor.
          -/
          descriptorSignedScientificSyntax negative
            (mantissa * 5 ^ denominatorExponent)
            (-Int.ofNat denominatorExponent)

private def descriptorFloatOrder10 (mantissa : Nat) (exponent10 : Int) :
    Int :=
  exponent10 + Int.ofNat (mantissa.repr.length - 1)

private def descriptorFloatOrder2 (mantissa : Nat) (exponent2 : Int) :
    Int :=
  exponent2 + Int.ofNat mantissa.log2

private def roundDescriptorRationalToEven
    (numerator denominator : Nat) : Nat :=
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  let twiceRemainder := 2 * remainder
  if twiceRemainder > denominator then
    quotient + 1
  else if twiceRemainder == denominator && quotient % 2 == 1 then
    quotient + 1
  else
    quotient

private def descriptorRationalBelowPowerOfTwo
    (numerator denominator : Nat) (exponent : Int) : Bool :=
  match exponent with
  | .ofNat exponent =>
      decide (numerator < denominator * 2 ^ exponent)
  | .negSucc predecessor =>
      decide (numerator * 2 ^ (predecessor + 1) < denominator)

private def descriptorRationalFloorLog2
    (numerator denominator : Nat) : Int :=
  let candidate :=
    Int.ofNat numerator.log2 - Int.ofNat denominator.log2
  if descriptorRationalBelowPowerOfTwo numerator denominator candidate then
    candidate - 1
  else
    candidate

private def roundScaledDescriptorRational
    (numerator denominator : Nat) (shift : Int) : Nat :=
  match shift with
  | .ofNat shift =>
      roundDescriptorRationalToEven (numerator * 2 ^ shift) denominator
  | .negSucc predecessor =>
      roundDescriptorRationalToEven numerator
        (denominator * 2 ^ (predecessor + 1))

/--
Round a positive exact rational to an IEEE binary format.  `fractionBits` is
52 for binary64 or 23 for binary32; `bias` is respectively 1023 or 127.
-/
private def descriptorPositiveRationalBits
    (numerator denominator fractionBits bias : Nat) : Nat :=
  if numerator == 0 then
    0
  else
    let exponent := descriptorRationalFloorLog2 numerator denominator
    let minNormalExponent := 1 - Int.ofNat bias
    let maxNormalExponent := Int.ofNat bias
    let implicitBit := 2 ^ fractionBits
    let infinityBits := (2 * bias + 1) * implicitBit
    if exponent < minNormalExponent then
      let subnormalShift := bias + fractionBits - 1
      let significand :=
        roundScaledDescriptorRational numerator denominator
          (Int.ofNat subnormalShift)
      if significand == 0 then
        0
      else if significand ≥ implicitBit then
        implicitBit
      else
        significand
    else if exponent > maxNormalExponent then
      infinityBits
    else
      let significand :=
        roundScaledDescriptorRational numerator denominator
          (Int.ofNat fractionBits - exponent)
      let (significand, exponent) :=
        if significand ≥ 2 * implicitBit then
          (implicitBit, exponent + 1)
        else
          (significand, exponent)
      if exponent > maxNormalExponent then
        infinityBits
      else
        (exponent + Int.ofNat bias).toNat * implicitBit +
          (significand - implicitBit)

private def descriptorFloat64MagnitudeBits :
    DescriptorFloatMagnitude → Nat
  | .infinity => (2 * 1023 + 1) * 2 ^ 52
  | .nan => (2 * 1023 + 1) * 2 ^ 52 + 2 ^ 51
  | .decimal mantissa exponent10 =>
      if mantissa == 0 then
        0
      else
        let order := descriptorFloatOrder10 mantissa exponent10
        if order > 400 then
          (2 * 1023 + 1) * 2 ^ 52
        else if order < -400 then
          0
        else
          let (mantissa, exponent10) :=
            cancelDescriptorDecimalZeros mantissa exponent10
          match exponent10 with
          | .ofNat exponent =>
              descriptorPositiveRationalBits
                (mantissa * 10 ^ exponent) 1 52 1023
          | .negSucc predecessor =>
              descriptorPositiveRationalBits
                mantissa (10 ^ (predecessor + 1)) 52 1023
  | .binary mantissa exponent2 =>
      if mantissa == 0 then
        0
      else
        let order := descriptorFloatOrder2 mantissa exponent2
        if order > 1200 then
          (2 * 1023 + 1) * 2 ^ 52
        else if order < -1300 then
          0
        else
          match exponent2 with
          | .ofNat exponent =>
              descriptorPositiveRationalBits
                (mantissa * 2 ^ exponent) 1 52 1023
          | .negSucc predecessor =>
              descriptorPositiveRationalBits
                mantissa (2 ^ (predecessor + 1)) 52 1023

private def descriptorFloat64Bits (value : DescriptorFloatValue) : Nat :=
  let magnitudeBits := descriptorFloat64MagnitudeBits value.magnitude
  match value.magnitude with
  | .nan => magnitudeBits
  | _ =>
      if value.negative then magnitudeBits + 2 ^ 63 else magnitudeBits

private def descriptorFloat32BitsOfFloat64Bits (bits : Nat) : Nat :=
  let negative := bits ≥ 2 ^ 63
  let magnitudeBits := bits % (2 ^ 63)
  let exponent := magnitudeBits / (2 ^ 52)
  let fraction := magnitudeBits % (2 ^ 52)
  if exponent == 2047 then
    if fraction == 0 then
      (if negative then 2 ^ 31 else 0) + (2 * 127 + 1) * 2 ^ 23
    else
      (2 * 127 + 1) * 2 ^ 23 + 2 ^ 22
  else if magnitudeBits > 0x47efffffe0000000 &&
      magnitudeBits ≤ 0x47effffff0000000 then
    (if negative then 2 ^ 31 else 0) + 0x7f7fffff
  else
    let (mantissa, exponent2) :=
      if exponent == 0 then
        (fraction, (-1074 : Int))
      else
        (2 ^ 52 + fraction, Int.ofNat exponent - 1075)
    let roundedMagnitude :=
      if mantissa == 0 then
        0
      else
        match exponent2 with
        | .ofNat exponent =>
            descriptorPositiveRationalBits
              (mantissa * 2 ^ exponent) 1 23 127
        | .negSucc predecessor =>
            descriptorPositiveRationalBits
              mantissa (2 ^ (predecessor + 1)) 23 127
    if negative then roundedMagnitude + 2 ^ 31 else roundedMagnitude

private def descriptorBinaryBitsSyntax
    (bits fractionBits bias : Nat) : M (TSyntax `options_value) := do
  let implicitBit := 2 ^ fractionBits
  let signMask := (2 * bias + 2) * implicitBit
  let negative := bits ≥ signMask
  let magnitudeBits := bits % signMask
  let exponent := magnitudeBits / implicitBit
  let fraction := magnitudeBits % implicitBit
  if exponent == 2 * bias + 1 then
    if fraction == 0 then
      descriptorSpecialFloatSyntax negative false
    else
      descriptorSpecialFloatSyntax false true
  else if exponent == 0 then
    if fraction == 0 then
      descriptorSignedNatSyntax negative 0
    else
      descriptorBinaryFloatSyntax negative fraction
        (1 - Int.ofNat bias - Int.ofNat fractionBits)
  else
    descriptorBinaryFloatSyntax negative
      (implicitBit + fraction)
      (Int.ofNat exponent - Int.ofNat bias - Int.ofNat fractionBits)

private def optionsValueOfDescriptorNumber
    (t : FieldDescriptorProto.Type) (raw : String) :
    M (TSyntax `options_value) := do
  let some value := parseDescriptorFloat? raw
    | throw s!"{decl_name%}: invalid floating-point default value '{raw}'"
  let doubleBits := descriptorFloat64Bits value
  if t == .TYPE_FLOAT then
    descriptorBinaryBitsSyntax
      (descriptorFloat32BitsOfFloat64Bits doubleBits) 23 127
  else if t == .TYPE_DOUBLE then
    descriptorBinaryBitsSyntax doubleBits 52 1023
  else
    throw s!"{decl_name%}: internal error: non-floating field type"

/--
Compatibility entry point for callers that do not carry the descriptor field
type.  Descriptor generation itself uses the type-aware helper above so a
`float` follows C++ DescriptorPool's binary64 parse and SafeDoubleToFloat
conversion rather than being rounded directly from decimal to binary32.
-/
def optionsValueOfNumber (raw : String) : M (TSyntax `options_value) :=
  optionsValueOfDescriptorNumber .TYPE_DOUBLE raw

private def parseIntegerDefaultValue (raw : String) : M Int := do
  /-
  C++ `strto*` accepts leading ASCII whitespace but its descriptor validation
  requires the end pointer to land exactly on NUL, so trailing whitespace is
  not accepted.
  -/
  let text := raw.trimAsciiStart.toString
  let (negative, body) :=
    if text.startsWith "-" then
      (true, (text.drop 1).toString)
    else if text.startsWith "+" then
      (false, (text.drop 1).toString)
    else
      (false, text)
  if body.isEmpty then
    throw s!"{decl_name%}: invalid integer default value '{raw}'"
  let (radix, digits) :=
    if body.startsWith "0x" || body.startsWith "0X" then
      (16, (body.drop 2).toString)
    else if body.length > 1 && body.startsWith "0" then
      (8, (body.drop 1).toString)
    else
      (10, body)
  if digits.isEmpty then
    throw s!"{decl_name%}: invalid integer default value '{raw}'"
  let mut magnitude := 0
  for byte in digits.toUTF8.data do
    let digit? :=
      if radix == 16 then
        hexDigit? byte
      else if radix == 8 then
        octalDigit? byte
      else if 48 ≤ byte && byte ≤ 57 then
        some (byte.toNat - 48)
      else
        none
    let some digit := digit?
      | throw s!"{decl_name%}: invalid integer default value '{raw}'"
    if digit >= radix then
      throw s!"{decl_name%}: invalid integer default value '{raw}'"
    magnitude := magnitude * radix + digit
  let value := Int.ofNat magnitude
  return if negative then -value else value

private def integerDefaultBounds
    (t : FieldDescriptorProto.Type) : Option (Int × Int × String) :=
  let signed (bits : Nat) (name : String) :=
    let half := Int.ofNat (2 ^ (bits - 1))
    (-half, half - 1, name)
  let unsigned (bits : Nat) (name : String) :=
    (0, Int.ofNat (2 ^ bits) - 1, name)
  match t with
  | .TYPE_INT32 => some (signed 32 "int32")
  | .TYPE_SINT32 => some (signed 32 "sint32")
  | .TYPE_SFIXED32 => some (signed 32 "sfixed32")
  | .TYPE_UINT32 => some (unsigned 32 "uint32")
  | .TYPE_FIXED32 => some (unsigned 32 "fixed32")
  | .TYPE_INT64 => some (signed 64 "int64")
  | .TYPE_SINT64 => some (signed 64 "sint64")
  | .TYPE_SFIXED64 => some (signed 64 "sfixed64")
  | .TYPE_UINT64 => some (unsigned 64 "uint64")
  | .TYPE_FIXED64 => some (unsigned 64 "fixed64")
  | _ => none

private def optionsValueOfInteger
    (t : FieldDescriptorProto.Type) (raw : String) :
    M (TSyntax `options_value) := do
  let value ← parseIntegerDefaultValue raw
  let some (minValue, maxValue, typeName) := integerDefaultBounds t
    | throw s!"{decl_name%}: internal error: non-integer field type"
  if value < minValue || value > maxValue then
    throw s!"{decl_name%}: default value {value} is outside the {typeName} range [{minValue}, {maxValue}]"
  if value < 0 then
    let lit : TSyntax `num :=
      ⟨Lean.Syntax.mkNumLit (-value).toNat.repr⟩
    `(options_value| -$lit:num)
  else
    let lit : TSyntax `num :=
      ⟨Lean.Syntax.mkNumLit value.toNat.repr⟩
    `(options_value| $lit:num)

def quoteEnumValue (value : Int32) : M (TSyntax `enum_value) := do
  let value := value.toInt
  if value < 0 then
    let lit : TSyntax `num := ⟨Lean.Syntax.mkNumLit (-value).toNat.repr⟩
    `(enum_value| -$lit:num)
  else
    let lit : TSyntax `num := ⟨Lean.Syntax.mkNumLit value.toNat.repr⟩
    `(enum_value| $lit:num)

def fieldIsPackable (field : FieldDescriptorProto) : M Bool := do
  let t ← get!! field.type
  match t with
  | .«Unknown.Value» _ => throw s!"{decl_name%}: unknown field type"
  | .TYPE_STRING | .TYPE_GROUP | .TYPE_MESSAGE | .TYPE_BYTES => pure false
  | _ => pure true

private def defaultValueAsString
    (raw : Protobuf.UnvalidatedString) : M String := do
  raw.toString?.getDM
    (throw s!"{decl_name%}: non-string field default contains invalid UTF-8")

def fieldDefaultOption? (field : FieldDescriptorProto) : M (Option (TSyntax ``options_entry)) := do
  let some rawValue := field.default_value | return none
  let t ← get!! field.type
  let value ← match t with
    | .TYPE_STRING =>
        let b64 := Protobuf.Base64.encode rawValue.bytes
        let lit : TSyntax `str := ⟨Lean.Syntax.mkStrLit b64⟩
        `(options_value| $lit:str)
    | .TYPE_BYTES =>
        let rawText ← defaultValueAsString rawValue
        let bytes ← decodeBytesDefault rawText
        let b64 := Protobuf.Base64.encode bytes
        let lit : TSyntax `str := ⟨Lean.Syntax.mkStrLit b64⟩
        `(options_value| $lit:str)
    | .TYPE_BOOL =>
        let rawText ← defaultValueAsString rawValue
        match rawText with
        | "true" => `(options_value| true)
        | "false" => `(options_value| false)
        | _ => throw s!"{decl_name%}: invalid boolean default value '{rawText}'"
    | .TYPE_ENUM =>
        let rawText ← defaultValueAsString rawValue
        let name := sanitizeEnumValueName rawText.trimAscii.toString
        let id := Lean.mkIdent (Name.mkStr1 name)
        `(options_value| $id:ident)
    | .TYPE_DOUBLE
    | .TYPE_FLOAT =>
        let rawText ← defaultValueAsString rawValue
        optionsValueOfDescriptorNumber t rawText
    | .TYPE_INT64
    | .TYPE_UINT64
    | .TYPE_INT32
    | .TYPE_FIXED64
    | .TYPE_FIXED32
    | .TYPE_UINT32
    | .TYPE_SFIXED32
    | .TYPE_SFIXED64
    | .TYPE_SINT32
    | .TYPE_SINT64 =>
        optionsValueOfInteger t (← defaultValueAsString rawValue)
    | .TYPE_MESSAGE =>
        throw s!"{decl_name%}: default option is not supported for message types"
    | .TYPE_GROUP =>
        throw s!"{decl_name%}: default option is not supported for group fields"
    | .«Unknown.Value» _ =>
        throw s!"{decl_name%}: unknown field type"
  some <$> `(options_entry| default = $value)

/--
Emit the downstream initializer that registers one compact serialized
`FileDescriptorProto` in the generated pool.
-/
private partial def concatStringTerms
    (terms : Array (TSyntax `term)) : M (TSyntax `term) := do
  if terms.isEmpty then
    `("")
  else if terms.size == 1 then
    return terms[0]!
  else
    let middle := terms.size / 2
    let left ← concatStringTerms (terms.extract 0 middle)
    let right ← concatStringTerms (terms.extract middle terms.size)
    /-
    Keep the parentheses in the syntax tree.  The protobuf command's safe
    printer cannot infer that an injected application is one argument of the
    surrounding `registerFileBase64!` application, and nested applications
    otherwise render as `String.append String.append ...`.
    -/
    `((String.append $left $right))

def compileFileDescriptorRegistration (file : FileDescriptorProto) : M Command := do
  let fileName ← get!! file.name
  /-
  SourceCodeInfo is useful to a compiler plugin while generating code, but it
  is not part of the generated-runtime descriptor in the mainstream protobuf
  implementations and can dwarf the schema itself.  Keep descriptor options
  (including retained custom options), while omitting this compiler-only
  location table from every downstream module.
  -/
  let file := { file with source_code_info := none }
  let bytes ←
    (FileDescriptorProto.«protobuf.internal».encode file).mapError fun err =>
      s!"cannot serialize descriptor for `{fileName}`: {err}"
  let encoded := Protobuf.Base64.encode bytes
  let chunkTerms : Array (TSyntax `term) :=
    (chunkString 4096 encoded).map quote
  let payload ← concatStringTerms chunkTerms
  let initializer := mkIdent (fileDescriptorInitializerName fileName)
  `(private initialize $initializer : Protobuf.Reflection.FileDescriptor ←
      Protobuf.Reflection.generatedPool.registerFileBase64! $payload)

def compileMessageReflectionInstance
    (leanName : Name) (protobufFullName : String) : M Command := do
  let typeId := mkIdent leanName
  let fullName := quote protobufFullName
  let toMessagePartial :=
    mkIdent (leanName.eraseMacroScopes.str "protobuf.internal" |>.str "toMessagePartial")
  let fromMessage :=
    mkIdent (leanName.eraseMacroScopes.str "protobuf.internal" |>.str "fromMessage")
  `(instance : Protobuf.Reflection.ReflectMessage $typeId := {
      descriptor := Protobuf.Reflection.MessageDescriptor.mk
        Protobuf.Reflection.generatedPool $fullName,
      toMessagePartial := $toMessagePartial,
      fromMessage := fun wire => $fromMessage wire
    })

def compileEnumReflectionInstance
    (leanName : Name) (protobufFullName : String) : M Command := do
  let typeId := mkIdent leanName
  let fullName := quote protobufFullName
  let toInt32 :=
    mkIdent (leanName.eraseMacroScopes.str "protobuf.internal" |>.str "toInt32")
  let fromInt32 :=
    mkIdent (leanName.eraseMacroScopes.str "protobuf.internal" |>.str "fromInt32")
  `(instance : Protobuf.Reflection.ReflectEnum $typeId := {
      descriptor := Protobuf.Reflection.EnumDescriptor.mk
        Protobuf.Reflection.generatedPool $fullName,
      toInt32 := $toInt32,
      fromInt32 := $fromInt32
    })
