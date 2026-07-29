module

public import Lean
public meta import Protobuf.Notation.Basic
public import Protobuf.Notation.Message
import Protobuf.Notation.Syntax

set_option hygiene false

public meta section

namespace Protobuf.Notation

open Lean Meta Elab Term Command

structure ExtensionTagEntry where
  extendee : Name
  fieldNumber : Nat
  fieldName : Name
deriving Inhabited

abbrev ExtensionTagState :=
  Std.HashMap (Name × Nat) Name

private def addExtensionTagEntry
    (state : ExtensionTagState) (entry : ExtensionTagEntry) :
    ExtensionTagState :=
  state.insert (entry.extendee, entry.fieldNumber) entry.fieldName

/--
Static extension-number metadata persisted through `.olean` files.

Internal notation is intentionally version-neutral and therefore has no
extension-range declarations to consult.  Tag uniqueness does not depend on
those ranges, however, and can be checked without runtime descriptors.
-/
initialize extensionTagsExt :
    SimplePersistentEnvExtension ExtensionTagEntry ExtensionTagState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addExtensionTagEntry
    addImportedFn :=
      mkStateFromImportedEntries addExtensionTagEntry {}
  }

private def prepareExtensionTagEntries
    (extendee : Ident) (fields : Array ProtoFieldMData) :
    CommandElabM (Array ExtensionTagEntry) := do
  let names ← resolveGlobalConst extendee
  unless names.length == 1 do
    throwErrorAt extendee
      "cannot uniquely resolve protobuf extension target `{extendee}`"
  let extendeeName := names[0]!
  let displayName := extendee.getId.eraseMacroScopes
  let env ← getEnv
  let some knownFields := messageFieldTagsExt.find? env extendeeName
    | throwErrorAt extendee
        "static field metadata is unavailable for protobuf message `{displayName}`; rebuild the module that declares it"
  let mut occupied := extensionTagsExt.getState env
  let mut entries := #[]
  for field in fields do
    let fieldNumber := field.field_num.getNat
    let fieldName := field.field_name.getId.eraseMacroScopes
    if let some previous :=
        knownFields.find? (fun known =>
          known.fieldNumber == fieldNumber) then
      throwErrorAt field.field_num
        "protobuf extension field number {fieldNumber} for `{displayName}` conflicts with declared field `{previous.fieldName}`"
    let key := (extendeeName, fieldNumber)
    if let some previous := occupied[key]? then
      throwErrorAt field.field_num
        "protobuf extension field number {fieldNumber} for `{displayName}` is already declared by `{previous}`"
    let entry := { extendee := extendeeName, fieldNumber, fieldName }
    occupied := addExtensionTagEntry occupied entry
    entries := entries.push entry
  return entries

private def registerExtensionTagEntries
    (entries : Array ExtensionTagEntry) : CommandElabM Unit := do
  for entry in entries do
    /-
    Two extension modules can be compiled independently and only meet when a
    third module imports both.  Persistent metadata cannot raise an error
    during environment import, so export a collision marker whose declaration
    name depends only on the public extendee and field number. Lean rejects
    importing two modules that provide the same marker.

    Private extendees cannot be referenced from another module; their
    same-module collisions are already caught by the metadata check above.
    -/
    unless isPrivateName entry.extendee do
      let markerName :=
        (entry.extendee.str "Extension.Tags.protobuf").str
          s!"{entry.fieldNumber}.protobuf"
      let markerId := mkIdent markerName
      elabCommand (← `(public def $markerId:ident : Unit := ()))
    modifyEnv fun env => extensionTagsExt.addEntry env entry

private def ensureExtendFieldSupported (x : ProtoFieldMData) : CommandElabM Unit := do
  if x.map_info?.isSome then
    throwErrorAt x.field_name "map fields are not supported in extend"
  if x.oneof_type?.isSome then
    throwErrorAt x.field_name "oneof fields are not supported in extend"
  if x.mod == .required then
    throwErrorAt x.field_name "extension fields cannot be required"

private def extensionWireFilter (x : ProtoFieldMData) (isRepeated : Bool) :
    CommandElabM Term := do
  if x.enum_type?.isSome then
    if isRepeated then
      `(fun
        | Protobuf.Encoding.ProtoVal.VARINT _
        | Protobuf.Encoding.ProtoVal.LEN _ => true
        | _ => false)
    else
      `(fun
        | Protobuf.Encoding.ProtoVal.VARINT _ => true
        | _ => false)
  else
    match x.internal_type? with
    | some .bool
    | some .int32
    | some .uint32
    | some .int64
    | some .uint64
    | some .sint32
    | some .sint64 =>
        if isRepeated then
          `(fun
            | Protobuf.Encoding.ProtoVal.VARINT _
            | Protobuf.Encoding.ProtoVal.LEN _ => true
            | _ => false)
        else
          `(fun
            | Protobuf.Encoding.ProtoVal.VARINT _ => true
            | _ => false)
    | some .double
    | some .fixed64
    | some .sfixed64 =>
        if isRepeated then
          `(fun
            | Protobuf.Encoding.ProtoVal.I64 _
            | Protobuf.Encoding.ProtoVal.LEN _ => true
            | _ => false)
        else
          `(fun
            | Protobuf.Encoding.ProtoVal.I64 _ => true
            | _ => false)
    | some .float
    | some .fixed32
    | some .sfixed32 =>
        if isRepeated then
          `(fun
            | Protobuf.Encoding.ProtoVal.I32 _
            | Protobuf.Encoding.ProtoVal.LEN _ => true
            | _ => false)
        else
          `(fun
            | Protobuf.Encoding.ProtoVal.I32 _ => true
            | _ => false)
    | some .string
    | some .raw_string
    | some .bytes
    | none =>
        if x.options.wired_as_group?.isEqSome true then
          `(fun
            | Protobuf.Encoding.ProtoVal.GROUPED _ => true
            | _ => false)
        else
          `(fun
            | Protobuf.Encoding.ProtoVal.LEN _ => true
            | _ => false)

private def extensionRetainedValues
    (x : ProtoFieldMData) (isRepeated : Bool) (wireFilter : Term) :
    CommandElabM Term := do
  let rawValues ← mkIdent <$> mkFreshUserName `rawValues
  match x.enum_type? with
  | none =>
      `(fun ($rawValues:ident : Array Protobuf.Encoding.ProtoVal) =>
        show Except Protobuf.Encoding.ProtoError
            (Array Protobuf.Encoding.ProtoVal) from
          pure
            (($rawValues:ident).filter fun value => !($wireFilter:term value)))
  | some _ =>
      let fromInt32 := helperIdent x.proto_type "fromInt32"
      let isKnown := helperIdent x.proto_type "isKnown"
      let isClosed := helperIdent x.proto_type "isClosed"
      let raw ← mkIdent <$> mkFreshUserName `raw
      let repeatedTerm := quote isRepeated
      `(fun ($rawValues:ident : Array Protobuf.Encoding.ProtoVal) =>
        Protobuf.Encoding.Message.retainEnumExtensionUnknownValues
          $rawValues:ident $repeatedTerm $isClosed:ident
          (fun $raw:ident =>
            $isKnown:ident
              ($fromInt32:ident
                (Int32.ofBitVec (UInt32.ofNat $raw:ident).toBitVec))))

private def elabExtendField (extendee : Ident) (x : ProtoFieldMData) : CommandElabM (Array Command) := do
  ensureExtendFieldSupported x
  let fieldNameStr := x.field_name.getId.toString
  let extendeeId := extendee
  let fieldNumTerm := x.field_num
  let isRepeated := x.mod == Modifier.repeated
  let leanType := x.lean_type_inner
  let builder ← x.builder?.getDM (throwErrorAt x.field_name "builder is absent for extension field")
  let decoder? ← x.decoder??.getDM (throwErrorAt x.field_name "decoder? is absent for extension field")
  let decoderRep ← x.decoder_rep?.getDM (throwErrorAt x.field_name "decoder_rep is absent for extension field")
  let valueBuilder : Term ←
    if x.options.wired_as_group?.isEqSome true then
      let toMessage ← x.toMessage?.getDM <|
        throwErrorAt x.field_name
          "group extension field has no generated toMessage function"
      `(fun value => do
        let groupMessage ← $toMessage:ident value
        Protobuf.Encoding.ProtoVal.ofGroup groupMessage)
    else
      `($builder:ident)
  let decodeRepeated : Term ←
    if x.options.wired_as_group?.isEqSome true then
      let fromMessage ← x.fromMessage?.getDM <|
        throwErrorAt x.field_name
          "group extension field has no generated fromMessage function"
      `(fun (wireMessage : Protobuf.Encoding.Message) (fieldNumber : Nat) => do
        let groupMessages ←
          Protobuf.Encoding.Message.getExpandedGroup
            wireMessage fieldNumber
        groupMessages.mapM fun groupMessage => do
          let childBudget ←
            Protobuf.Encoding.descendMessageRecursion
              Protobuf.Encoding.defaultMessageRecursionLimit
          $fromMessage:ident groupMessage childBudget)
    else
      `($decoderRep:ident)
  let decodeSingular : Term ←
    if x.options.wired_as_group?.isEqSome true then
      let fromMessage ← x.fromMessage?.getDM <|
        throwErrorAt x.field_name
          "group extension field has no generated fromMessage function"
      `(fun (wireMessage : Protobuf.Encoding.Message) (fieldNumber : Nat) => do
        let groupMessages ←
          Protobuf.Encoding.Message.getExpandedGroup
            wireMessage fieldNumber
        if let first :: rest := groupMessages.toList then
          let merged :=
            rest.foldl
              (init := first) Protobuf.Encoding.Message.combine
          let childBudget ←
            Protobuf.Encoding.descendMessageRecursion
              Protobuf.Encoding.defaultMessageRecursionLimit
          return some (← $fromMessage:ident merged childBudget)
        else
          return none)
    else
      `($decoder?:ident)
  let packed := x.options.packed?.isEqSome true
  -- `packed` controls the representation emitted by the setter only.
  -- Protobuf parsers must accept both packed and unpacked representations for
  -- every repeated packable field, including extensions.
  let unknownAccessor := mkIdentFrom extendee (extendee.getId.str "Unknown.Fields")
  let unknownFieldId := mkIdent `«Unknown.Fields»
  /-
  Extension declarations live outside the extendee, so valid schemas may use
  the same simple extension name in different packages, and the extendee may
  already have ordinary fields named `get_x`, `set_x`, or `has_x`.  The field
  number is globally unique within an extendee's extension ranges, making this
  nested path a stable collision-free API across files.

  Historical flat names are emitted below only when the extendee namespace does
  not already contain that declaration.
  -/
  let nestedComponent := s!"{fieldNameStr}_{x.field_num.getNat}"
  -- The dotted component cannot be produced by a legal protobuf identifier,
  -- so nested message/type names cannot occupy this accessor namespace.
  let nestedPrefix :=
    (extendee.getId.str "Extension.Accessors").str nestedComponent
  let getId := mkIdentFrom extendee (nestedPrefix.str "get?")
  let getValueId := mkIdentFrom extendee (nestedPrefix.str "get")
  let setId := mkIdentFrom extendee (nestedPrefix.str "set")
  let hasId := mkIdentFrom extendee (nestedPrefix.str "has")
  let flatGetId := mkIdentFrom extendee (extendee.getId.str s!"get_{fieldNameStr}?")
  let flatGetValueId := mkIdentFrom extendee (extendee.getId.str s!"get_{fieldNameStr}")
  let flatSetId := mkIdentFrom extendee (extendee.getId.str s!"set_{fieldNameStr}")
  let flatHasId := mkIdentFrom extendee (extendee.getId.str s!"has_{fieldNameStr}")
  let msg ← mkIdent <$> mkFreshUserName `msg
  let val ← mkIdent <$> mkFreshUserName `val
  let map ← mkIdent <$> mkFreshUserName `map
  let wire ← mkIdent <$> mkFreshUserName `wire
  let vals ← mkIdent <$> mkFreshUserName `vals
  let wireFilter ← extensionWireFilter x isRepeated
  let retainValues ← extensionRetainedValues x isRepeated wireFilter
  let getCmd ←
    if isRepeated then
      `(partial def $getId:ident : $extendeeId → Except Protobuf.Encoding.ProtoError (Array $leanType) := fun $msg => do
        let rawValues := (($unknownAccessor $msg)[$fieldNumTerm]?).getD #[]
        let rawValues := rawValues.filter $wireFilter:term
        let $wire:ident := Protobuf.Encoding.Message.mk <|
          rawValues.map fun value =>
            Protobuf.Encoding.Record.mk $fieldNumTerm value
        $decodeRepeated:term $wire $fieldNumTerm
        )
    else
      `(partial def $getId:ident : $extendeeId → Except Protobuf.Encoding.ProtoError (Option $leanType) := fun $msg => do
        let rawValues := (($unknownAccessor $msg)[$fieldNumTerm]?).getD #[]
        let rawValues := rawValues.filter $wireFilter:term
        let $wire:ident := Protobuf.Encoding.Message.mk <|
          rawValues.map fun value =>
            Protobuf.Encoding.Record.mk $fieldNumTerm value
        $decodeSingular:term $wire $fieldNumTerm
        )
  let getValueCmd? ←
    if isRepeated then
      pure none
    else
      let defaultValue := x.accessor_default
      some <$> `(partial def $getValueId:ident :
          $extendeeId → Except Protobuf.Encoding.ProtoError $leanType := fun $msg => do
        return (← $getId:ident $msg).getD $defaultValue)
  let setCmd ←
    if isRepeated then
      if packed then
        `(partial def $setId:ident : $extendeeId → Array $leanType → Except Protobuf.Encoding.ProtoError $extendeeId := fun $msg $vals => do
          let incompatible ←
            ($retainValues:term)
              ((($unknownAccessor $msg)[$fieldNumTerm]?).getD #[])
          let encoded ←
            if ($vals:ident).isEmpty then
              pure #[]
            else
              let $vals:ident ← Array.mapM $valueBuilder:term $vals
              let packedValue ←
                Protobuf.Encoding.ProtoVal.of_packed $vals
              pure #[packedValue]
          let combined := incompatible ++ encoded
          let $map:ident :=
            if combined.isEmpty then
              ($unknownAccessor $msg).erase $fieldNumTerm
            else
              ($unknownAccessor $msg).insert $fieldNumTerm combined
          return { $msg with $unknownFieldId:ident := $map }
          )
      else
        `(partial def $setId:ident : $extendeeId → Array $leanType → Except Protobuf.Encoding.ProtoError $extendeeId := fun $msg $vals => do
          let incompatible ←
            ($retainValues:term)
              ((($unknownAccessor $msg)[$fieldNumTerm]?).getD #[])
          let encoded ← Array.mapM $valueBuilder:term $vals
          let combined := incompatible ++ encoded
          let $map:ident :=
            if combined.isEmpty then
              ($unknownAccessor $msg).erase $fieldNumTerm
            else
              ($unknownAccessor $msg).insert $fieldNumTerm combined
          return { $msg with $unknownFieldId:ident := $map }
          )
    else
      `(partial def $setId:ident : $extendeeId → $leanType → Except Protobuf.Encoding.ProtoError $extendeeId := fun $msg $val => do
        let incompatible ←
          ($retainValues:term)
            ((($unknownAccessor $msg)[$fieldNumTerm]?).getD #[])
        let $val:ident ← $valueBuilder:term $val
        let $map:ident :=
          ($unknownAccessor $msg).insert $fieldNumTerm (incompatible.push $val)
        return { $msg with $unknownFieldId:ident := $map }
        )
  let hasCmd ←
    if isRepeated then
      `(partial def $hasId:ident : $extendeeId → Bool := fun $msg =>
        match $getId:ident $msg with
        | .ok values => !values.isEmpty
        | .error _ => false)
    else
      `(partial def $hasId:ident : $extendeeId → Bool := fun $msg =>
        match $getId:ident $msg with
        | .ok value => value.isSome
        | .error _ => false)
  let nameExists (id : Ident) : CommandElabM Bool := do
    try
      return !(← resolveGlobalConst (mkIdent id.getId.eraseMacroScopes)).isEmpty
    catch _ =>
      return false
  let flatGetExists ← nameExists flatGetId
  let flatGetValueExists ← nameExists flatGetValueId
  let flatSetExists ← nameExists flatSetId
  let flatHasExists ← nameExists flatHasId
  let mut legacy := #[]
  unless flatGetExists do
    let cmd ←
      if isRepeated then
        `(def $flatGetId:ident : $extendeeId →
            Except Protobuf.Encoding.ProtoError (Array $leanType) :=
          $getId:ident)
      else
        `(def $flatGetId:ident : $extendeeId →
            Except Protobuf.Encoding.ProtoError (Option $leanType) :=
          $getId:ident)
    legacy := legacy.push cmd
  if !isRepeated && !flatGetValueExists then
    legacy := legacy.push (←
      `(def $flatGetValueId:ident : $extendeeId →
          Except Protobuf.Encoding.ProtoError $leanType :=
        $getValueId:ident))
  unless flatSetExists do
    let cmd ←
      if isRepeated then
        `(def $flatSetId:ident : $extendeeId → Array $leanType →
            Except Protobuf.Encoding.ProtoError $extendeeId :=
          $setId:ident)
      else
        `(def $flatSetId:ident : $extendeeId → $leanType →
            Except Protobuf.Encoding.ProtoError $extendeeId :=
          $setId:ident)
    legacy := legacy.push cmd
  unless flatHasExists do
    legacy := legacy.push (←
      `(def $flatHasId:ident : $extendeeId → Bool := $hasId:ident))
  return #[getCmd] ++ getValueCmd?.toArray ++ #[setCmd, hasCmd] ++ legacy

@[scoped command_elab extendDec]
public def elabExtendDec : CommandElab := fun stx => do
  let `(extendDec| extend $extendee { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let mdata ← computeMData {} {} {} extendee mod t' n fidx optionsStx
  let tagEntries ← prepareExtensionTagEntries extendee mdata
  let cmds ← mdata.mapM (elabExtendField extendee)
  for cmd in cmds.flatten do
    elabCommand cmd
  registerExtensionTagEntries tagEntries

end Protobuf.Notation
