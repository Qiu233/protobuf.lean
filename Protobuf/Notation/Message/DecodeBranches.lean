module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Notation.Message.Metadata

public meta section

namespace Protobuf.Notation

open Encoding Notation
open Lean Meta Elab Term Command

private def InternalType.recordDecoder : InternalType → Ident
  | .string => mkIdent ``Encoding.Record.getString
  | .raw_string => mkIdent ``Encoding.Record.getUnvalidatedString
  | .bytes => mkIdent ``Encoding.Record.getBytes
  | .bool => mkIdent ``Encoding.Record.getBool
  | .int32 => mkIdent ``Encoding.Record.getVarint_int32
  | .uint32 => mkIdent ``Encoding.Record.getVarint_uint32
  | .int64 => mkIdent ``Encoding.Record.getVarint_int64
  | .uint64 => mkIdent ``Encoding.Record.getVarint_uint64
  | .sint32 => mkIdent ``Encoding.Record.getVarint_sint32
  | .sint64 => mkIdent ``Encoding.Record.getVarint_sint64
  | .double => mkIdent ``Encoding.Record.getI64_double
  | .fixed64 => mkIdent ``Encoding.Record.getI64_fixed64
  | .sfixed64 => mkIdent ``Encoding.Record.getI64_sfixed64
  | .float => mkIdent ``Encoding.Record.getI32_float
  | .fixed32 => mkIdent ``Encoding.Record.getI32_fixed32
  | .sfixed32 => mkIdent ``Encoding.Record.getI32_sfixed32

private def InternalType.recordAppender : InternalType → Ident
  | .string => mkIdent ``Encoding.Record.appendRepeatedString
  | .raw_string => mkIdent ``Encoding.Record.appendRepeatedUnvalidatedString
  | .bytes => mkIdent ``Encoding.Record.appendRepeatedBytes
  | .bool => mkIdent ``Encoding.Record.appendRepeatedBool
  | .int32 => mkIdent ``Encoding.Record.appendRepeatedVarint_int32
  | .uint32 => mkIdent ``Encoding.Record.appendRepeatedVarint_uint32
  | .int64 => mkIdent ``Encoding.Record.appendRepeatedVarint_int64
  | .uint64 => mkIdent ``Encoding.Record.appendRepeatedVarint_uint64
  | .sint32 => mkIdent ``Encoding.Record.appendRepeatedVarint_sint32
  | .sint64 => mkIdent ``Encoding.Record.appendRepeatedVarint_sint64
  | .double => mkIdent ``Encoding.Record.appendRepeatedI64_double
  | .fixed64 => mkIdent ``Encoding.Record.appendRepeatedI64_fixed64
  | .sfixed64 => mkIdent ``Encoding.Record.appendRepeatedI64_sfixed64
  | .float => mkIdent ``Encoding.Record.appendRepeatedI32_float
  | .fixed32 => mkIdent ``Encoding.Record.appendRepeatedI32_fixed32
  | .sfixed32 => mkIdent ``Encoding.Record.appendRepeatedI32_sfixed32

/--
Identifiers and generated terms shared by the per-field decoder branch
builders. Keeping these builders in separate declarations avoids one enormous
meta definition whose elaboration itself exhausts Lean's default heartbeat
budget.
-/
structure DecodeFoldContext where
  name : Ident
  recVar : Ident
  state : Ident
  seen : Ident
  pending : Ident
  oneofPending? : Option Ident
  state' : Ident
  seen' : Ident
  pending' : Ident
  oneofPending'? : Option Ident
  recursionBudget : Ident
  unknownField : Ident
  unknownProj : Ident
  stateTy : Term
  unknownBody : Term
  requiredStrictMeta : Array (Name × Nat)
  regularMessageMeta : Array (Name × Nat)

private def DecodeFoldContext.mkState
    (ctx : DecodeFoldContext) (state seen pending : Term) :
    CommandElabM Term := do
  match ctx.oneofPending? with
  | some oneofPending =>
      `((($state, $seen, $pending, $oneofPending:ident) :
        $(ctx.stateTy)))
  | none =>
      `((($state, $seen, $pending) : $(ctx.stateTy)))

private def DecodeFoldContext.mkStateWithOneof
    (ctx : DecodeFoldContext) (state seen pending oneofPending : Term) :
    CommandElabM Term := do
  if ctx.oneofPending?.isNone then
    throwError
      "{decl_name%}: internal error: oneof state requested for a message without oneofs"
  `((($state, $seen, $pending, $oneofPending) : $(ctx.stateTy)))

private def DecodeFoldContext.seenUpdate
    (ctx : DecodeFoldContext) (field : ProtoFieldMData) :
    CommandElabM Term := do
  match ctx.requiredStrictMeta.findSome? (fun (fieldName, i) =>
    if fieldName == field.field_name.getId then some i else none) with
  | some i => `(($(ctx.seen)).set! $(quote i) true)
  | none => `($(ctx.seen))

private def constructMapBranch
    (ctx : DecodeFoldContext) (fieldMData : ProtoFieldMData)
    (mapInfo : MapFieldMData) (seenUpdate : Term) :
    CommandElabM Term := do
  let {
    name,
    recVar,
    state,
    seen := _,
    pending,
    state',
    seen',
    recursionBudget,
    unknownField := _,
    unknownProj := _,
    unknownBody,
    ..
  } := ctx
  let mapInsert ←
    if mapInfo.uses_raw_map then
      ``(Std.HashMap.Raw.insert)
    else
      ``(Std.HashMap.insert)
  let keyDecoder? := mapInfo.key_decoder?
  let valueDecoder? := mapInfo.value_decoder?
  let keyDefault := mapInfo.key_default
  let valueDefault := mapInfo.value_default
  let entry := mkIdent `entry
  let entryBudget := mkIdent `entryBudget
  let map := mkIdent `map
  let field := fieldMData.field_name
  let successState ← ctx.mkState state' seen' pending
  let decodeValue ←
    if mapInfo.value_is_message then
      /-
      Parse message values without checking required initialization. Map
      entries replace by key, so the containing message validates only the
      value retained in the final map.
      -/
      `($valueDecoder?:ident $entry:ident 2 $entryBudget:ident false)
    else
      `($valueDecoder?:ident $entry:ident 2)
  let decodeMissingValue ←
    if mapInfo.value_is_message then
      let valueFromMessage :=
        helperIdent mapInfo.value_proto_type "fromMessage"
      `($valueFromMessage:ident
        Protobuf.Encoding.Message.empty $entryBudget:ident false)
    else
      `(pure $valueDefault)
  let normalBody ← `(do
    let $entry:ident ←
      Encoding.Record.getMessage $recVar:ident $recursionBudget:ident
    let $entryBudget:ident ←
      Protobuf.Encoding.descendMessageRecursion $recursionBudget:ident
    let key? ← $keyDecoder?:ident $entry:ident 1
    let value? ← $decodeValue:term
    let key := Option.getD key? $keyDefault
    let value ←
      match value? with
      | some value => pure value
      | none => $decodeMissingValue:term
    let $map:ident :=
      $mapInsert:term ($(fieldMData.field_proj) $state:ident) key value
    let $state':ident : $name := {
      $state:ident with
      $field:ident := $map:ident
    }
    let $seen':ident := $seenUpdate:term
    pure $successState:term)
  match mapInfo.value_enum_type? with
  | none => pure normalBody
  | some _ =>
    let enumFromInt32 := helperIdent mapInfo.value_proto_type "fromInt32"
    let enumIsKnown := helperIdent mapInfo.value_proto_type "isKnown"
    let enumIsClosed := helperIdent mapInfo.value_proto_type "isClosed"
    `(do
      let $entry:ident ←
        Encoding.Record.getMessage $recVar:ident $recursionBudget:ident
      let _ ←
        Protobuf.Encoding.descendMessageRecursion $recursionBudget:ident
      let hasUnknownClosedValue :=
        $enumIsClosed:ident &&
          ($entry:ident).records.any (fun record =>
            if record.fieldNum != 2 then
              false
            else
              match record.value with
              | .VARINT raw =>
                  !($enumIsKnown:ident
                    ($enumFromInt32:ident
                      (Int32.ofBitVec (UInt32.ofNat raw).toBitVec)))
              | _ => false)
      if hasUnknownClosedValue then
        $unknownBody:term
      else
        $normalBody:term)

private def constructRepeatedBranch
    (ctx : DecodeFoldContext) (fieldMData : ProtoFieldMData)
    (seenUpdate : Term) : CommandElabM Term := do
  let {
    name,
    recVar,
    state,
    seen := _,
    pending,
    recursionBudget,
    state',
    seen',
    unknownField,
    unknownProj,
    unknownBody,
    ..
  } := ctx
  let fieldNum := fieldMData.field_num
  let field := fieldMData.field_name
  /-
  Repeated scalar parsers accept both packed and unpacked wire records.
  `packed` controls serialization only.
  -/
  let xs := mkIdent `xs
  let successState ← ctx.mkState state' seen' pending
  let normalBody ←
    if fieldMData.enum_type?.isSome then
      pure unknownBody
    else match fieldMData.internal_type? with
    | some type =>
      let appender := type.recordAppender
      `(do
        let values ←
          $appender:ident $recVar:ident
            ($(fieldMData.field_proj) $state:ident)
        let $state':ident : $name := {
          $state:ident with
          $field:ident := values
        }
        let $seen':ident := $seenUpdate:term
        pure $successState:term)
    | none =>
      let decodeRepeated ←
        if fieldMData.options.wired_as_group?.isEqSome true then
          let fromMessage ← fieldMData.fromMessage?.getDM <|
            throwErrorAt fieldMData.field_name
              "{decl_name%}: internal error: repeated group field has no generated fromMessage function"
          let groupMessage ← mkIdent <$> mkFreshUserName `groupMessage
          let childBudget ← mkIdent <$> mkFreshUserName `childBudget
          `(do
            let $groupMessage:ident ←
              Encoding.Record.getGroup $recVar:ident
            let $childBudget:ident ←
              Protobuf.Encoding.descendMessageRecursion
                $recursionBudget:ident
            let value ←
              $fromMessage:ident
                $groupMessage:ident $childBudget:ident false
            pure #[value])
        else
          let fromMessage ← fieldMData.fromMessage?.getDM <|
            throwErrorAt fieldMData.field_name
              "{decl_name%}: internal error: repeated message field has no generated fromMessage function"
          let nested ← mkIdent <$> mkFreshUserName `nested
          let childBudget ← mkIdent <$> mkFreshUserName `childBudget
          `(do
            let $nested:ident ←
              Encoding.Record.getMessage
                $recVar:ident $recursionBudget:ident
            let $childBudget:ident ←
              Protobuf.Encoding.descendMessageRecursion
                $recursionBudget:ident
            let value ←
              $fromMessage:ident $nested:ident $childBudget:ident false
            pure #[value])
      `(do
        let $xs:ident ← $decodeRepeated:term
        let values :=
          ($xs:ident).foldl
            (init := ($(fieldMData.field_proj) $state:ident))
            fun values value => values.push value
        let $state':ident : $name := {
          $state:ident with
          $field:ident := values
        }
        let $seen':ident := $seenUpdate:term
        pure $successState:term)
  match fieldMData.enum_type? with
  | none => pure normalBody
  | some _ =>
    let enumFromInt32 := helperIdent fieldMData.proto_type "fromInt32"
    let enumIsKnown := helperIdent fieldMData.proto_type "isKnown"
    let enumIsClosed := helperIdent fieldMData.proto_type "isClosed"
    `(match ($recVar:ident).value with
      | .VARINT raw =>
          let value :=
            $enumFromInt32:ident
              (Int32.ofBitVec (UInt32.ofNat raw).toBitVec)
          if !$enumIsClosed:ident || $enumIsKnown:ident value then
            let $state':ident : $name := {
              $state:ident with
              $field:ident :=
                ($(fieldMData.field_proj) $state:ident).push value
            }
            let $seen':ident := $seenUpdate:term
            pure $successState:term
          else
            $unknownBody:term
      | .LEN _ => do
          let raws ←
            Encoding.Record.appendRepeatedVarint_uint64
              $recVar:ident #[]
          let mut known := #[]
          let mut unknown := #[]
          for raw in raws do
            let truncated : UInt32 := UInt32.ofNat raw.toNat
            let value :=
              $enumFromInt32:ident
                (Int32.ofBitVec truncated.toBitVec)
            if !$enumIsClosed:ident || $enumIsKnown:ident value then
              known := known.push value
            else
              -- Packed closed-enum unknowns re-emit as expanded uint32
              -- varints, matching official runtimes.
              unknown := unknown.push
                (Protobuf.Encoding.ProtoVal.VARINT truncated.toNat)
          let unknownFields :=
            if unknown.isEmpty then
              $unknownProj:ident $state:ident
            else
              ($unknownProj:ident $state:ident).alter
                $fieldNum:num (fun
                  | Option.none => Option.some unknown
                  | Option.some vals => Option.some (vals ++ unknown))
          let values :=
            known.foldl
              (init := $(fieldMData.field_proj) $state:ident)
              fun values value => values.push value
          let $state':ident : $name := {
            $state:ident with
            $field:ident := values
            $unknownField:ident := unknownFields
          }
          let $seen':ident := $seenUpdate:term
          pure $successState:term
      | _ =>
          throw (.invalidWireType
            s!"expected VARINT or LEN for repeated enum field"))

private def constructSingularScalarBranch
    (ctx : DecodeFoldContext) (fieldMData : ProtoFieldMData)
    (seenUpdate : Term) : CommandElabM Term := do
  let {
    name,
    recVar,
    state,
    seen,
    pending,
    state',
    seen',
    unknownBody,
    ..
  } := ctx
  let field := fieldMData.field_name
  let decodeValue? ←
    match fieldMData.internal_type? with
    | some type =>
        let decoder := type.recordDecoder
        `(do
          let value ← $decoder:ident $recVar:ident
          pure (some value))
    | none =>
        let enumFromInt32 := helperIdent fieldMData.proto_type "fromInt32"
        let enumIsKnown := helperIdent fieldMData.proto_type "isKnown"
        let enumIsClosed := helperIdent fieldMData.proto_type "isClosed"
        `(match ($recVar:ident).value with
          | .VARINT raw =>
              let value :=
                $enumFromInt32:ident
                  (Int32.ofBitVec (UInt32.ofNat raw).toBitVec)
              if !$enumIsClosed:ident || $enumIsKnown:ident value then
                pure (some value)
              else
                pure none
          | _ =>
              throw (.invalidWireType "expected VARINT for enum field"))
  let value? := mkIdent `value?
  let value := mkIdent `value
  match fieldMData.mod with
  | .optional | .required =>
    let unchangedState ← ctx.mkState state seen pending
    let successState ← ctx.mkState state' seen pending
    match fieldMData.enum_type? with
    | none =>
      `(do
        let $value?:ident ← $decodeValue?:term
        let $state':ident : $name := {
          $state:ident with
          $field:ident := $value?:ident
        }
        pure $successState:term)
    | some _ =>
      let enumIsClosed := helperIdent fieldMData.proto_type "isClosed"
      `(do
        let $value?:ident ← $decodeValue?:term
        match $value?:ident with
        | Option.some $value:ident =>
            let $state':ident : $name := {
              $state:ident with
              $field:ident := some $value:ident
            }
            pure $successState:term
        | Option.none =>
            if $enumIsClosed:ident then
              $unknownBody:term
            else
              pure $unchangedState:term)
  | .default =>
    let unchangedState ← ctx.mkState state seen pending
    let successState ← ctx.mkState state' seen' pending
    match fieldMData.enum_type? with
    | none =>
      `(do
        let $value?:ident ← $decodeValue?:term
        match $value?:ident with
        | Option.some $value:ident =>
            let $state':ident : $name := {
              $state:ident with
              $field:ident := $value:ident
            }
            let $seen':ident := $seenUpdate:term
            pure $successState:term
        | Option.none =>
            pure $unchangedState:term)
    | some _ =>
      let enumIsClosed := helperIdent fieldMData.proto_type "isClosed"
      `(do
        let $value?:ident ← $decodeValue?:term
        match $value?:ident with
        | Option.some $value:ident =>
            let $state':ident : $name := {
              $state:ident with
              $field:ident := $value:ident
            }
            let $seen':ident := $seenUpdate:term
            pure $successState:term
        | Option.none =>
            if $enumIsClosed:ident then
              $unknownBody:term
            else
              pure $unchangedState:term)
  | .repeated => unreachable!

private def constructSingularMessageBranch
    (ctx : DecodeFoldContext) (fieldMData : ProtoFieldMData)
    (seenUpdate : Term) : CommandElabM Term := do
  let {
    recVar,
    state,
    seen',
    pending,
    pending',
    recursionBudget,
    ..
  } := ctx
  let some pendingIndex := ctx.regularMessageMeta.findSome? (fun (fieldName, i) =>
    if fieldName == fieldMData.field_name.getId then some i else none)
    | throwErrorAt fieldMData.field_name
        "{decl_name%}: internal error: singular message field has no pending slot"
  let nested := mkIdent `nested
  let chunks := mkIdent `chunks
  let updatedState ← ctx.mkState state seen' pending'
  let getNestedMessage ←
    if fieldMData.options.wired_as_group?.isEqSome true then
      `(Encoding.Record.getGroup $recVar:ident)
    else
      `(Encoding.Record.getMessage
        $recVar:ident $recursionBudget:ident)
  `(do
    let $nested:ident ← $getNestedMessage:term
    let $chunks:ident :=
      (($pending:ident)[$(quote pendingIndex)]!).push $nested:ident
    let $pending':ident :=
      ($pending:ident).set! $(quote pendingIndex) $chunks:ident
    let $seen':ident := $seenUpdate:term
    pure $updatedState:term)

private def constructRegularBranch
    (ctx : DecodeFoldContext) (fieldMData : ProtoFieldMData) :
    CommandElabM (Nat × Term) := do
  let seenUpdate ← ctx.seenUpdate fieldMData
  let body ←
    if let some mapInfo := fieldMData.map_info? then
      constructMapBranch ctx fieldMData mapInfo seenUpdate
    else
      match fieldMData.mod with
      | .repeated =>
          constructRepeatedBranch ctx fieldMData seenUpdate
      | .default | .required | .optional =>
          if fieldMData.internal_type?.isSome ||
              fieldMData.enum_type?.isSome then
            constructSingularScalarBranch ctx fieldMData seenUpdate
          else
            constructSingularMessageBranch ctx fieldMData seenUpdate
  pure (fieldMData.field_num.getNat, body)

def constructRegularBranches
    (ctx : DecodeFoldContext) (fields : Array ProtoFieldMData) :
    CommandElabM (Array (Nat × Term)) :=
  fields.mapM (constructRegularBranch ctx)

def constructOneofBranch
    (ctx : DecodeFoldContext)
    (field : ProtoFieldMData) (pendingIndex : Nat) :
    CommandElabM Term := do
  let acceptsRecord := helperIdent field.proto_type "acceptsRecord"
  let decodeRecord := helperIdent field.proto_type "decodeRecord"
  let oneofValue ←
    mkIdent <$> mkFreshUserName field.field_name.getId
  let pendingValue ←
    mkIdent <$> mkFreshUserName `pendingOneofMessage
  let state' := ctx.state'
  let some oneofPending := ctx.oneofPending?
    | throwError
        "{decl_name%}: internal error: oneof branch has no pending state"
  let some oneofPending' := ctx.oneofPending'?
    | throwError
        "{decl_name%}: internal error: oneof branch has no updated pending state"
  let fieldName := field.field_name
  let updatedState ←
    ctx.mkStateWithOneof
      state' ctx.seen ctx.pending oneofPending'
  `(if $acceptsRecord:ident $(ctx.recVar) then do
      let ($oneofValue:ident, $pendingValue:ident) ←
        $decodeRecord:ident
          (($(field.field_proj) $(ctx.state)),
            ($oneofPending:ident)[$(quote pendingIndex)]!)
          $(ctx.recVar) $(ctx.recursionBudget)
      let $state':ident : $(ctx.name) := {
        $(ctx.state) with
        $fieldName:ident := $oneofValue:ident
      }
      let $oneofPending':ident :=
        ($oneofPending:ident).set!
          $(quote pendingIndex) $pendingValue:ident
      pure $updatedState:term
    else
      $(ctx.unknownBody))

end Protobuf.Notation
