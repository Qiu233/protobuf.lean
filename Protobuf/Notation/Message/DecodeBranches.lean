module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Notation.Message.Metadata

public meta section

namespace Protobuf.Notation

open Encoding Notation
open Lean Meta Elab Term Command

/--
Identifiers and generated terms shared by the per-field decoder branch
builders. Keeping these builders in separate declarations avoids one enormous
meta definition whose elaboration itself exhausts Lean's default heartbeat
budget.
-/
structure DecodeFoldContext where
  name : Ident
  recVar : Ident
  recMsg : Ident
  state : Ident
  seen : Ident
  pending : Ident
  state' : Ident
  seen' : Ident
  pending' : Ident
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
  `((($state, $seen, $pending) : $(ctx.stateTy)))

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
    recMsg,
    state,
    seen := _,
    pending,
    state',
    seen',
    recursionBudget,
    unknownField := _,
    unknownProj := _,
    stateTy,
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
  let fieldNum := fieldMData.field_num
  let field := fieldMData.field_name
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
    let entries ←
      Encoding.Message.getExpandedMessage
        $recMsg:ident $fieldNum:num $recursionBudget:ident
    let $entryBudget:ident ←
      Protobuf.Encoding.descendMessageRecursion $recursionBudget:ident
    let $map:ident ←
      entries.foldlM
        (init := $(fieldMData.field_proj) $state:ident)
        (fun $map:ident $entry:ident => do
          let key? ← $keyDecoder?:ident $entry 1
          let value? ← $decodeValue:term
          let key := Option.getD key? $keyDefault
          let value ←
            match value? with
            | some value => pure value
            | none => $decodeMissingValue:term
          pure ($mapInsert:term $map key value))
    let $state':ident : $name := {
      $state:ident with
      $field:ident := $map:ident
    }
    let $seen':ident := $seenUpdate:term
    pure (($state':ident, $seen':ident, $pending:ident) : $stateTy))
  match mapInfo.value_enum_type? with
  | none => pure normalBody
  | some _ =>
    let enumFromInt32 := helperIdent mapInfo.value_proto_type "fromInt32"
    let enumIsKnown := helperIdent mapInfo.value_proto_type "isKnown"
    let enumIsClosed := helperIdent mapInfo.value_proto_type "isClosed"
    `(do
      let entries ←
        Encoding.Message.getExpandedMessage
          $recMsg:ident $fieldNum:num $recursionBudget:ident
      let _ ←
        Protobuf.Encoding.descendMessageRecursion $recursionBudget:ident
      let hasUnknownClosedValue :=
        $enumIsClosed:ident && entries.any (fun entry =>
          entry.records.any (fun record =>
            if record.fieldNum != 2 then
              false
            else
              match record.value with
              | .VARINT raw =>
                  !($enumIsKnown:ident
                    ($enumFromInt32:ident
                      (Int32.ofBitVec (UInt32.ofNat raw).toBitVec)))
              | _ => false))
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
    recMsg,
    state,
    seen := _,
    pending,
    recursionBudget,
    state',
    seen',
    unknownField,
    unknownProj,
    stateTy,
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
  let decodeRepeated ←
    if fieldMData.options.wired_as_group?.isEqSome true then
      let fromMessage ← fieldMData.fromMessage?.getDM <|
        throwErrorAt fieldMData.field_name
          "{decl_name%}: internal error: repeated group field has no generated fromMessage function"
      let groupMessage ← mkIdent <$> mkFreshUserName `groupMessage
      let childBudget ← mkIdent <$> mkFreshUserName `childBudget
      `(do
        let groupMessages ←
          Encoding.Message.getExpandedGroup
            $recMsg:ident $fieldNum:num
        groupMessages.mapM fun $groupMessage:ident => do
          let $childBudget:ident ←
            Protobuf.Encoding.descendMessageRecursion
              $recursionBudget:ident
          $fromMessage:ident $groupMessage:ident $childBudget:ident false)
    else
      let decoderRep ← fieldMData.decoder_rep?.getDM <|
        throwErrorAt fieldMData.field_name
          "{decl_name%}: internal error: repeated field has no generated decoder"
      if fieldMData.internal_type?.isNone &&
        fieldMData.enum_type?.isNone then
        `($decoderRep:ident
          $recMsg:ident $fieldNum:num $recursionBudget:ident false)
      else
        `($decoderRep:ident $recMsg:ident $fieldNum:num)
  let normalBody ← `(do
    let $xs:ident ← $decodeRepeated:term
    let $state':ident : $name := {
      $state:ident with
      $field:ident := $(fieldMData.field_proj) $state:ident ++ $xs:ident
    }
    let $seen':ident := $seenUpdate:term
    pure (($state':ident, $seen':ident, $pending:ident) : $stateTy))
  match fieldMData.enum_type? with
  | none => pure normalBody
  | some _ =>
    let enumFromInt32 := helperIdent fieldMData.proto_type "fromInt32"
    let enumIsKnown := helperIdent fieldMData.proto_type "isKnown"
    let enumIsClosed := helperIdent fieldMData.proto_type "isClosed"
    `(if !$enumIsClosed:ident then
        $normalBody:term
      else
        match ($recVar:ident).value with
        | .VARINT raw =>
            let value :=
              $enumFromInt32:ident
                (Int32.ofBitVec (UInt32.ofNat raw).toBitVec)
            if $enumIsKnown:ident value then
              let $state':ident : $name := {
                $state:ident with
                $field:ident :=
                  ($(fieldMData.field_proj) $state:ident).push value
              }
              let $seen':ident := $seenUpdate:term
              pure (($state':ident, $seen':ident, $pending:ident) : $stateTy)
            else
              $unknownBody:term
        | .LEN _ => do
            let raws ←
              Encoding.Message.getPackedVarint_uint64
                $recMsg:ident $fieldNum:num
            let mut known := #[]
            let mut unknown := #[]
            for raw in raws do
              let truncated : UInt32 := UInt32.ofNat raw.toNat
              let value :=
                $enumFromInt32:ident
                  (Int32.ofBitVec truncated.toBitVec)
              if $enumIsKnown:ident value then
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
            let $state':ident : $name := {
              $state:ident with
              $field:ident :=
                $(fieldMData.field_proj) $state:ident ++ known
              $unknownField:ident := unknownFields
            }
            let $seen':ident := $seenUpdate:term
            pure (($state':ident, $seen':ident, $pending:ident) : $stateTy)
        | _ =>
            throw (.invalidWireType
              s!"expected VARINT or LEN for repeated enum field"))

private def constructSingularScalarBranch
    (ctx : DecodeFoldContext) (fieldMData : ProtoFieldMData)
    (seenUpdate : Term) : CommandElabM Term := do
  let {
    name,
    recMsg,
    state,
    seen,
    pending,
    state',
    seen',
    stateTy,
    unknownBody,
    ..
  } := ctx
  let fieldNum := fieldMData.field_num
  let field := fieldMData.field_name
  let decoder? := fieldMData.decoder??.get!
  let value? := mkIdent `value?
  let value := mkIdent `value
  match fieldMData.mod with
  | .optional | .required =>
    let successState ← ctx.mkState state' seen pending
    match fieldMData.enum_type? with
    | none =>
      `(do
        let $value?:ident ← $decoder?:ident $recMsg:ident $fieldNum:num
        let $state':ident : $name := {
          $state:ident with
          $field:ident := $value?:ident
        }
        pure $successState:term)
    | some _ =>
      let enumIsClosed := helperIdent fieldMData.proto_type "isClosed"
      `(do
        let $value?:ident ← $decoder?:ident $recMsg:ident $fieldNum:num
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
              pure (($state:ident, $seen:ident, $pending:ident) : $stateTy))
  | .default =>
    let unchangedState ← ctx.mkState state seen pending
    let successState ← ctx.mkState state' seen' pending
    match fieldMData.enum_type? with
    | none =>
      `(do
        let $value?:ident ← $decoder?:ident $recMsg:ident $fieldNum:num
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
        let $value?:ident ← $decoder?:ident $recMsg:ident $fieldNum:num
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
    recMsg,
    state,
    seen',
    pending,
    pending',
    recursionBudget,
    ..
  } := ctx
  let fieldNum := fieldMData.field_num
  let some pendingIndex := ctx.regularMessageMeta.findSome? (fun (fieldName, i) =>
    if fieldName == fieldMData.field_name.getId then some i else none)
    | throwErrorAt fieldMData.field_name
        "{decl_name%}: internal error: singular message field has no pending slot"
  let nestedMessages := mkIdent `nestedMessages
  let nested := mkIdent `nested
  let combined := mkIdent `combined
  let updatedState ← ctx.mkState state seen' pending'
  let getNestedMessages ←
    if fieldMData.options.wired_as_group?.isEqSome true then
      `(Encoding.Message.getExpandedGroup
        $recMsg:ident $fieldNum:num)
    else
      `(Encoding.Message.getExpandedMessage
        $recMsg:ident $fieldNum:num $recursionBudget:ident)
  `(do
    let $nestedMessages:ident ← $getNestedMessages:term
    let Option.some $nested:ident := $nestedMessages:ident[0]?
      | throw (Protobuf.Encoding.ProtoError.userError
          "internal error: a message wire record decoded to no payload")
    let $combined:ident :=
      match ($pending:ident)[$(quote pendingIndex)]! with
      | Option.some previous =>
          Protobuf.Encoding.Message.combine previous $nested:ident
      | Option.none => $nested:ident
    let $pending':ident :=
      ($pending:ident).set! $(quote pendingIndex) (some $combined:ident)
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

def constructOneofDispatch
    (oneofs : List ProtoFieldMData) (recVar : Ident)
    (knownState unknownBody : Term) : CommandElabM Term := do
  match oneofs with
  | [] => pure unknownBody
  | field :: rest =>
    let fallback ←
      constructOneofDispatch rest recVar knownState unknownBody
    let acceptsRecord := helperIdent field.proto_type "acceptsRecord"
    `(if $acceptsRecord:ident $recVar:ident then
        pure $knownState:term
      else
        $fallback:term)

end Protobuf.Notation
