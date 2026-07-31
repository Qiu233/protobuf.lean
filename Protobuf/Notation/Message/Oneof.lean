module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Notation.Message.Metadata
public meta import Protobuf.Notation.Message.Validate
import Protobuf.Notation.Syntax

public meta section

namespace Protobuf.Notation

open Encoding Notation

open Lean Meta Elab Term Command

private def siblingHelper (id : Ident) (component : String) : Ident :=
  match id.getId with
  | .str scope _ => mkIdentFrom id (scope.str component)
  | _ => id

private def InternalType.recordDecoder : InternalType → Ident
  | .string => mkIdent ``Encoding.SpannedRecord.getString
  | .raw_string => mkIdent ``Encoding.SpannedRecord.getUnvalidatedString
  | .bytes => mkIdent ``Encoding.SpannedRecord.getBytes
  | .bool => mkIdent ``Encoding.SpannedRecord.getBool
  | .int32 => mkIdent ``Encoding.SpannedRecord.getVarint_int32
  | .uint32 => mkIdent ``Encoding.SpannedRecord.getVarint_uint32
  | .int64 => mkIdent ``Encoding.SpannedRecord.getVarint_int64
  | .uint64 => mkIdent ``Encoding.SpannedRecord.getVarint_uint64
  | .sint32 => mkIdent ``Encoding.SpannedRecord.getVarint_sint32
  | .sint64 => mkIdent ``Encoding.SpannedRecord.getVarint_sint64
  | .double => mkIdent ``Encoding.SpannedRecord.getI64_double
  | .fixed64 => mkIdent ``Encoding.SpannedRecord.getI64_fixed64
  | .sfixed64 => mkIdent ``Encoding.SpannedRecord.getI64_sfixed64
  | .float => mkIdent ``Encoding.SpannedRecord.getI32_float
  | .fixed32 => mkIdent ``Encoding.SpannedRecord.getI32_fixed32
  | .sfixed32 => mkIdent ``Encoding.SpannedRecord.getI32_sfixed32

/--
Build a bounded-depth exact field-number dispatch for generated oneof helpers.
Alternatives may use arbitrary protobuf tag numbers, so sort once and split
around the midpoint rather than emitting a source-order linear chain.
-/
private partial def constructBalancedRecordDispatch
    (record : Ident) (fallback : Term)
    (cases : Array (Nat × Term))
    (start stop : Nat) : CommandElabM Term := do
  if start >= stop then
    pure fallback
  else
    let mid := start + (stop - start) / 2
    let (fieldNum, body) := cases[mid]!
    let left ←
      constructBalancedRecordDispatch record fallback cases start mid
    let right ←
      constructBalancedRecordDispatch record fallback cases (mid + 1) stop
    `(if ($record:ident).fieldNum == $(quote fieldNum) then
        $body:term
      else if ($record:ident).fieldNum < $(quote fieldNum) then
        $left:term
      else
        $right:term)

public def elabOneofDecCore
    (mutEnums mutOneofs messages : NameSet) :
    Syntax → CommandElabM ProtobufDeclBlock := fun stx => do
  let `(oneofDec| oneof $rawName { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let name := protectGeneratedTypeName rawName
  let safeAlternativeNames := n.map protectGeneratedMemberName
  let mdata ←
    computeMData mutEnums mutOneofs messages name mod t'
      safeAlternativeNames fidx optionsStx
  mdata.forM fun x =>
    match x.mod with
    | .default => pure ()
    | _ => throwErrorAt x.field_name "Fields in oneofs must not have cardinality modifier"
  mdata.forM fun x => do
    if x.map_info?.isSome then
      throwErrorAt x.field_name "map fields cannot appear in oneofs"
    if x.options.default?.isSome then
      throwErrorAt x.field_name "oneof fields cannot declare a default value"
  let ts := mdata.map fun x => x.lean_type_inner
  let push_name (component : String) := helperIdent name component
  let ind ← `(@[proto_oneof] inductive $name where
    $[| $safeAlternativeNames:ident : $ts:term →
      $(ts.map (fun _ => name)):ident]*
    )
  let builders ← mdata.mapM fun m => do
    let builder ←
      m.builder?.getDM (throwError "{decl_name%}: builder is absent")
      -- NOTE: builder is absent when type is a oneof, while nested oneof is
      -- forbidden by protobuf.
    if m.options.wired_as_group?.isEqSome true then
      let toMessage ← m.toMessage?.getDM <|
        throwErrorAt m.field_name
          "{decl_name%}: internal error: group oneof alternative has no generated toMessage function"
      `(fun x => do
        let groupMessage ← $toMessage:ident x
        Protobuf.Encoding.ProtoVal.ofGroup groupMessage)
    else
      `($builder:ident)
  let partialBuilders ← mdata.mapM fun m => do
    let builder ←
      m.builder?.getDM (throwError "{decl_name%}: builder is absent")
    if m.options.wired_as_group?.isEqSome true then
      let toMessage ← m.toMessage?.getDM <|
        throwErrorAt m.field_name
          "{decl_name%}: internal error: group oneof alternative has no generated toMessage function"
      let partialToMessage := siblingHelper toMessage "toMessagePartial"
      `(fun x => do
        let groupMessage ← $partialToMessage:ident x
        Protobuf.Encoding.ProtoVal.ofGroup groupMessage)
    else if m.internal_type?.isNone && m.enum_type?.isNone then
      pure (siblingHelper builder "builderPartial")
    else
      `($builder:ident)
  let nums := mdata.map ProtoFieldMData.field_num
  let toMessageId := push_name "toMessage"
  let toMessage ← `(partial def $toMessageId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message := fun val => do
    match val with
    $[| $(mdata.map ProtoFieldMData.field_proj) x =>
      let v ← ($builders:term x)
      return Protobuf.Encoding.Message.mk #[Protobuf.Encoding.Record.mk $nums:num v]
      ]*
    )
  let toMessagePartialId := push_name "toMessagePartial"
  let toMessagePartial ← `(partial def $toMessagePartialId:ident :
      $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message :=
    fun val => do
      match val with
      $[| $(mdata.map ProtoFieldMData.field_proj) x =>
        let v ← ($partialBuilders:term x)
        return Protobuf.Encoding.Message.mk
          #[Protobuf.Encoding.Record.mk $nums:num v]
        ]*)
  let requiredValidator ←
    constructOneofRequiredValidator name push_name mdata
  let messageFields := mdata.filter (fun x =>
    x.internal_type?.isNone && x.enum_type?.isNone)
  let mergeAlts ← messageFields.mapM fun x => do
    let ctor := x.field_proj
    let merger := helperIdent x.proto_type "merge"
    `(Parser.Term.matchAltExpr|
      | $ctor:ident old, $ctor:ident new =>
          $ctor:ident ($merger:ident old new))
  let mergeId := push_name "merge"
  let merge ←
    if mdata.size == 1 && messageFields.size == 1 then
      /-
      The same-message case is exhaustive for a one-constructor oneof.  Adding
      the generic replacement case makes Lean reject the generated definition
      as a redundant match alternative.
      -/
      `(
        /-- Merge two values of this oneof. -/
        partial def $mergeId:ident : $name → $name → $name := fun old new =>
          match old, new with
          $mergeAlts:matchAlt*)
    else
      `(
        /--
        Merge two values of this oneof.

        A later different case replaces the earlier case. Two occurrences of
        the same message-valued case recursively merge, matching protobuf
        MergeFrom and wire parsing semantics.
        -/
        partial def $mergeId:ident : $name → $name → $name := fun old new =>
          match old, new with
          $mergeAlts:matchAlt*
          | _, new => new)
  let msg ← mkIdent <$> mkFreshUserName `msg
  let recVar := mkIdent `r
  let recursionBudget := mkIdent `recursionBudget
  let validateRequired := mkIdent `validateRequired
  let state := mkIdent `st
  let state' := mkIdent `st'
  let result := mkIdent `result
  let stateTy ← `((Option $name ×
    Option
      (Nat × Protobuf.Encoding.SpannedMessageChunks)))
  let acceptsRecordId := helperIdent name "acceptsRecord"
  let acceptsRecordArg ← mkIdent <$> mkFreshUserName `record
  let acceptsCases ← mdata.mapM fun x => do
    let acceptsValue ←
      if x.enum_type?.isSome then
        let enumFromInt32 := helperIdent x.proto_type "fromInt32"
        let enumIsKnown := helperIdent x.proto_type "isKnown"
        let enumIsClosed := helperIdent x.proto_type "isClosed"
        `(match ($acceptsRecordArg:ident).value with
          | .varint raw =>
              !$enumIsClosed:ident ||
                $enumIsKnown:ident
                  ($enumFromInt32:ident
                    (Int32.ofBitVec raw.toUInt32.toBitVec))
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
            `(match ($acceptsRecordArg:ident).value with
              | .varint _ => true
              | _ => false)
        | some .double
        | some .fixed64
        | some .sfixed64 =>
            `(match ($acceptsRecordArg:ident).value with
              | .i64 _ => true
              | _ => false)
        | some .float
        | some .fixed32
        | some .sfixed32 =>
            `(match ($acceptsRecordArg:ident).value with
              | .i32 _ => true
              | _ => false)
        | some .string
        | some .raw_string
        | some .bytes
        | none =>
          if x.options.wired_as_group?.isEqSome true then
            `(match ($acceptsRecordArg:ident).value with
              | .grouped _ => true
              | _ => false)
          else
            `(match ($acceptsRecordArg:ident).value with
              | .len .. => true
              | _ => false)
    pure (x.field_num.getNat, acceptsValue)
  let acceptsCases :=
    acceptsCases.qsort (fun a b => a.1 < b.1)
  let acceptsFallback ← `(false)
  let acceptsBody ←
    constructBalancedRecordDispatch
      acceptsRecordArg acceptsFallback acceptsCases 0 acceptsCases.size
  let acceptsRecord ← `(
    /--
    Classify a oneof wire record using only its statically generated field
    number and wire-type rules. This avoids recursively decoding a message
    member once for classification and again for its final value.
    -/
    partial def $acceptsRecordId:ident
        ($acceptsRecordArg :
          Protobuf.Encoding.SpannedRecord) : Bool :=
      $acceptsBody:term)
  let validatePendingId := push_name "validatePendingMessage"
  let pending := mkIdent `pending
  let pendingField := mkIdent `pendingField
  let pendingChunks := mkIdent `pendingChunks
  let rec mkValidatePending
      (fields : List ProtoFieldMData) : CommandElabM Term := do
    match fields with
    | [] =>
        `(throw (Protobuf.Encoding.ProtoError.userError
          "internal error: unknown pending oneof message field"))
    | x :: rest =>
      let fallback ← mkValidatePending rest
      let childFromSpannedChunks :=
        helperIdent x.proto_type "fromSpannedChunks"
      let childBudget ← mkIdent <$> mkFreshUserName `childBudget
      `(if $pendingField:ident == $(x.field_num):num then
          do
            let $childBudget:ident ←
              Protobuf.Encoding.descendMessageRecursion
                $recursionBudget:ident
            let _ ←
              $childFromSpannedChunks:ident $pendingChunks:ident
                $childBudget:ident false
            pure ()
        else
          $fallback:term)
  let validatePendingBody ← mkValidatePending messageFields.toList
  let validatePending ← `(
    /--
    Decode a displaced message-valued oneof member far enough to observe wire
    errors. Required-field initialization is deliberately deferred to the
    final selected member.
    -/
    partial def $validatePendingId:ident
        ($pending :
          Option
            (Nat × Protobuf.Encoding.SpannedMessageChunks))
        ($recursionBudget : Nat) :
      Except Protobuf.Encoding.ProtoError Unit :=
      match $pending:ident with
      | Option.none => pure ()
      | Option.some ($pendingField:ident, $pendingChunks:ident) =>
          $validatePendingBody:term)
  let ds ← mdata.mapM fun x => do
    let decode ←
      if let some internalType := x.internal_type? then
        let recordDecoder := internalType.recordDecoder
        `(do
          let value ← $recordDecoder:ident $recVar:ident
          let _ ←
            $validatePendingId:ident
              ($state:ident).2 $recursionBudget:ident
          pure (((Option.some ($(x.field_proj) value), Option.none) :
            $stateTy)))
      else if x.enum_type?.isSome then
        let enumFromInt32 := helperIdent x.proto_type "fromInt32"
        `(do
          let .varint raw := ($recVar:ident).value
            | throw (.invalidWireType "expected VARINT for oneof enum field")
          let value :=
            $enumFromInt32:ident
              (Int32.ofBitVec raw.toUInt32.toBitVec)
          let _ ←
            $validatePendingId:ident
              ($state:ident).2 $recursionBudget:ident
          pure (((Option.some ($(x.field_proj) value), Option.none) :
            $stateTy)))
      else
        let nested := mkIdent `nested
        let source ← mkIdent <$> mkFreshUserName `source
        let start ← mkIdent <$> mkFreshUserName `start
        let stop ← mkIdent <$> mkFreshUserName `stop
        let chunks := mkIdent `chunks
        let getNested ←
          if x.options.wired_as_group?.isEqSome true then
            `(match ($recVar:ident).value with
              | .grouped $nested:ident =>
                  pure
                    (Protobuf.Encoding.SpannedMessageSource.spanned
                      $nested:ident)
              | _ => throw (.invalidWireType "expected GROUPED"))
          else
            `(match ($recVar:ident).value with
              | .len $source:ident $start:ident $stop:ident =>
                  pure
                    (Protobuf.Encoding.SpannedMessageSource.span
                      $source:ident $start:ident $stop:ident)
              | _ => throw (.invalidWireType "expected LEN"))
        `(do
          let $nested:ident ← $getNested:term
          let $chunks:ident ←
            match ($state:ident).2 with
            | Option.some (previousField, previous) =>
                if previousField == $(x.field_num):num then
                  pure (previous.push $nested:ident)
                else do
                  let _ ←
                    $validatePendingId:ident
                      ($state:ident).2 $recursionBudget:ident
                  pure (.single $nested:ident)
            | Option.none => pure (.single $nested:ident)
          pure (((Option.none,
            Option.some ($(x.field_num):num, $chunks:ident)) : $stateTy)))
    pure (x.field_num.getNat, decode)
  let ds := ds.qsort (fun a b => a.1 < b.1)
  let dispatchFallback ← `(pure $state:ident)
  let dispatch ←
    constructBalancedRecordDispatch
      recVar dispatchFallback ds 0 ds.size
  let decodeRecordId := push_name "decodeRecord"
  let decodeRecord ← `(
    /--
    Apply one wire record to a oneof accumulator.

    Incompatible wire types and undeclared values of closed enums are ignored
    here so the containing message decoder can retain them as unknown fields.
    -/
    partial def $decodeRecordId:ident
        ($state : $stateTy)
        ($recVar : Protobuf.Encoding.SpannedRecord)
        ($recursionBudget : Nat) :
      Except Protobuf.Encoding.ProtoError $stateTy := do
      if $acceptsRecordId:ident $recVar:ident then
        $dispatch:term
      else
        pure $state:ident)
  let rec mkFinalize (fields : List ProtoFieldMData) : CommandElabM Term := do
    match fields with
    | [] =>
        `(throw (Protobuf.Encoding.ProtoError.userError
          "internal error: unknown pending oneof message field"))
    | x :: rest =>
      let fallback ← mkFinalize rest
      let childFromSpannedChunks :=
        helperIdent x.proto_type "fromSpannedChunks"
      let childBudget ← mkIdent <$> mkFreshUserName `childBudget
      `(if $pendingField:ident == $(x.field_num):num then
          do
            let $childBudget:ident ←
              Protobuf.Encoding.descendMessageRecursion
                $recursionBudget:ident
            let value ←
              $childFromSpannedChunks:ident $pendingChunks:ident
                $childBudget:ident false
            pure (Option.some ($(x.field_proj) value))
        else
          $fallback:term)
  let finalizeBody ← mkFinalize messageFields.toList
  let finalizePendingId := push_name "finalizePendingMessage"
  let finalizePending ← `(
    /-- Decode the final pending message-valued member of a oneof, if any. -/
    partial def $finalizePendingId:ident
        ($state : $stateTy)
        ($recursionBudget : Nat) :
      Except Protobuf.Encoding.ProtoError (Option $name) :=
      match ($state:ident).2 with
      | Option.none => pure ($state:ident).1
      | Option.some ($pendingField:ident, $pendingChunks:ident) =>
          $finalizeBody:term)
  let fromMessage?Id := push_name "fromMessage?"
  let requiredValidatorId := push_name "validateRequired"
  let fromMessage? ← `(
    /--
    Decode a standalone oneof payload using protobuf's wire-level "last one wins" rule.

    Parsing respects wire order. Same-case message occurrences are accumulated
    as raw wire messages. A message case is decoded once when a later different
    case clears it, or once at the end when it wins. Nested message values are
    parsed without required initialization checks. Only the final selected
    value is initialized after every parse error has been observed.
    -/
    partial def $fromMessage?Id:ident
        ($msg : Protobuf.Encoding.Message)
        ($recursionBudget : Nat :=
          Protobuf.Encoding.defaultMessageRecursionLimit)
        ($validateRequired : Bool := true) :
      Except Protobuf.Encoding.ProtoError (Option $name) := do
      let $state':ident ←
        (Protobuf.Encoding.SpannedMessageChunks.ofMessage
          $msg:ident).foldlM
          (((Option.none, Option.none) : $stateTy))
          (fun ($state:ident : $stateTy) $recVar:ident =>
            $decodeRecordId:ident
              $state:ident $recVar:ident $recursionBudget:ident)
          $recursionBudget:ident
      let $result:ident ←
        $finalizePendingId:ident
          $state':ident $recursionBudget:ident
      if $validateRequired:ident then
        match $result:ident with
        | Option.none => pure Option.none
        | Option.some value =>
            let _ ← $requiredValidatorId:ident value
            pure $result:ident
      else
        pure $result:ident)
  return {
    decls := #[ind],
    encodingFunctions := #[toMessage, toMessagePartial],
    mergeFunctions := #[merge],
    validationFunctions := #[requiredValidator],
    decodingFunctions := #[
      acceptsRecord,
      validatePending,
      decodeRecord,
      finalizePending,
      fromMessage?
    ]
  }

@[scoped command_elab oneofDec]
public def elabOneofDec : CommandElab := fun stx => do
  let (name, alternatives) ← oneofAlternativesOfSyntax stx
  let r ← elabOneofDecCore {} {} {} stx
  r.elaborate
  registerOneofAlternatives name alternatives

end Protobuf.Notation
