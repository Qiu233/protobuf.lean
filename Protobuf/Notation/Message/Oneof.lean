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
  let stateTy ← `((Option $name × Option (Nat × Protobuf.Encoding.Message)))
  let acceptsRecordId := helperIdent name "acceptsRecord"
  let acceptsRecordArg ← mkIdent <$> mkFreshUserName `record
  let acceptsCases ← mdata.mapM fun x => do
    let acceptsValue ←
      if x.enum_type?.isSome then
        let enumFromInt32 := helperIdent x.proto_type "fromInt32"
        let enumIsKnown := helperIdent x.proto_type "isKnown"
        let enumIsClosed := helperIdent x.proto_type "isClosed"
        `(match ($acceptsRecordArg:ident).value with
          | .VARINT raw =>
              !$enumIsClosed:ident ||
                $enumIsKnown:ident
                  ($enumFromInt32:ident
                    (Int32.ofBitVec (UInt32.ofNat raw).toBitVec))
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
              | .VARINT _ => true
              | _ => false)
        | some .double
        | some .fixed64
        | some .sfixed64 =>
            `(match ($acceptsRecordArg:ident).value with
              | .I64 _ => true
              | _ => false)
        | some .float
        | some .fixed32
        | some .sfixed32 =>
            `(match ($acceptsRecordArg:ident).value with
              | .I32 _ => true
              | _ => false)
        | some .string
        | some .raw_string
        | some .bytes
        | none =>
          if x.options.wired_as_group?.isEqSome true then
            `(match ($acceptsRecordArg:ident).value with
              | .GROUPED _ => true
              | _ => false)
          else
            `(match ($acceptsRecordArg:ident).value with
              | .LEN _ => true
              | _ => false)
    pure (x.field_num.getNat, acceptsValue)
  let rec mkAcceptsDispatch
      (cases : List (Nat × Term)) : CommandElabM Term := do
    match cases with
    | [] => `(false)
    | (fieldNum, acceptsValue) :: rest =>
      let fallback ← mkAcceptsDispatch rest
      `(if ($acceptsRecordArg:ident).fieldNum == $(quote fieldNum) then
          $acceptsValue:term
        else
          $fallback:term)
  let acceptsBody ← mkAcceptsDispatch acceptsCases.toList
  let acceptsRecord ← `(
    /--
    Classify a oneof wire record using only its statically generated field
    number and wire-type rules. This avoids recursively decoding a message
    member once for classification and again for its final value.
    -/
    partial def $acceptsRecordId:ident
        ($acceptsRecordArg : Protobuf.Encoding.Record) : Bool :=
      $acceptsBody:term)
  let validatePendingId := push_name "validatePendingMessage"
  let pending := mkIdent `pending
  let pendingField := mkIdent `pendingField
  let pendingMessage := mkIdent `pendingMessage
  let rec mkValidatePending
      (fields : List ProtoFieldMData) : CommandElabM Term := do
    match fields with
    | [] =>
        `(throw (Protobuf.Encoding.ProtoError.userError
          "internal error: unknown pending oneof message field"))
    | x :: rest =>
      let fallback ← mkValidatePending rest
      let childFromMessage := x.fromMessage?.get!
      let childBudget ← mkIdent <$> mkFreshUserName `childBudget
      `(if $pendingField:ident == $(x.field_num):num then
          do
            let $childBudget:ident ←
              Protobuf.Encoding.descendMessageRecursion
                $recursionBudget:ident
            let _ ←
              $childFromMessage:ident $pendingMessage:ident
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
          Option (Nat × Protobuf.Encoding.Message))
        ($recursionBudget : Nat) :
      Except Protobuf.Encoding.ProtoError Unit :=
      match $pending:ident with
      | Option.none => pure ()
      | Option.some ($pendingField:ident, $pendingMessage:ident) =>
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
          let .VARINT raw := ($recVar:ident).value
            | throw (.invalidWireType "expected VARINT for oneof enum field")
          let value :=
            $enumFromInt32:ident
              (Int32.ofBitVec (UInt32.ofNat raw).toBitVec)
          let _ ←
            $validatePendingId:ident
              ($state:ident).2 $recursionBudget:ident
          pure (((Option.some ($(x.field_proj) value), Option.none) :
            $stateTy)))
      else
        let nested := mkIdent `nested
        let combined := mkIdent `combined
        let getNested ←
          if x.options.wired_as_group?.isEqSome true then
            `(Protobuf.Encoding.Record.getGroup $recVar:ident)
          else
            `(Protobuf.Encoding.Record.getMessage
              $recVar:ident $recursionBudget:ident)
        `(do
          let $nested:ident ← $getNested:term
          let $combined:ident ←
            match ($state:ident).2 with
            | Option.some (previousField, previous) =>
                if previousField == $(x.field_num):num then
                  pure <|
                    Protobuf.Encoding.Message.combine previous $nested:ident
                else do
                  let _ ←
                    $validatePendingId:ident
                      ($state:ident).2 $recursionBudget:ident
                  pure $nested:ident
            | Option.none => pure $nested:ident
          pure (((Option.none,
            Option.some ($(x.field_num):num, $combined:ident)) : $stateTy)))
    pure (x.field_num.getNat, decode)
  let rec mkDispatch (cases : List (Nat × Term)) : CommandElabM Term := do
    match cases with
    | [] => `(pure $state:ident)
    | (fieldNum, body) :: rest =>
      let restTerm ← mkDispatch rest
      `(if ($recVar:ident).fieldNum == $(quote fieldNum) then
          $body:term
        else
          $restTerm:term)
  let dispatch ← mkDispatch ds.toList
  let decodeRecordId := push_name "decodeRecord"
  let decodeRecord ← `(
    /--
    Apply one wire record to a oneof accumulator.

    Incompatible wire types and undeclared values of closed enums are ignored
    here so the containing message decoder can retain them as unknown fields.
    -/
    partial def $decodeRecordId:ident
        ($state : $stateTy)
        ($recVar : Protobuf.Encoding.Record)
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
      let childFromMessage := x.fromMessage?.get!
      let childBudget ← mkIdent <$> mkFreshUserName `childBudget
      `(if $pendingField:ident == $(x.field_num):num then
          do
            let $childBudget:ident ←
              Protobuf.Encoding.descendMessageRecursion
                $recursionBudget:ident
            let value ←
              $childFromMessage:ident $pendingMessage:ident
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
      | Option.some ($pendingField:ident, $pendingMessage:ident) =>
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
        ($msg).records.foldlM
          (init := (((Option.none, Option.none) : $stateTy)))
          (fun ($state:ident : $stateTy) $recVar:ident =>
            $decodeRecordId:ident
              $state:ident $recVar:ident $recursionBudget:ident)
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
