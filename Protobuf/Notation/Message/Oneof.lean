module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Notation.Message.Metadata
import Protobuf.Notation.Syntax

public meta section

namespace Protobuf.Notation

open Encoding Notation

open Lean Meta Elab Term Command

public def elabOneofDecCore
    (mutEnums mutOneofs messages : NameSet)
    (suppressLegacyHelpers : Bool := false) :
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
  let decoder? ← mdata.mapM fun m =>
    m.decoder??.getDM (throwError "{decl_name%}: decoder? is absent")
  let nums := mdata.map ProtoFieldMData.field_num
  let toMessageId := push_name "toMessage"
  let toMessage ← `(partial def $toMessageId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message := fun val => do
    match val with
    $[| $(mdata.map ProtoFieldMData.field_proj) x =>
      let v ← ($builders:term x)
      return Protobuf.Encoding.Message.mk #[Protobuf.Encoding.Record.mk $nums:num v]
      ]*
    )
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
  let recMsg := mkIdent `recordMsg
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
  let validatePending := mkIdent `validatePending
  let pendingField := mkIdent `pendingField
  let pendingMessage := mkIdent `pendingMessage
  let ds ← mdata.zip decoder? |>.mapM fun (x, d) => do
    let decode ←
      if x.internal_type?.isSome || x.enum_type?.isSome then
        if x.enum_type?.isSome then
          `(do
            let value? ← ($d:ident $recMsg:ident $(x.field_num):num)
            match value? with
            | Option.some v =>
                let _ ← $validatePending:ident $state:ident
                pure (((Option.some ($(x.field_proj) v), Option.none) : $stateTy))
            -- A closed-enum value outside the declared set is an unknown
            -- field and must not select or clear a oneof case.
            | Option.none => pure $state:ident)
        else
          `(do
            let Option.some v ← ($d:ident $recMsg:ident $(x.field_num):num)
              | throw (Protobuf.Encoding.ProtoError.userError "")
            let _ ← $validatePending:ident $state:ident
            pure (((Option.some ($(x.field_proj) v), Option.none) : $stateTy)))
      else
        let nestedMessages := mkIdent `nestedMessages
        let nested := mkIdent `nested
        let combined := mkIdent `combined
        let getNestedMessages ←
          if x.options.wired_as_group?.isEqSome true then
            `(Protobuf.Encoding.Message.getExpandedGroup
              $recMsg:ident $(x.field_num):num)
          else
            `(Protobuf.Encoding.Message.getExpandedMessage
              $recMsg:ident $(x.field_num):num $recursionBudget:ident)
        `(do
          let $nestedMessages:ident ←
            $getNestedMessages:term
          let Option.some $nested:ident := $nestedMessages:ident[0]?
            | throw (Protobuf.Encoding.ProtoError.userError
                "internal error: a oneof message record decoded to no payload")
          let $combined:ident ←
            match ($state:ident).2 with
            | Option.some (previousField, previous) =>
                if previousField == $(x.field_num):num then
                  pure <|
                    Protobuf.Encoding.Message.combine previous $nested:ident
                else do
                  let _ ← $validatePending:ident $state:ident
                  pure $nested:ident
            | Option.none => pure $nested:ident
          pure (((Option.none,
            Option.some ($(x.field_num):num, $combined:ident)) : $stateTy)))
    pure (x.field_num.getNat, decode)
  let pendingState ← mkIdent <$> mkFreshUserName `pendingState
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
  let validatePendingInit ← `(Parser.Term.doSeqItem|
    let $validatePending:ident :
        $stateTy → Except Protobuf.Encoding.ProtoError Unit :=
      fun $pendingState:ident =>
        match ($pendingState:ident).2 with
        | Option.none => pure ()
        | Option.some ($pendingField:ident, $pendingMessage:ident) =>
            $validatePendingBody:term)
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
  let finalize ← mkFinalize messageFields.toList
  let fromMessage?Id := push_name "fromMessage?"
  let toMessageId := push_name "toMessage"
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
      $validatePendingInit
      let $state':ident ←
        ($msg).records.foldlM
          (init := (((Option.none, Option.none) : $stateTy)))
          (fun ($state:ident : $stateTy) $recVar:ident => do
        let $recMsg:ident := Protobuf.Encoding.Message.mk #[$recVar:ident]
        match ($dispatch:term :
            Except Protobuf.Encoding.ProtoError $stateTy) with
          | .ok next => pure next
          -- A known field number with an incompatible wire type is an unknown
          -- field, not a malformed oneof.  Ignore it here so the containing
          -- message can retain the original record in Unknown.Fields.
          | .error (.invalidWireType _) => pure $state:ident
          | .error err => throw err)
      let $result:ident ←
        match ($state':ident).2 with
        | Option.none => pure ($state':ident).1
        | Option.some ($pendingField:ident, $pendingMessage:ident) =>
            $finalize:term
      if $validateRequired:ident then
        match $result:ident with
        | Option.none => pure Option.none
        | Option.some value =>
            let _ ← $toMessageId:ident value
            pure $result:ident
      else
        pure $result:ident)
  let legacyComponents := legacyOneofHelperComponents
  let alternativeNames := mdata.map fun field =>
    field.field_name.getId.eraseMacroScopes
  let aliasCollides := legacyComponents.any fun component =>
    alternativeNames.contains (Name.mkStr1 component)
  let legacyAliases : Array (Name × Name) ←
    if aliasCollides || suppressLegacyHelpers then
      pure #[]
    else
      legacyHelperAliases name legacyComponents
  let legacyAcceptsRecord :=
    mkIdentFrom name
      ((name.getId.eraseMacroScopes.append `Internal).str "acceptsRecord")
  let legacyAcceptsRecordCmd ←
    `(def $legacyAcceptsRecord:ident
        ($acceptsRecordArg : Protobuf.Encoding.Record) : Bool :=
      $acceptsRecordId:ident $acceptsRecordArg)
  return {
    decls := #[ind],
    encodingFunctions := #[toMessage],
    mergeFunctions := #[merge],
    decodingFunctions := #[acceptsRecord, fromMessage?],
    legacyAliases
    aliases := #[legacyAcceptsRecordCmd]
  }

@[scoped command_elab oneofDec]
public def elabOneofDec : CommandElab := fun stx => do
  let (name, alternatives) ← oneofAlternativesOfSyntax stx
  let r ← elabOneofDecCore {} {} {} false stx
  r.elaborate
  registerOneofAlternatives name alternatives

end Protobuf.Notation
