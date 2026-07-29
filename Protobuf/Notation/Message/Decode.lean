module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Notation.Message.Metadata
public meta import Protobuf.Notation.Message.DecodeBranches
import Protobuf.Notation.Syntax

public meta section

namespace Protobuf.Notation

open Encoding Notation

open Lean Meta Elab Term Command

private def recoverInvalidWireType
    (stateTy body unknownBody : Term) : CommandElabM Term := do
  let next ← mkIdent <$> mkFreshUserName `next
  let err ← mkIdent <$> mkFreshUserName `err
  `(match ($body : Except Protobuf.Encoding.ProtoError $stateTy) with
    | .ok $next:ident => pure $next:ident
    | .error (.invalidWireType _) => $unknownBody
    | .error $err:ident => throw $err:ident)

private abbrev DoSeqItem := TSyntax ``Parser.Term.doSeqItem

/--
Build a bounded-depth field-number dispatch tree.

A source-order chain of `if ... else` terms has depth proportional to the
number of fields.  Conformance messages with more than one hundred fields made
`whnf` traverse that entire suffix for many branches.  Sorting once and
splitting around the midpoint keeps generated syntax depth logarithmic while
preserving exact field-number dispatch.
-/
private partial def constructBalancedDispatch
    (recVar fallback : Ident)
    (cases : Array (Nat × Term))
    (start stop : Nat) : CommandElabM Term := do
  if start >= stop then
    `($fallback:ident ())
  else
    let mid := start + (stop - start) / 2
    let (fieldNum, body) := cases[mid]!
    let left ← constructBalancedDispatch recVar fallback cases start mid
    let right ← constructBalancedDispatch recVar fallback cases (mid + 1) stop
    `(if ($recVar:ident).fieldNum == $(quote fieldNum) then
        $body:term
      else if ($recVar:ident).fieldNum < $(quote fieldNum) then
        $left:term
      else
        $right:term)

private def decodingChunkSize : Nat := 16

/--
Decode the raw wire messages accumulated for singular message fields.

The outer fold has already parsed every LEN payload into an untyped wire
message. Decoding the combined payload here visits each nested record once,
preserves singular-message merge semantics, and performs required-field checks
only after all occurrences have been combined.
-/
private def constructPendingMessageDecodes
    (name stateAfterFold pendingAfterFold recursionBudget : Ident)
    (regularMessageFields : Array ProtoFieldMData) :
    CommandElabM (Array DoSeqItem × Ident) := do
  regularMessageFields.zipIdx.foldlM
    (init := (#[], stateAfterFold))
    (fun (accState : Array DoSeqItem × Ident) (fieldMData, i) => do
      let (items, currentState) := accState
      let field := fieldMData.field_name
      let childFromMessage := fieldMData.fromMessage?.get!
      let childMessage ← mkIdent <$> mkFreshUserName `childMessage
      let childValue ← mkIdent <$> mkFreshUserName fieldMData.field_name.getId
      let childBudget ← mkIdent <$> mkFreshUserName `childBudget
      let value? ← mkIdent <$> mkFreshUserName `value?
      let nextState ← mkIdent <$> mkFreshUserName `st
      let decodeItem ← `(Parser.Term.doSeqItem|
        let $value?:ident ←
          match ($pendingAfterFold:ident)[$(quote i)]! with
          | Option.none => pure Option.none
          | Option.some $childMessage:ident => do
              let $childBudget:ident ←
                Protobuf.Encoding.descendMessageRecursion
                  $recursionBudget:ident
              let $childValue:ident ←
                $childFromMessage:ident $childMessage:ident
                  $childBudget:ident false
              pure (Option.some $childValue:ident))
      let updateItem ← `(Parser.Term.doSeqItem|
        let $nextState:ident : $name := {
          $currentState:ident with
          $field:ident := $value?:ident
        })
      pure (items.push decodeItem |>.push updateItem, nextState))

def construct_fromMessage
    (name : Ident)
    (push_name : String → Ident)
    (fields : Array ProtoFieldMData) :
    CommandElabM (Ident × Array Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let recVar := mkIdent `r
  let recMsg := mkIdent `recordMsg
  let acc := mkIdent `acc
  let state := mkIdent `st
  let seen := mkIdent `seen
  let pending := mkIdent `pendingMessages
  let state' := mkIdent `st'
  let seen' := mkIdent `seen'
  let pending' := mkIdent `pendingMessages'
  let recursionBudget := mkIdent `recursionBudget
  let validateRequired := mkIdent `validateRequired
  let unknownField := mkIdent `«Unknown.Fields»
  let unknownProj := mkIdentFrom name (name.getId.append unknownField.getId)
  let oneofFields := fields.filter (fun x => x.oneof_type?.isSome)
  let regularFields := fields.filter (fun x => x.oneof_type?.isNone)
  let regularMessageFields := regularFields.filter (fun x =>
    x.map_info?.isNone &&
      x.mod != .repeated &&
      x.internal_type?.isNone &&
      x.enum_type?.isNone)
  let requiredStrictFields := regularFields.filter (fun x =>
    x.mod == .required && x.lean_shape == .strict)
  let requiredStrictMeta := requiredStrictFields.zipIdx.map fun (x, i) => (x.field_name.getId, i)
  let regularMessageMeta :=
    regularMessageFields.zipIdx.map fun (x, i) => (x.field_name.getId, i)
  /-
  We decode the message in a single left-to-right pass over wire records.

  `state` stores the partially decoded Lean value. `seen` is retained for any
  future strict required representation, while current required fields all use
  `Option`.

  Singular message fields cannot be decoded occurrence-by-occurrence: protobuf
  first merges all occurrences and only then constructs the resulting child.
  `pendingMessages` stores their already parsed wire messages until the fold is
  complete. Nested decoders run in partial mode; the outermost generated
  decoder validates required initialization on the final typed tree, after all
  parse errors have been observed. This remains generated, statically typed
  code; the array is only an internal accumulator, not reflection.
  -/
  let stateTy ← `(($name × Array Bool × Array (Option Protobuf.Encoding.Message)))
  let mkState : Term → Term → Term → CommandElabM Term := fun st sn pd => do
    `((($st, $sn, $pd) : $stateTy))
  let unknownState ← mkState state' seen pending
  let unknownBody ← `(do
    let $state':ident : $name := {
      $state:ident with
      $unknownField:ident := ($unknownProj:ident $state:ident).alter $(recVar).fieldNum (fun
        | Option.none => Option.some #[$(recVar).value]
        | Option.some vals => Option.some (vals.push $(recVar).value))
    }
    pure $unknownState:term)
  let branchContext : DecodeFoldContext := {
    name,
    recVar,
    recMsg,
    state,
    seen,
    pending,
    state',
    seen',
    pending',
    recursionBudget,
    unknownField,
    unknownProj,
    stateTy,
    unknownBody,
    requiredStrictMeta,
    regularMessageMeta
  }
  let branchCases ← constructRegularBranches branchContext regularFields
  let stateInit ← `(Parser.Term.doSeqItem| let $state:ident : $name := default)
  let seenInit ← `(Parser.Term.doSeqItem| let $seen:ident : Array Bool := Array.replicate $(quote requiredStrictFields.size) false)
  let pendingInit ← `(Parser.Term.doSeqItem|
    let $pending:ident : Array (Option Protobuf.Encoding.Message) :=
      Array.replicate $(quote regularMessageFields.size) Option.none)
  let foldAcc := mkIdent `acc
  /-
  Oneofs are intentionally deferred during the main fold because their semantics
  span all members of the union ("last one wins", with same-member submessages
  merged). The message-level field has dummy number zero, so each oneof emits a
  statically generated record classifier for its real member numbers and wire
  types. Classification does not recursively decode message values; the
  whole-message oneof pass below decodes each winning or cleared message case
  once. A non-member, wrong-wire record, or unknown CLOSED enum value falls
  through to Unknown.Fields.
  -/
  let pureState ← mkState state seen pending
  let oneofDispatch ←
    constructOneofDispatch
      oneofFields.toList recVar pureState unknownBody
  let branchCases ← branchCases.mapM fun (fieldNum, body) => do
    let body ← recoverInvalidWireType stateTy body unknownBody
    pure (fieldNum, body)
  let fallback ← mkIdent <$> mkFreshUserName `fallback
  let fallbackInit ← `(Parser.Term.doSeqItem|
    let $fallback:ident :
        Unit → Except Protobuf.Encoding.ProtoError $stateTy :=
      fun _ => $oneofDispatch:term)
  let sortedCases := branchCases.qsort (fun a b => a.1 < b.1)
  let (dispatchBody, dispatchHelpers) ←
    if sortedCases.size ≤ decodingChunkSize then
      let dispatch ←
        constructBalancedDispatch
          recVar fallback sortedCases 0 sortedCases.size
      pure (dispatch, #[])
    else do
      /-
      Keep every generated decoder declaration bounded as well as its dispatch
      depth.  Each helper handles at most `decodingChunkSize` exact field
      numbers. A thunk supplied by the parent performs oneof/unknown fallback
      for gaps in a chunk's numeric range.
      -/
      let chunkCount :=
        (sortedCases.size + decodingChunkSize - 1) / decodingChunkSize
      let chunks : Array (Nat × Ident × Command) ←
        (List.range chunkCount).toArray.mapM fun i => do
          let start := i * decodingChunkSize
          let chunkCases :=
            sortedCases.extract start
              (min sortedCases.size (start + decodingChunkSize))
          let maxFieldNum := chunkCases.back!.1
          let chunkId :=
            mkIdentFrom name
              ((helperName name.getId "fromMessage").str s!"_chunk_{i}")
          let chunkFallback ← mkIdent <$> mkFreshUserName `fallback
          let chunkAcc ← mkIdent <$> mkFreshUserName `acc
          let chunkDispatch ←
            constructBalancedDispatch
              recVar chunkFallback chunkCases 0 chunkCases.size
          let chunkCommand ← `(partial def $chunkId:ident :
              (Unit → Except Protobuf.Encoding.ProtoError $stateTy) →
              $stateTy →
              Protobuf.Encoding.Record →
              Nat →
              Except Protobuf.Encoding.ProtoError $stateTy :=
            fun $chunkFallback:ident $chunkAcc:ident $recVar:ident
                $recursionBudget:ident => do
              let $state:ident := ($chunkAcc:ident).1
              let $seen:ident := ($chunkAcc:ident).2.1
              let $pending:ident := ($chunkAcc:ident).2.2
              let $recMsg:ident :=
                Protobuf.Encoding.Message.mk #[$recVar:ident]
              $chunkDispatch:term)
          pure (maxFieldNum, chunkId, chunkCommand)
      let rec constructChunkDispatch
          (chunks : List (Nat × Ident × Command)) :
          CommandElabM Term := do
        match chunks with
        | [] => `($fallback:ident ())
        | (maxFieldNum, chunkId, _) :: rest =>
            let restDispatch ← constructChunkDispatch rest
            `(if ($recVar:ident).fieldNum ≤ $(quote maxFieldNum) then
                $chunkId:ident $fallback:ident $acc:ident $recVar:ident
                  $recursionBudget:ident
              else
                $restDispatch:term)
      let dispatch ← constructChunkDispatch chunks.toList
      pure (dispatch, chunks.map (fun (_, _, command) => command))
  let foldExpr ← `((Protobuf.Encoding.Message.records $msg).foldlM
      (init := ((($state:ident, $seen:ident, $pending:ident) : $stateTy)))
      (fun ($acc:ident : $stateTy) $recVar:ident => do
        let $state:ident := ($acc:ident).1
        let $seen:ident := ($acc:ident).2.1
        let $pending:ident := ($acc:ident).2.2
        let $recMsg:ident := Protobuf.Encoding.Message.mk #[$recVar:ident]
        $fallbackInit
        $dispatchBody:term))
  let foldBody ← `(Parser.Term.doSeqItem| let $foldAcc:ident : $stateTy ← $foldExpr:term)
  let stateAfterFold := mkIdent `st
  let seenAfterFold := mkIdent `seen
  let pendingAfterFold := mkIdent `pendingMessages
  let foldStateBind ← `(Parser.Term.doSeqItem| let $stateAfterFold:ident : $name := ($foldAcc:ident).1)
  let foldSeenBind ← `(Parser.Term.doSeqItem| let $seenAfterFold:ident : Array Bool := ($foldAcc:ident).2.1)
  let foldPendingBind ← `(Parser.Term.doSeqItem|
    let $pendingAfterFold:ident : Array (Option Protobuf.Encoding.Message) :=
      ($foldAcc:ident).2.2)
  let (messageDecodes, stateAfterMessages) ←
    constructPendingMessageDecodes
      name stateAfterFold pendingAfterFold recursionBudget
        regularMessageFields
  let oneofStatePairs ← oneofFields.foldlM
    (init := (#[], stateAfterMessages))
    (fun (accState : Array (TSyntax ``Parser.Term.doSeqItem) × Ident) x => do
      let (items, currentState) := accState
      let field := x.field_name
      let fromMessage? := x.fromMessage??.get!
      let oneofVal ← mkIdent <$> mkFreshUserName (x.field_name.getId)
      let nextState ← mkIdent <$> mkFreshUserName `st
      let item1 ← `(Parser.Term.doSeqItem|
        let $oneofVal:ident ←
          $fromMessage?:ident $msg $recursionBudget:ident false)
      let item2 ← `(Parser.Term.doSeqItem| let $nextState:ident : $name := { $currentState:ident with $field:ident := $oneofVal:ident })
      pure (items.push item1 |>.push item2, nextState))
  let oneofDecodes := oneofStatePairs.1
  let finalState := oneofStatePairs.2
  let fromMessageId := push_name "fromMessage"
  let toMessageId := push_name "toMessage"
  let ret ← `(Parser.Term.doSeqItem|
    if $validateRequired:ident then
      let _ ← $toMessageId:ident $finalState:ident
      pure $finalState:ident
    else
      pure $finalState:ident)
  let fromMessage ← `(partial def $fromMessageId:ident
      ($msg : Protobuf.Encoding.Message)
      ($recursionBudget : Nat :=
        Protobuf.Encoding.defaultMessageRecursionLimit)
      ($validateRequired : Bool := true) :
      Except Protobuf.Encoding.ProtoError $name := do
    $stateInit
    $seenInit
    $pendingInit
    $foldBody
    $foldStateBind
    $foldSeenBind
    $foldPendingBind
    $messageDecodes*
    $oneofDecodes*
    $ret
    )
  return (fromMessageId, dispatchHelpers.push fromMessage)

def construct_decoder_rep (name : Ident) (push_name : String → Ident) (fromMessage : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let recursionBudget ← mkIdent <$> mkFreshUserName `recursionBudget
  let validateRequired := mkIdent `validateRequired
  let childBudget ← mkIdent <$> mkFreshUserName `childBudget
  let decoderRepId := push_name "decoder_rep"
  let decoderRep ← `(partial def $decoderRepId:ident
      ($msg : Protobuf.Encoding.Message) (field_num : Nat)
      ($recursionBudget : Nat :=
        Protobuf.Encoding.defaultMessageRecursionLimit)
      ($validateRequired : Bool := true) :
      Except Protobuf.Encoding.ProtoError (Array $name) := do
    let xs ←
      Encoding.Message.getExpandedMessage
        $msg field_num $recursionBudget:ident
    xs.mapM fun x => do
      let $childBudget:ident ←
        Protobuf.Encoding.descendMessageRecursion
          $recursionBudget:ident
      $fromMessage:ident x $childBudget:ident $validateRequired:ident
    )
  return (decoderRepId, decoderRep)

def construct_merge (name : Ident) (push_name : String → Ident) (fields : Array ProtoFieldMData) : CommandElabM (Ident × Command) := do
  let a ← mkIdent <$> mkFreshUserName `a
  let b ← mkIdent <$> mkFreshUserName `b
  let mergeBody ← fields.mapM (β := (Ident × TSyntax ``Parser.Term.doSeqItem)) fun {mod, proto_type, field_name, field_proj, internal_type?, enum_type?, oneof_type?, map_info?, test_unset, ..} => do
    let var ← mkIdent <$> mkFreshUserName (field_name.getId)
    let va ← `($field_proj $a)
    let vb ← `($field_proj $b)
    let merger := helperIdent proto_type "merge"
    if let some map_info := map_info? then
      let map_union ←
        if map_info.uses_raw_map then
          ``(Std.HashMap.Raw.union)
        else
          ``(Std.HashMap.union)
      let stx ← `(Parser.Term.doSeqItem| let $var := $map_union:term $va $vb)
      return (var, stx)
    else if oneof_type?.isSome then
      let stx ← `(Parser.Term.doSeqItem| let $var := match $va:term, $vb:term with
        | Option.some x, Option.some y => Option.some ($merger x y)
        | Option.some x, _ => Option.some x
        | _, Option.some y => Option.some y
        | _, _ => Option.none)
      return (var, stx)
    else
      let stx ← match mod with
        | .default =>
          if internal_type?.isSome || enum_type?.isSome then
            `(Parser.Term.doSeqItem| let $var := if $test_unset $vb then $va else $vb)
          else
            `(Parser.Term.doSeqItem| let $var := match $va:term, $vb:term with
              | Option.some x, Option.some y => Option.some ($merger x y)
              | Option.some x, _ => Option.some x
              | _, Option.some y => Option.some y
              | _, _ => Option.none)
        | .required =>
          if internal_type?.isSome || enum_type?.isSome then
            `(Parser.Term.doSeqItem| let $var := $vb <|> $va)
          else
            `(Parser.Term.doSeqItem| let $var := match $va:term, $vb:term with
              | Option.some x, Option.some y => Option.some ($merger x y)
              | Option.some x, _ => Option.some x
              | _, Option.some y => Option.some y
              | _, _ => Option.none)
        | .optional =>
          if internal_type?.isSome || enum_type?.isSome then
            `(Parser.Term.doSeqItem| let $var := $vb <|> $va)
          else
            `(Parser.Term.doSeqItem| let $var := match $va:term, $vb:term with
              | Option.some x, Option.some y => Option.some ($merger x y)
              | Option.some x, _ => Option.some x
              | _, Option.some y => Option.some y
              | _, _ => Option.none)
        | .repeated => `(Parser.Term.doSeqItem| let $var := $va ++ $vb) -- concatenate
      return (var, stx)
  let u := mkIdent `«Unknown.Fields»
  let mergeBody := mergeBody.push (← do
    let field_proj :=
      mkIdentFrom name (name.getId.str "Unknown.Fields")
    let va ← `($field_proj $a)
    let vb ← `($field_proj $b)
    let s ← `(Parser.Term.doSeqItem| let $u:ident := Protobuf.Encoding.merge_map $va $vb)
    pure (u, s))
  let ps := fields.map ProtoFieldMData.field_name |>.push u
  let (vs, mergeBody) := mergeBody.unzip
  let structInst ← `({ $[$ps:ident := $vs]* : $name })
  let ret ← `(Parser.Term.doSeqItem| return $structInst)
  let mergeId := push_name "merge"
  let merge ← `(partial def $mergeId:ident : $name → $name → $name := fun $a $b => Id.run do
    $mergeBody*
    $ret
    )
  return (mergeId, merge)

def construct_decoder? (name : Ident) (push_name : String → Ident) (fromMessage : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let recursionBudget ← mkIdent <$> mkFreshUserName `recursionBudget
  let validateRequired := mkIdent `validateRequired
  let childBudget ← mkIdent <$> mkFreshUserName `childBudget
  let decoder?Id := push_name "decoder?"
  let decoder? ← `(partial def $decoder?Id:ident
      ($msg : Protobuf.Encoding.Message) (field_num : Nat)
      ($recursionBudget : Nat :=
        Protobuf.Encoding.defaultMessageRecursionLimit)
      ($validateRequired : Bool := true) :
      Except Protobuf.Encoding.ProtoError (Option $name) := do
    let messages ←
      Encoding.Message.getExpandedMessage
        $msg field_num $recursionBudget:ident
    if let first :: rest := messages.toList then
      -- Singular message occurrences merge at the wire-message level. Required
      -- initialization is checked once, after the complete child is assembled.
      let merged := rest.foldl (init := first) Protobuf.Encoding.Message.combine
      let $childBudget:ident ←
        Protobuf.Encoding.descendMessageRecursion
          $recursionBudget:ident
      let value ←
        $fromMessage:ident merged $childBudget:ident
          $validateRequired:ident
      return some value
    else
      return none
    )
  return (decoder?Id, decoder?)

def construct_decode (name : Ident) (push_name : String → Ident) (fromMessage : Ident) : CommandElabM (Ident × Command) := do
  let decodeId := push_name "decode"
  let s ← `(partial def $decodeId:ident : ByteArray → Except Encoding.ProtoError $name := fun bs => do
    if bs.size > 0x7fffffff then
      throw (.invalidBuffer
        "protobuf messages must be smaller than 2 GiB")
    let msg := Binary.Get.run (Binary.getThe Encoding.Message) bs |>.toExcept
    let msg ← Encoding.protoDecodeParseResultExcept msg
    $fromMessage:ident msg)
  return (decodeId, s)

end Protobuf.Notation
