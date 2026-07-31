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

private partial def constructBalancedChunkDispatch
    (recVar fallback acc recursionBudget : Ident)
    (chunks : Array (Nat × Ident × Command))
    (start stop : Nat) : CommandElabM Term := do
  if start >= stop then
    `($fallback:ident ())
  else if stop - start == 1 then
    let (_, chunkId, _) := chunks[start]!
    `($chunkId:ident $fallback:ident $acc:ident $recVar:ident
        $recursionBudget:ident)
  else
    let mid := start + (stop - start) / 2
    let (leftMaxFieldNum, _, _) := chunks[mid - 1]!
    let left ←
      constructBalancedChunkDispatch recVar fallback acc recursionBudget
        chunks start mid
    let right ←
      constructBalancedChunkDispatch recVar fallback acc recursionBudget
        chunks mid stop
    `(if ($recVar:ident).fieldNum ≤ $(quote leftMaxFieldNum) then
        $left:term
      else
        $right:term)

private def decodingChunkSize : Nat := 16

/--
Decode the wire sources accumulated for singular message fields.

The outer fold keeps ordinary LEN occurrences as borrowed source intervals and
only materializes legacy groups. Streaming all occurrences into one child
accumulator preserves singular-message merge semantics and performs
required-field checks only after the complete merged child is available.
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
      let childFromSpannedChunks :=
        helperIdent fieldMData.proto_type "fromSpannedChunks"
      let childValue ← mkIdent <$> mkFreshUserName fieldMData.field_name.getId
      let childBudget ← mkIdent <$> mkFreshUserName `childBudget
      let value? ← mkIdent <$> mkFreshUserName `value?
      let nextState ← mkIdent <$> mkFreshUserName `st
      let decodeItem ← `(Parser.Term.doSeqItem|
        let $value?:ident ← do
          let chunks :=
            ($pendingAfterFold:ident)[$(quote i)]!
          if chunks.isEmpty then
            pure Option.none
          else
            let $childBudget:ident ←
              Protobuf.Encoding.descendMessageRecursion
                $recursionBudget:ident
            let $childValue:ident ←
              $childFromSpannedChunks:ident chunks
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
    (localOneofs : LocalOneofAlternatives)
    (fields : Array ProtoFieldMData) :
    CommandElabM (Ident × Ident × Array Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let recVar := mkIdent `r
  let acc := mkIdent `acc
  let state := mkIdent `st
  let seen := mkIdent `seen
  let pending := mkIdent `pendingMessages
  let oneofPending := mkIdent `pendingOneofMessages
  let state' := mkIdent `st'
  let seen' := mkIdent `seen'
  let pending' := mkIdent `pendingMessages'
  let oneofPending' := mkIdent `pendingOneofMessages'
  let recursionBudget := mkIdent `recursionBudget
  let validateRequired := mkIdent `validateRequired
  let unknownField := mkIdent `«Unknown.Fields»
  let unknownProj := mkIdentFrom name (name.getId.append unknownField.getId)
  let oneofFields := fields.filter (fun x => x.oneof_type?.isSome)
  let hasOneofs := !oneofFields.isEmpty
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
  `pendingMessages` stores their borrowed source intervals (or parsed legacy
  groups) until the fold is complete. `pendingOneofMessages` does the same for
  a currently active message-valued oneof member; scalar members live directly
  in `state`.
  Nested decoders run in partial mode; the outermost generated decoder validates
  required initialization on the final typed tree, after all parse errors have
  been observed. These arrays are generated internal accumulators, not
  reflection.
  -/
  let stateTy ←
    if hasOneofs then
      `(($name × Array Bool ×
        Array Protobuf.Encoding.SpannedMessageChunks ×
        Array
          (Option
            (Nat × Protobuf.Encoding.SpannedMessageChunks))))
    else
      `(($name × Array Bool ×
        Array Protobuf.Encoding.SpannedMessageChunks))
  let mkState : Term → Term → Term → CommandElabM Term :=
    fun st sn pd => do
      if hasOneofs then
        `((($st, $sn, $pd, $oneofPending:ident) : $stateTy))
      else
        `((($st, $sn, $pd) : $stateTy))
  let unknownState ← mkState state' seen pending
  let unknownBody ← `(do
    let $state':ident : $name := {
      $state:ident with
      $unknownField:ident := ($unknownProj:ident $state:ident).alter $(recVar).fieldNum (fun
        | Option.none =>
            Option.some #[$(recVar).value.toProtoVal]
        | Option.some vals =>
            Option.some (vals.push $(recVar).value.toProtoVal))
    }
    pure $unknownState:term)
  let branchContext : DecodeFoldContext := {
    name,
    recVar,
    state,
    seen,
    pending,
    oneofPending? := if hasOneofs then some oneofPending else none,
    state',
    seen',
    pending',
    oneofPending'? := if hasOneofs then some oneofPending' else none,
    recursionBudget,
    unknownField,
    unknownProj,
    stateTy,
    unknownBody,
    requiredStrictMeta,
    regularMessageMeta
  }
  let regularBranchCases ←
    constructRegularBranches branchContext regularFields
  let oneofBranchCases ← oneofFields.zipIdx.foldlM
    (init := (#[] : Array (Nat × Term)))
    (fun cases (field, pendingIndex) => do
      let some oneofName := field.oneof_type?
        | throwErrorAt field.field_name
            "{decl_name%}: internal error: oneof field has no oneof type"
      let alternatives? ←
        match localOneofs.find? oneofName with
        | some alternatives => pure (some alternatives)
        | none => do
            let env ← getEnv
            pure (oneofAlternativesExt.find? env oneofName)
      let some alternatives := alternatives?
        | throwErrorAt field.proto_type
            "static field metadata is unavailable for protobuf oneof `{oneofName}`; rebuild the module that declares it"
      let body ←
        constructOneofBranch branchContext field pendingIndex
      pure <| alternatives.foldl
        (init := cases)
        fun cases alternative =>
          cases.push (alternative.fieldNumber, body))
  let branchCases := regularBranchCases ++ oneofBranchCases
  let stateInit ← `(Parser.Term.doSeqItem| let $state:ident : $name := default)
  let seenInit ← `(Parser.Term.doSeqItem| let $seen:ident : Array Bool := Array.replicate $(quote requiredStrictFields.size) false)
  let pendingInit ← `(Parser.Term.doSeqItem|
    let $pending:ident :
        Array Protobuf.Encoding.SpannedMessageChunks :=
      Array.replicate $(quote regularMessageFields.size) .empty)
  let oneofPendingInits : Array DoSeqItem ←
    if hasOneofs then
      let init ← `(Parser.Term.doSeqItem|
    let $oneofPending:ident :
        Array
          (Option
            (Nat × Protobuf.Encoding.SpannedMessageChunks)) :=
          Array.replicate $(quote oneofFields.size) Option.none)
      pure #[init]
    else
      pure #[]
  let foldAcc := mkIdent `acc
  /-
  Every ordinary field and oneof alternative participates in the same
  field-number dispatch tree. A oneof hit updates its accumulator slot
  immediately: scalars obey last-one-wins, while consecutive occurrences of
  the same message member merge raw wire payloads until finalize. A wrong-wire
  record or unknown CLOSED enum value falls through to Unknown.Fields.
  -/
  let fallback ← mkIdent <$> mkFreshUserName `fallback
  let fallbackInit ← `(Parser.Term.doSeqItem|
    let $fallback:ident :
        Unit → Except Protobuf.Encoding.ProtoError $stateTy :=
      fun _ => $unknownBody:term)
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
          let chunkPendingProjection ←
            if hasOneofs then
              `(($chunkAcc:ident).2.2.1)
            else
              `(($chunkAcc:ident).2.2)
          let chunkOneofPendingBinds : Array DoSeqItem ←
            if hasOneofs then
              let bind ← `(Parser.Term.doSeqItem|
                let $oneofPending:ident :=
                  ($chunkAcc:ident).2.2.2)
              pure #[bind]
            else
              pure #[]
          let chunkCommand ← `(partial def $chunkId:ident :
              (Unit → Except Protobuf.Encoding.ProtoError $stateTy) →
              $stateTy →
              Protobuf.Encoding.SpannedRecord →
              Nat →
              Except Protobuf.Encoding.ProtoError $stateTy :=
            fun $chunkFallback:ident $chunkAcc:ident $recVar:ident
                $recursionBudget:ident => do
              let $state:ident := ($chunkAcc:ident).1
              let $seen:ident := ($chunkAcc:ident).2.1
              let $pending:ident := $chunkPendingProjection:term
              $chunkOneofPendingBinds*
              $chunkDispatch:term)
          pure (maxFieldNum, chunkId, chunkCommand)
      let dispatch ←
        constructBalancedChunkDispatch
          recVar fallback acc recursionBudget chunks 0 chunks.size
      pure (dispatch, chunks.map (fun (_, _, command) => command))
  /-
  A known field with an incompatible wire type is retained as unknown. Wrap
  the completed dispatch once instead of cloning this recovery block into
  every regular-field branch. The oneof/unknown fallback must therefore keep
  handling its own wrong-wire cases without throwing `invalidWireType`.
  -/
  let dispatchBody ←
    recoverInvalidWireType stateTy dispatchBody unknownBody
  let initialFoldState ← mkState state seen pending
  let applyPendingProjection ←
    if hasOneofs then
      `(($acc:ident).2.2.1)
    else
      `(($acc:ident).2.2)
  let applyOneofPendingBinds : Array DoSeqItem ←
    if hasOneofs then
      let bind ← `(Parser.Term.doSeqItem|
        let $oneofPending:ident := ($acc:ident).2.2.2)
      pure #[bind]
    else
      pure #[]
  let applyRecordId := push_name "applySpannedRecord"
  let applyRecord ← `(partial def $applyRecordId:ident
      ($acc : $stateTy)
      ($recVar : Protobuf.Encoding.SpannedRecord)
      ($recursionBudget : Nat) :
      Except Protobuf.Encoding.ProtoError $stateTy := do
    let $state:ident := ($acc:ident).1
    let $seen:ident := ($acc:ident).2.1
    let $pending:ident := $applyPendingProjection:term
    $applyOneofPendingBinds*
    $fallbackInit
    $dispatchBody:term)
  let cursorAcc ← mkIdent <$> mkFreshUserName `acc
  let cursor ← mkIdent <$> mkFreshUserName `cursor
  let cursorOffset ← mkIdent <$> mkFreshUserName `offset
  let nextOffset ← mkIdent <$> mkFreshUserName `offset
  let cursorRecord ← mkIdent <$> mkFreshUserName `record
  let cursorBudget ← mkIdent <$> mkFreshUserName `recursionBudget
  let foldCursorId := push_name "foldSpannedCursor"
  let foldCursor ← `(partial def $foldCursorId:ident
      ($cursorAcc : $stateTy)
      ($cursor : Protobuf.Encoding.SpannedCursor)
      ($cursorOffset : Nat)
      ($cursorBudget : Nat) :
      Except Protobuf.Encoding.ProtoError $stateTy := do
    match ←
      ($cursor:ident).nextAt
        $cursorOffset:ident $cursorBudget:ident
    with
    | .done => pure $cursorAcc:ident
    | .next $cursorRecord:ident $nextOffset:ident => do
        let $cursorAcc:ident ←
          $applyRecordId:ident $cursorAcc:ident
            $cursorRecord:ident $cursorBudget:ident
        $foldCursorId:ident $cursorAcc:ident
          $cursor:ident $nextOffset:ident $cursorBudget:ident)
  let sourceAcc ← mkIdent <$> mkFreshUserName `acc
  let sourceVar ← mkIdent <$> mkFreshUserName `source
  let sourceBudget ← mkIdent <$> mkFreshUserName `recursionBudget
  let sourceBytes ← mkIdent <$> mkFreshUserName `bytes
  let sourceStart ← mkIdent <$> mkFreshUserName `start
  let sourceStop ← mkIdent <$> mkFreshUserName `stop
  let sourceMessage ← mkIdent <$> mkFreshUserName `message
  let sourceRecord ← mkIdent <$> mkFreshUserName `record
  let sourceCursor ← mkIdent <$> mkFreshUserName `cursor
  let foldSourceId := push_name "foldSpannedSource"
  let foldSource ← `(partial def $foldSourceId:ident
      ($sourceAcc : $stateTy)
      ($sourceVar : Protobuf.Encoding.SpannedMessageSource)
      ($sourceBudget : Nat) :
      Except Protobuf.Encoding.ProtoError $stateTy := do
    match $sourceVar:ident with
    | .span $sourceBytes:ident $sourceStart:ident $sourceStop:ident => do
        let $sourceCursor:ident ←
          Protobuf.Encoding.SpannedCursor.ofSpan
            $sourceBytes:ident $sourceStart:ident $sourceStop:ident
        $foldCursorId:ident $sourceAcc:ident
          $sourceCursor:ident ($sourceCursor:ident).offset
          $sourceBudget:ident
    | .spanned $sourceMessage:ident =>
        ($sourceMessage:ident).records.foldlM
          (init := $sourceAcc:ident)
          fun $sourceAcc:ident $sourceRecord:ident =>
            $applyRecordId:ident $sourceAcc:ident
              $sourceRecord:ident $sourceBudget:ident
    | .owned $sourceMessage:ident =>
        ($sourceMessage:ident).records.foldlM
          (init := $sourceAcc:ident)
          fun $sourceAcc:ident $sourceRecord:ident =>
            $applyRecordId:ident $sourceAcc:ident
              ($sourceRecord:ident).toSpannedRecord
              $sourceBudget:ident)
  let chunksAcc ← mkIdent <$> mkFreshUserName `acc
  let chunksVar ← mkIdent <$> mkFreshUserName `chunks
  let chunksBudget ← mkIdent <$> mkFreshUserName `recursionBudget
  let chunkSource ← mkIdent <$> mkFreshUserName `source
  let chunkSources ← mkIdent <$> mkFreshUserName `sources
  let foldChunksId := push_name "foldSpannedChunks"
  let foldChunks ← `(partial def $foldChunksId:ident
      ($chunksAcc : $stateTy)
      ($chunksVar : Protobuf.Encoding.SpannedMessageChunks)
      ($chunksBudget : Nat) :
      Except Protobuf.Encoding.ProtoError $stateTy := do
    match $chunksVar:ident with
    | .empty => pure $chunksAcc:ident
    | .single $chunkSource:ident =>
        $foldSourceId:ident $chunksAcc:ident
          $chunkSource:ident $chunksBudget:ident
    | .many $chunkSources:ident => do
        let mut $chunksAcc:ident := $chunksAcc:ident
        for $chunkSource:ident in $chunkSources:ident do
          $chunksAcc:ident ←
            $foldSourceId:ident $chunksAcc:ident
              $chunkSource:ident $chunksBudget:ident
        pure $chunksAcc:ident)
  let foldBody ← `(Parser.Term.doSeqItem|
    let $foldAcc:ident : $stateTy ←
      $foldChunksId:ident $initialFoldState:term
        $msg:ident $recursionBudget:ident)
  let stateAfterFold := mkIdent `st
  let seenAfterFold := mkIdent `seen
  let pendingAfterFold := mkIdent `pendingMessages
  let oneofPendingAfterFold := mkIdent `pendingOneofMessages
  let foldStateBind ← `(Parser.Term.doSeqItem| let $stateAfterFold:ident : $name := ($foldAcc:ident).1)
  let foldSeenBind ← `(Parser.Term.doSeqItem| let $seenAfterFold:ident : Array Bool := ($foldAcc:ident).2.1)
  let pendingAfterFoldProjection ←
    if hasOneofs then
      `(($foldAcc:ident).2.2.1)
    else
      `(($foldAcc:ident).2.2)
  let foldPendingBind ← `(Parser.Term.doSeqItem|
    let $pendingAfterFold:ident :
        Array Protobuf.Encoding.SpannedMessageChunks :=
      $pendingAfterFoldProjection:term)
  let foldOneofPendingBinds : Array DoSeqItem ←
    if hasOneofs then
      let bind ← `(Parser.Term.doSeqItem|
        let $oneofPendingAfterFold:ident :
            Array
              (Option
                (Nat × Protobuf.Encoding.SpannedMessageChunks)) :=
          ($foldAcc:ident).2.2.2)
      pure #[bind]
    else
      pure #[]
  let (messageDecodes, stateAfterMessages) ←
    constructPendingMessageDecodes
      name stateAfterFold pendingAfterFold recursionBudget
        regularMessageFields
  let oneofStatePairs ← oneofFields.zipIdx.foldlM
    (init := (#[], stateAfterMessages))
    (fun (accState : Array (TSyntax ``Parser.Term.doSeqItem) × Ident)
        (x, i) => do
      let (items, currentState) := accState
      let field := x.field_name
      let finalizePending :=
        helperIdent x.proto_type "finalizePendingMessage"
      let oneofVal ← mkIdent <$> mkFreshUserName (x.field_name.getId)
      let nextState ← mkIdent <$> mkFreshUserName `st
      let item1 ← `(Parser.Term.doSeqItem|
        let $oneofVal:ident ←
          $finalizePending:ident
            (($(x.field_proj) $currentState:ident,
              ($oneofPendingAfterFold:ident)[$(quote i)]!))
            $recursionBudget:ident)
      let item2 ← `(Parser.Term.doSeqItem| let $nextState:ident : $name := { $currentState:ident with $field:ident := $oneofVal:ident })
      pure (items.push item1 |>.push item2, nextState))
  let oneofFinalizations := oneofStatePairs.1
  let finalState := oneofStatePairs.2
  let fromMessageId := push_name "fromMessage"
  let fromSpannedChunksId := push_name "fromSpannedChunks"
  let requiredValidatorId := push_name "validateRequired"
  let ret ← `(Parser.Term.doSeqItem|
    if $validateRequired:ident then
      let _ ← $requiredValidatorId:ident $finalState:ident
      pure $finalState:ident
    else
      pure $finalState:ident)
  let fromSpannedChunks ← `(partial def $fromSpannedChunksId:ident
      ($msg : Protobuf.Encoding.SpannedMessageChunks)
      ($recursionBudget : Nat :=
        Protobuf.Encoding.defaultMessageRecursionLimit)
      ($validateRequired : Bool := true) :
      Except Protobuf.Encoding.ProtoError $name := do
    $stateInit
    $seenInit
    $pendingInit
    $oneofPendingInits*
    $foldBody
    $foldStateBind
    $foldSeenBind
    $foldPendingBind
    $foldOneofPendingBinds*
    $messageDecodes*
    $oneofFinalizations*
    $ret
    )
  let ownedMessage ← mkIdent <$> mkFreshUserName `msg
  let ownedBudget ← mkIdent <$> mkFreshUserName `recursionBudget
  let ownedValidate ← mkIdent <$> mkFreshUserName `validateRequired
  let fromMessage ← `(partial def $fromMessageId:ident
      ($ownedMessage : Protobuf.Encoding.Message)
      ($ownedBudget : Nat :=
        Protobuf.Encoding.defaultMessageRecursionLimit)
      ($ownedValidate : Bool := true) :
      Except Protobuf.Encoding.ProtoError $name :=
    $fromSpannedChunksId:ident
      (Protobuf.Encoding.SpannedMessageChunks.ofMessage
        $ownedMessage:ident)
      $ownedBudget:ident $ownedValidate:ident)
  return (
    fromMessageId,
    fromSpannedChunksId,
    dispatchHelpers
      |>.push applyRecord
      |>.push foldCursor
      |>.push foldSource
      |>.push foldChunks
      |>.push fromSpannedChunks
      |>.push fromMessage
  )

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

def construct_decode
    (name : Ident) (push_name : String → Ident)
    (fromSpannedChunks : Ident) : CommandElabM (Ident × Command) := do
  let decodeId := push_name "decode"
  let s ← `(partial def $decodeId:ident : ByteArray → Except Encoding.ProtoError $name := fun bs => do
    if bs.size > 0x7fffffff then
      throw (.invalidBuffer
        "protobuf messages must be smaller than 2 GiB")
    $fromSpannedChunks:ident
      (Protobuf.Encoding.SpannedMessageChunks.ofBytes bs))
  return (decodeId, s)

end Protobuf.Notation
