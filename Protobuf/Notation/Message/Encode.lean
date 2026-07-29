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

private def construct_toMessageBody
    (val msg : Ident)
    (fields : Array ProtoFieldMData) :
    CommandElabM (Array (TSyntax ``Parser.Term.doSeqItem)) := do
  fields.mapM fun {mod, field_name, field_proj, field_num, options, internal_type?, builder?, enum_type?, oneof_type?, toMessage?, test_unset, map_info?, ..} => do
    if let some map_info := map_info? then
      let entries ← mkIdent <$> mkFreshUserName `entries
      let submsg ← mkIdent <$> mkFreshUserName `submsg
      let entry_key := mkIdent `entry_key
      let entry_val := mkIdent `entry_val
      let key_builder := map_info.key_builder
      let value_builder := map_info.value_builder
      `(Parser.Term.doSeqItem|
        let $msg:ident ← do
          if $test_unset ($field_proj $val) then
            pure $msg
          else
            let $entries:ident ← ($field_proj $val).toArray.mapM (fun ($entry_key:ident, $entry_val:ident) => do
              let $submsg:ident := Protobuf.Encoding.Message.emptyWithCapacity 2
              let $submsg:ident ← (1 : Nat) <~ ($key_builder $entry_key) # $submsg
              let $submsg:ident ← (2 : Nat) <~ ($value_builder $entry_val) # $submsg
              Encoding.ProtoVal.ofMessage $submsg
              )
            $field_num:num <~f (pure $entries) # $msg
        )
    else if oneof_type?.isSome then
      let toMessage ← toMessage?.getDM <|
        throwErrorAt field_name
          "{decl_name%}: internal error: oneof field has no generated toMessage function"
      `(Parser.Term.doSeqItem|
        let $msg:ident ← (do
          let sub? ← (Option.mapM $toMessage:ident ($field_proj $val))
          let combined := Option.getD (Option.map (fun sub => Protobuf.Encoding.Message.combine $msg sub) sub?) $msg
          pure combined)
      )
    else
      let builder ← builder?.getDM <|
        throwErrorAt field_name
          "{decl_name%}: internal error: ordinary field has no generated wire builder"
      let fieldBuilder : Term ←
        if options.wired_as_group?.isEqSome true then
          let toMessage ← toMessage?.getDM <|
            throwErrorAt field_name
              "{decl_name%}: internal error: group field has no generated toMessage function"
          `(fun x => do
            let groupMessage ← $toMessage:ident x
            Protobuf.Encoding.ProtoVal.ofGroup groupMessage)
        else
          `($builder:ident)
      match mod with
      | .default =>
        if internal_type?.isSome || enum_type?.isSome then
          `(Parser.Term.doSeqItem| let $msg ← do
            if $test_unset ($field_proj $val) then
              pure $msg
            else
              $field_num:num <~ ($fieldBuilder:term ($field_proj $val)) # $msg)
        else
          `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~? (Option.mapM $fieldBuilder:term ($field_proj $val)) # $msg)
      | .required =>
        `(Parser.Term.doSeqItem|
          let $msg ← do
            if let Option.some v := ($field_proj $val) then
              $field_num:num <~ ($fieldBuilder:term v) # $msg
            else
              throw (Protobuf.Encoding.ProtoError.missingRequiredField s!"required field `{$(quote field_proj.getId.toString)}` is missing when building the message")
            )
      | .optional =>
        `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~? (Option.mapM $fieldBuilder:term ($field_proj $val)) # $msg)
      | .repeated =>
        if options.packed?.isEqSome true then
          `(Parser.Term.doSeqItem|
            let $msg ← do
              if $test_unset ($field_proj $val) then
                pure $msg
              else
                $field_num:num <~p (Array.mapM $fieldBuilder:term ($field_proj $val)) # $msg)
        else
          `(Parser.Term.doSeqItem|
            let $msg ← do
              if $test_unset ($field_proj $val) then
                pure $msg
              else
                $field_num:num <~f (Array.mapM $fieldBuilder:term ($field_proj $val)) # $msg)
private def encodingChunkSize : Nat := 16

/--
Generate the statically typed encoder core.

Wide protobuf messages used to become one deeply nested `do` term.  Lean's
elaborator and compiler then repeatedly traversed the whole prefix while
checking each later field.  For wide messages, generate bounded helper
functions instead.  They remain in the recursive encoder SCC, so recursive
message fields retain direct static calls and require no descriptor
interpreter.
-/
def construct_toMessage
    (name : Ident)
    (push_name : String → Ident)
    (fields : Array ProtoFieldMData) :
    CommandElabM (Ident × Array Command) := do
  let toMessageId := push_name "toMessage"
  if fields.size ≤ encodingChunkSize then
    let msg ← mkIdent <$> mkFreshUserName `msg
    let val ← mkIdent <$> mkFreshUserName `val
    let body ← construct_toMessageBody val msg fields
    let toMessage ← `(partial def $toMessageId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message := fun $val => do
      let $msg:ident := Protobuf.Encoding.Message.emptyWithCapacity $(quote fields.size)
      $body*
      let $msg := Protobuf.Encoding.Message.wire_map $msg
        ($(mkIdentFrom name (name.getId.str "Unknown.Fields")) $val)
      return $msg
      )
    return (toMessageId, #[toMessage])

  let chunkCount := (fields.size + encodingChunkSize - 1) / encodingChunkSize
  let chunks ← (List.range chunkCount).toArray.mapM fun i => do
    let start := i * encodingChunkSize
    let chunkFields := fields.extract start (min fields.size (start + encodingChunkSize))
    let chunkId :=
      mkIdentFrom name
        ((helperName name.getId "toMessage").str s!"_chunk_{i}")
    let msg ← mkIdent <$> mkFreshUserName `msg
    let val ← mkIdent <$> mkFreshUserName `val
    let body ← construct_toMessageBody val msg chunkFields
    let command ← `(partial def $chunkId:ident :
        $name → Protobuf.Encoding.Message →
          Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message :=
      fun $val $msg => do
        $body*
        return $msg)
    pure (chunkId, command)

  let msg ← mkIdent <$> mkFreshUserName `msg
  let val ← mkIdent <$> mkFreshUserName `val
  let calls ← chunks.mapM fun (chunkId, _) =>
    `(Parser.Term.doSeqItem|
      let $msg:ident ← $chunkId:ident $val $msg)
  let toMessage ← `(partial def $toMessageId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message := fun $val => do
    let $msg:ident := Protobuf.Encoding.Message.emptyWithCapacity $(quote fields.size)
    $calls*
    let $msg := Protobuf.Encoding.Message.wire_map $msg
      ($(mkIdentFrom name (name.getId.str "Unknown.Fields")) $val)
    return $msg
    )
  return (toMessageId, chunks.map Prod.snd |>.push toMessage)

def construct_builder (name : Ident) (push_name : String → Ident) (toMessage : Ident) : CommandElabM (Ident × Command) := do
  let val ← mkIdent <$> mkFreshUserName `val
  let builderId := push_name "builder"
  let builder ← `(partial def $builderId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.ProtoVal := fun $val => do
    let m ← $toMessage:ident $val
    Encoding.ProtoVal.ofMessage m
    )
  return (builderId, builder)


def construct_default (name : Ident) (push_name : String → Ident) (_fields : Array ProtoFieldMData) : CommandElabM (Ident × Command) := do
  let defaultId := push_name "Default.Value"
  /-
  Every generated structure field already carries its protobuf default in the
  structure declaration.  An empty structure literal applies those defaults
  without duplicating a potentially huge record expression here.
  -/
  let default ← `(partial def $defaultId:ident : $name := {})
  return (defaultId, default)

def construct_encode (name : Ident) (push_name : String → Ident) (toMessage : Ident) : CommandElabM (Ident × Command) := do
  let encodeId := push_name "encode"
  let s ← `(partial def $encodeId:ident : $name → Except Encoding.ProtoError ByteArray := fun x => do
    let wireMsg ← $toMessage:ident x
    wireMsg.validateForEncoding
    let bytes := Binary.Put.run (Binary.put wireMsg)
    if bytes.size > (1 <<< 31) - 1 then
      throw (.userError "serialized protobuf message exceeds the 2 GiB limit")
    return bytes)
  return (encodeId, s)

end Protobuf.Notation
