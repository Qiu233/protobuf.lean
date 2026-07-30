module

import Protobuf.Encoding
public meta import Protobuf.Notation.Message.Metadata

public meta section

namespace Protobuf.Notation

open Encoding Notation
open Lean Meta Elab Term Command

private abbrev DoSeqItem := TSyntax ``Parser.Term.doSeqItem

private def validationChunkSize : Nat := 16

private def missingRequiredField
    (field : ProtoFieldMData) : CommandElabM Term :=
  `(throw
    (Protobuf.Encoding.ProtoError.missingRequiredField
      s!"required field `{$(quote field.field_proj.getId.toString)}` is missing when validating the message"))

private def fieldNeedsRequiredValidation
    (field : ProtoFieldMData) : Bool :=
  match field.map_info? with
  | some mapInfo => mapInfo.value_is_message
  | none =>
      field.oneof_type?.isSome ||
        field.mod == .required ||
        (field.internal_type?.isNone && field.enum_type?.isNone)

private def constructMessageFieldValidation
    (value : Ident) (field : ProtoFieldMData) :
    CommandElabM DoSeqItem := do
  let projection := field.field_proj
  if let some mapInfo := field.map_info? then
    let child ← mkIdent <$> mkFreshUserName `child
    let childValidator :=
      helperIdent mapInfo.value_proto_type "validateRequired"
    `(Parser.Term.doSeqItem|
      for (_, $child:ident) in $projection:ident $value:ident do
        $childValidator:ident $child:ident)
  else if field.oneof_type?.isSome then
    let oneofValue ← mkIdent <$> mkFreshUserName `oneofValue
    let oneofValidator := helperIdent field.proto_type "validateRequired"
    `(Parser.Term.doSeqItem|
      match $projection:ident $value:ident with
      | Option.none => pure ()
      | Option.some $oneofValue:ident =>
          $oneofValidator:ident $oneofValue:ident)
  else
    let isMessage :=
      field.internal_type?.isNone && field.enum_type?.isNone
    match field.mod with
    | .required =>
        let requiredValue ← mkIdent <$> mkFreshUserName `requiredValue
        let missing ← missingRequiredField field
        if isMessage then
          let childValidator :=
            helperIdent field.proto_type "validateRequired"
          `(Parser.Term.doSeqItem|
            match $projection:ident $value:ident with
            | Option.some $requiredValue:ident =>
                $childValidator:ident $requiredValue:ident
            | Option.none => $missing:term)
        else
          `(Parser.Term.doSeqItem|
            match $projection:ident $value:ident with
            | Option.some _ => pure ()
            | Option.none => $missing:term)
    | .default | .optional =>
        let child ← mkIdent <$> mkFreshUserName `child
        let childValidator :=
          helperIdent field.proto_type "validateRequired"
        `(Parser.Term.doSeqItem|
          match $projection:ident $value:ident with
          | Option.none => pure ()
          | Option.some $child:ident =>
              $childValidator:ident $child:ident)
    | .repeated =>
        let child ← mkIdent <$> mkFreshUserName `child
        let childValidator :=
          helperIdent field.proto_type "validateRequired"
        `(Parser.Term.doSeqItem|
          for $child:ident in $projection:ident $value:ident do
            $childValidator:ident $child:ident)

/--
Generate the protobuf initialization check for a message.

Unlike encoding, initialization validation only observes explicit required
presence and recursively visits retained message values. It does not construct
`ProtoVal`, `Record`, or `Message` values.
-/
def constructMessageRequiredValidator
    (name : Ident)
    (pushName : String → Ident)
    (fields : Array ProtoFieldMData) :
    CommandElabM (Array Command) := do
  let fields := fields.filter fieldNeedsRequiredValidation
  let value ← mkIdent <$> mkFreshUserName `value
  let validatorId := pushName "validateRequired"
  if fields.size ≤ validationChunkSize then
    let validations ←
      fields.mapM (constructMessageFieldValidation value)
    let validator ← `(partial def $validatorId:ident
        ($value : $name) :
        Except Protobuf.Encoding.ProtoError Unit := do
      $validations*
      pure ())
    return #[validator]

  let chunkCount :=
    (fields.size + validationChunkSize - 1) / validationChunkSize
  let chunks ← (List.range chunkCount).toArray.mapM fun i => do
    let start := i * validationChunkSize
    let chunkFields :=
      fields.extract start
        (min fields.size (start + validationChunkSize))
    let chunkId :=
      mkIdentFrom name
        ((helperName name.getId "validateRequired").str s!"_chunk_{i}")
    let chunkValue ← mkIdent <$> mkFreshUserName `value
    let validations ←
      chunkFields.mapM
        (constructMessageFieldValidation chunkValue)
    let command ← `(partial def $chunkId:ident
        ($chunkValue : $name) :
        Except Protobuf.Encoding.ProtoError Unit := do
      $validations*
      pure ())
    pure (chunkId, command)
  let calls ← chunks.mapM fun (chunkId, _) =>
    `(Parser.Term.doSeqItem|
      let _ ← $chunkId:ident $value:ident)
  let validator ← `(partial def $validatorId:ident
      ($value : $name) :
      Except Protobuf.Encoding.ProtoError Unit := do
    $calls*
    pure ())
  return chunks.map Prod.snd |>.push validator

/--
Generate the initialization check for the value retained by a oneof.

Only message-valued alternatives can contain required fields. The containing
message decides whether the oneof itself is present.
-/
def constructOneofRequiredValidator
    (name : Ident)
    (pushName : String → Ident)
    (fields : Array ProtoFieldMData) :
    CommandElabM Command := do
  let value ← mkIdent <$> mkFreshUserName `value
  let alternatives ← fields.mapM fun field => do
    let ctor := field.field_proj
    let alternativeValue ←
      mkIdent <$> mkFreshUserName field.field_name.getId
    if field.internal_type?.isNone && field.enum_type?.isNone then
      let childValidator :=
        helperIdent field.proto_type "validateRequired"
      `(Parser.Term.matchAltExpr|
        | $ctor:ident $alternativeValue:ident =>
            $childValidator:ident $alternativeValue:ident)
    else
      `(Parser.Term.matchAltExpr|
        | $ctor:ident _ => pure ())
  let validatorId := pushName "validateRequired"
  `(partial def $validatorId:ident
      ($value : $name) :
      Except Protobuf.Encoding.ProtoError Unit :=
    match $value:ident with
    $alternatives:matchAlt*)

end Protobuf.Notation
