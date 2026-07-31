module

import Protobuf.Encoding.Builder
public meta import Protobuf.Notation.Message.Metadata

public meta section

namespace Protobuf.Notation

open Encoding

open Lean Meta Elab Term Command

private def InternalType.packedBuilder? : InternalType → Option Ident
  | .bool => some <| mkIdent ``Encoding.ProtoVal.ofPackedBool
  | .int32 => some <| mkIdent ``Encoding.ProtoVal.ofPackedVarint_int32
  | .uint32 => some <| mkIdent ``Encoding.ProtoVal.ofPackedVarint_uint32
  | .int64 => some <| mkIdent ``Encoding.ProtoVal.ofPackedVarint_int64
  | .uint64 => some <| mkIdent ``Encoding.ProtoVal.ofPackedVarint_uint64
  | .sint32 => some <| mkIdent ``Encoding.ProtoVal.ofPackedVarint_sint32
  | .sint64 => some <| mkIdent ``Encoding.ProtoVal.ofPackedVarint_sint64
  | .double => some <| mkIdent ``Encoding.ProtoVal.ofPackedI64_double
  | .fixed64 => some <| mkIdent ``Encoding.ProtoVal.ofPackedI64_fixed64
  | .sfixed64 => some <| mkIdent ``Encoding.ProtoVal.ofPackedI64_sfixed64
  | .float => some <| mkIdent ``Encoding.ProtoVal.ofPackedI32_float
  | .fixed32 => some <| mkIdent ``Encoding.ProtoVal.ofPackedI32_fixed32
  | .sfixed32 => some <| mkIdent ``Encoding.ProtoVal.ofPackedI32_sfixed32
  | .string
  | .raw_string
  | .bytes => none

private def fieldBuilder
    (field : ProtoFieldMData) : CommandElabM Term := do
  field.builder?.getDM <|
    throwErrorAt field.field_name
      "{decl_name%}: internal error: ordinary field has no generated wire builder"

private def packedFieldBuilder
    (field : ProtoFieldMData) : CommandElabM Term := do
  if let some packedBuilder := field.internal_type?.bind InternalType.packedBuilder? then
    return packedBuilder
  let builder ← fieldBuilder field
  `(fun values => do
      let wireValues ← values.mapM $builder:term
      Encoding.ProtoVal.of_packed wireValues)

private def isMessageField (field : ProtoFieldMData) : Bool :=
  field.internal_type?.isNone &&
    field.enum_type?.isNone &&
    field.oneof_type?.isNone

private def InternalType.varintValue? :
    InternalType → Ident → CommandElabM (Option Term)
  | .bool, value => some <$>
      `(if $value:ident then (1 : UInt64) else 0)
  | .int32, value => some <$>
      `(($value:ident).toInt64.toUInt64)
  | .uint32, value => some <$>
      `(UInt64.ofNat ($value:ident).toNat)
  | .int64, value => some <$>
      `(($value:ident).toUInt64)
  | .uint64, value => some <$> `($value:ident)
  | .sint32, value => some <$>
      `(Protobuf.Encoding.zigZagInt32ToUInt64 $value:ident)
  | .sint64, value => some <$>
      `(Protobuf.Encoding.zigZagInt64ToUInt64 $value:ident)
  | _, _ => pure none

private def InternalType.fixed32Value? :
    InternalType → Ident → CommandElabM (Option Term)
  | .float, value => some <$> `(($value:ident).toBits)
  | .fixed32, value => some <$> `($value:ident)
  | .sfixed32, value => some <$> `(($value:ident).toUInt32)
  | _, _ => pure none

private def InternalType.fixed64Value? :
    InternalType → Ident → CommandElabM (Option Term)
  | .double, value => some <$> `(($value:ident).toBits)
  | .fixed64, value => some <$> `($value:ident)
  | .sfixed64, value => some <$> `(($value:ident).toUInt64)
  | _, _ => pure none

private def InternalType.lengthDelimitedPayload :
    InternalType → Ident → CommandElabM (Option Term)
  | .string, value => some <$> `(($value:ident).toUTF8)
  | .raw_string, value => some <$> `(($value:ident).bytes)
  | .bytes, value => some <$> `($value:ident)
  | _, _ => pure none

private def InternalType.lengthDelimitedSize :
    InternalType → Ident → CommandElabM (Option Term)
  | .string, value => some <$> `(($value:ident).utf8ByteSize)
  | .raw_string, value => some <$> `(($value:ident).bytes.size)
  | .bytes, value => some <$> `(($value:ident).size)
  | _, _ => pure none

private def constructSizeOccurrence
    (field : ProtoFieldMData)
    (value size validateRequired : Ident) :
    CommandElabM (TSyntax ``Parser.Term.doSeqItem) := do
  if isMessageField field then
    let childSize :=
      helperIdent field.proto_type "encodedSizeWithRequiredValidation"
    if field.options.wired_as_group?.isEqSome true then
      `(Parser.Term.doSeqItem|
        let $size:ident ← do
          let payloadSize ←
            $childSize:ident $value:ident $validateRequired:ident
          let recordSize ←
            Protobuf.Encoding.groupFieldEncodedSize
              $(field.field_num) payloadSize
          pure ($size + recordSize))
    else
      `(Parser.Term.doSeqItem|
        let $size:ident ← do
          let payloadSize ←
            $childSize:ident $value:ident $validateRequired:ident
          let recordSize ←
            Protobuf.Encoding.lengthDelimitedFieldEncodedSize
              $(field.field_num) payloadSize
          pure ($size + recordSize))
  else if let some internalType := field.internal_type? then
    if let some wireValue ← internalType.varintValue? value then
      `(Parser.Term.doSeqItem|
        let $size:ident ← do
          let recordSize ←
            Protobuf.Encoding.varintFieldEncodedSize
              $(field.field_num) $wireValue:term
          pure ($size + recordSize))
    else if (← internalType.fixed32Value? value).isSome then
      `(Parser.Term.doSeqItem|
        let $size:ident ← do
          let recordSize ←
            Protobuf.Encoding.fixed32FieldEncodedSize
              $(field.field_num)
          pure ($size + recordSize))
    else if (← internalType.fixed64Value? value).isSome then
      `(Parser.Term.doSeqItem|
        let $size:ident ← do
          let recordSize ←
            Protobuf.Encoding.fixed64FieldEncodedSize
              $(field.field_num)
          pure ($size + recordSize))
    else if let some payloadSize ←
        internalType.lengthDelimitedSize value then
      `(Parser.Term.doSeqItem|
        let $size:ident ← do
          let recordSize ←
            Protobuf.Encoding.lengthDelimitedFieldEncodedSize
              $(field.field_num) $payloadSize:term
          pure ($size + recordSize))
    else
      throwErrorAt field.field_name
        "{decl_name%}: internal error: unsupported direct scalar size"
  else
    let builder ← fieldBuilder field
    `(Parser.Term.doSeqItem|
      let $size:ident ← do
        let wireValue ← $builder:term $value:ident
        let recordSize ←
          (Protobuf.Encoding.Record.mk
            $(field.field_num) wireValue).validateAndEncodedSize
        pure ($size + recordSize))

private def constructWriteOccurrence
    (field : ProtoFieldMData)
    (value output validateRequired : Ident) :
    CommandElabM (TSyntax ``Parser.Term.doSeqItem) := do
  if isMessageField field then
    let childSize :=
      helperIdent field.proto_type "encodedSizeWithRequiredValidation"
    let childWrite :=
      helperIdent field.proto_type "writeToWithRequiredValidation"
    if field.options.wired_as_group?.isEqSome true then
      `(Parser.Term.doSeqItem|
        let $output:ident ← do
          let output :=
            Protobuf.Encoding.Internal.writeKeyTo
              $output $(field.field_num) 3
          let output ←
            $childWrite:ident
              $value:ident output $validateRequired:ident
          pure <|
            Protobuf.Encoding.Internal.writeKeyTo
              output $(field.field_num) 4)
    else
      `(Parser.Term.doSeqItem|
        let $output:ident ← do
          let payloadSize ←
            $childSize:ident $value:ident $validateRequired:ident
          let output :=
            Protobuf.Encoding.Internal.writeKeyTo
              $output $(field.field_num) 2
          let output :=
            Protobuf.Encoding.Internal.writeVarintUInt64To
              output (UInt64.ofNat payloadSize)
          $childWrite:ident
            $value:ident output $validateRequired:ident)
  else if let some internalType := field.internal_type? then
    if let some wireValue ← internalType.varintValue? value then
      `(Parser.Term.doSeqItem|
        let $output:ident :=
          Protobuf.Encoding.Internal.writeVarintFieldTo
            $output $(field.field_num) $wireValue:term)
    else if let some wireValue ← internalType.fixed32Value? value then
      `(Parser.Term.doSeqItem|
        let $output:ident :=
          Protobuf.Encoding.Internal.writeFixed32FieldTo
            $output $(field.field_num) $wireValue:term)
    else if let some wireValue ← internalType.fixed64Value? value then
      `(Parser.Term.doSeqItem|
        let $output:ident :=
          Protobuf.Encoding.Internal.writeFixed64FieldTo
            $output $(field.field_num) $wireValue:term)
    else if let some payload ←
        internalType.lengthDelimitedPayload value then
      `(Parser.Term.doSeqItem|
        let $output:ident :=
          Protobuf.Encoding.Internal.writeLengthDelimitedFieldTo
            $output $(field.field_num) $payload:term)
    else
      throwErrorAt field.field_name
        "{decl_name%}: internal error: unsupported direct scalar writer"
  else
    let builder ← fieldBuilder field
    `(Parser.Term.doSeqItem|
      let $output:ident ← do
        let wireValue ← $builder:term $value:ident
        pure <| Protobuf.Encoding.Internal.writeRecordTo
          $output
          (Protobuf.Encoding.Record.mk $(field.field_num) wireValue))

private inductive DirectPass where
  | size
  | write

private def constructPackedAction
    (pass : DirectPass)
    (field : ProtoFieldMData)
    (values : Term)
    (accumulator element : Ident) :
    CommandElabM (TSyntax ``Parser.Term.doSeqItem) := do
  let some internalType := field.internal_type?
    | throwErrorAt field.field_name
        "{decl_name%}: internal error: direct packed field is not primitive"
  if let some wireValue ← internalType.varintValue? element then
    match pass with
    | .size =>
        `(Parser.Term.doSeqItem|
          let $accumulator:ident ← do
            let payloadSize :=
              $values:term |>.foldl (init := 0)
                fun payloadSize $element:ident =>
                  payloadSize +
                    Protobuf.Encoding.varintUInt64EncodedSize
                      $wireValue:term
            let recordSize ←
              Protobuf.Encoding.lengthDelimitedFieldEncodedSize
                $(field.field_num) payloadSize
            pure ($accumulator + recordSize))
    | .write =>
        `(Parser.Term.doSeqItem|
          let $accumulator:ident := Id.run do
            let payloadSize :=
              $values:term |>.foldl (init := 0)
                fun payloadSize $element:ident =>
                  payloadSize +
                    Protobuf.Encoding.varintUInt64EncodedSize
                      $wireValue:term
            let output :=
              Protobuf.Encoding.Internal.writeKeyTo
                $accumulator $(field.field_num) 2
            let output :=
              Protobuf.Encoding.Internal.writeVarintUInt64To
                output (UInt64.ofNat payloadSize)
            pure <|
              $values:term |>.foldl (init := output)
                fun output $element:ident =>
                  Protobuf.Encoding.Internal.writeVarintUInt64To
                    output $wireValue:term)
  else if let some wireValue ← internalType.fixed32Value? element then
    match pass with
    | .size =>
        `(Parser.Term.doSeqItem|
          let $accumulator:ident ← do
            let payloadSize := ($values:term).size * 4
            let recordSize ←
              Protobuf.Encoding.lengthDelimitedFieldEncodedSize
                $(field.field_num) payloadSize
            pure ($accumulator + recordSize))
    | .write =>
        `(Parser.Term.doSeqItem|
          let $accumulator:ident := Id.run do
            let payloadSize := ($values:term).size * 4
            let output :=
              Protobuf.Encoding.Internal.writeKeyTo
                $accumulator $(field.field_num) 2
            let output :=
              Protobuf.Encoding.Internal.writeVarintUInt64To
                output (UInt64.ofNat payloadSize)
            pure <|
              $values:term |>.foldl (init := output)
                fun output $element:ident =>
                  Protobuf.Encoding.Internal.writeUInt32LETo
                    output $wireValue:term)
  else if let some wireValue ← internalType.fixed64Value? element then
    match pass with
    | .size =>
        `(Parser.Term.doSeqItem|
          let $accumulator:ident ← do
            let payloadSize := ($values:term).size * 8
            let recordSize ←
              Protobuf.Encoding.lengthDelimitedFieldEncodedSize
                $(field.field_num) payloadSize
            pure ($accumulator + recordSize))
    | .write =>
        `(Parser.Term.doSeqItem|
          let $accumulator:ident := Id.run do
            let payloadSize := ($values:term).size * 8
            let output :=
              Protobuf.Encoding.Internal.writeKeyTo
                $accumulator $(field.field_num) 2
            let output :=
              Protobuf.Encoding.Internal.writeVarintUInt64To
                output (UInt64.ofNat payloadSize)
            pure <|
              $values:term |>.foldl (init := output)
                fun output $element:ident =>
                  Protobuf.Encoding.Internal.writeUInt64LETo
                    output $wireValue:term)
  else
    throwErrorAt field.field_name
      "{decl_name%}: internal error: unsupported direct packed primitive"

private def constructFieldBody
    (pass : DirectPass)
    (val accumulator validateRequired : Ident)
    (field : ProtoFieldMData) :
    CommandElabM (TSyntax ``Parser.Term.doSeqItem) := do
  let occurrence
      (value : Ident) :
      CommandElabM (TSyntax ``Parser.Term.doSeqItem) :=
    match pass with
    | .size =>
        constructSizeOccurrence field value accumulator validateRequired
    | .write =>
        constructWriteOccurrence field value accumulator validateRequired
  let fieldValue ← mkIdent <$> mkFreshUserName `fieldValue
  let one ← occurrence fieldValue
  let oneBody := #[one]
  let projected ← `($(field.field_proj) $val)
  match field.mod with
  | .default =>
      if isMessageField field then
        `(Parser.Term.doSeqItem|
          let $accumulator:ident ← do
            if let Option.some $fieldValue:ident := $projected:term then
              $oneBody*
              pure $accumulator
            else
              pure $accumulator)
      else
        `(Parser.Term.doSeqItem|
          let $accumulator:ident ← do
            if $(field.test_unset) $projected:term then
              pure $accumulator
            else
              let $fieldValue:ident := $projected:term
              $oneBody*
              pure $accumulator)
  | .required =>
      `(Parser.Term.doSeqItem|
        let $accumulator:ident ← do
          if let Option.some $fieldValue:ident := $projected:term then
            $oneBody*
            pure $accumulator
          else if $validateRequired:ident then
            throw
              (Protobuf.Encoding.ProtoError.missingRequiredField
                s!"required field `{$(quote field.field_proj.getId.toString)}` is missing when building the message")
          else
            pure $accumulator)
  | .optional =>
      `(Parser.Term.doSeqItem|
        let $accumulator:ident ← do
          if let Option.some $fieldValue:ident := $projected:term then
            $oneBody*
            pure $accumulator
          else
            pure $accumulator)
  | .repeated =>
      if field.options.packed?.isEqSome true then
        let packedAction ←
          if field.internal_type?.isSome then
            constructPackedAction
              pass field projected accumulator fieldValue
          else
            let packedBuilder ← packedFieldBuilder field
            match pass with
            | .size =>
                `(Parser.Term.doSeqItem|
                  let $accumulator:ident ← do
                    let wireValue ← $packedBuilder:term $projected:term
                    let recordSize ←
                      (Protobuf.Encoding.Record.mk
                        $(field.field_num) wireValue).validateAndEncodedSize
                    pure ($accumulator + recordSize))
            | .write =>
                `(Parser.Term.doSeqItem|
                  let $accumulator:ident ← do
                    let wireValue ← $packedBuilder:term $projected:term
                    pure <| Protobuf.Encoding.Internal.writeRecordTo
                      $accumulator
                      (Protobuf.Encoding.Record.mk
                        $(field.field_num) wireValue))
        let packedBody := #[packedAction]
        `(Parser.Term.doSeqItem|
          let $accumulator:ident ← do
            if $(field.test_unset) $projected:term then
              pure $accumulator
            else
              $packedBody*
              pure $accumulator)
      else
        `(Parser.Term.doSeqItem|
          let $accumulator:ident ← do
            if $(field.test_unset) $projected:term then
              pure $accumulator
            else
              ($projected:term).foldlM
                (init := $accumulator)
                fun $accumulator:ident $fieldValue:ident => do
                  $oneBody*
                  pure $accumulator)

private def directChunkSize : Nat := 16

structure DirectEncodingResult where
  sizeId : Ident
  writeId : Ident
  commands : Array Command
  useAtTopLevel : Bool

/--
Generate an exact typed size pass and a direct writer.

Map and oneof field lowering is kept on the compatibility path for now.  Such
messages still receive these helpers so ordinary parents can call them
uniformly, but their top-level `encode` wrapper remains unchanged.
-/
def constructDirectEncoding
    (name : Ident)
    (pushName : String → Ident)
    (fields : Array ProtoFieldMData) :
    CommandElabM DirectEncodingResult := do
  let sizeId := pushName "encodedSizeWithRequiredValidation"
  let writeId := pushName "writeToWithRequiredValidation"
  let useAtTopLevel :=
    fields.all fun field =>
      field.map_info?.isNone && field.oneof_type?.isNone
  if !useAtTopLevel then
    let toMessageCore := pushName "toMessageWithRequiredValidation"
    let sizeCommand ← `(partial def $sizeId:ident :
        $name → Bool →
          Except Protobuf.Encoding.ProtoError Nat :=
      fun value validateRequired => do
        let wireMessage ← $toMessageCore:ident value validateRequired
        wireMessage.validateAndEncodedSize)
    let writeCommand ← `(partial def $writeId:ident :
        $name → ByteArray → Bool →
          Except Protobuf.Encoding.ProtoError ByteArray :=
      fun value output validateRequired => do
        let wireMessage ← $toMessageCore:ident value validateRequired
        pure <| Protobuf.Encoding.Internal.writeMessageTo output wireMessage)
    return {
      sizeId
      writeId
      commands := #[sizeCommand, writeCommand]
      useAtTopLevel
    }

  let chunkCount :=
    max 1 ((fields.size + directChunkSize - 1) / directChunkSize)
  let sizeChunks ← (List.range chunkCount).toArray.mapM fun i => do
    let start := i * directChunkSize
    let chunkFields :=
      fields.extract start (min fields.size (start + directChunkSize))
    let chunkId :=
      pushName s!"encodedSizeWithRequiredValidation_chunk_{i}"
    let val ← mkIdent <$> mkFreshUserName `val
    let size ← mkIdent <$> mkFreshUserName `size
    let validateRequired ← mkIdent <$> mkFreshUserName `validateRequired
    let body ←
      chunkFields.mapM
        (constructFieldBody .size val size validateRequired)
    let command ← `(partial def $chunkId:ident :
        $name → Nat → Bool →
          Except Protobuf.Encoding.ProtoError Nat :=
      fun $val $size $validateRequired => do
        $body*
        pure $size)
    pure (chunkId, command)
  let writeChunks ← (List.range chunkCount).toArray.mapM fun i => do
    let start := i * directChunkSize
    let chunkFields :=
      fields.extract start (min fields.size (start + directChunkSize))
    let chunkId :=
      pushName s!"writeToWithRequiredValidation_chunk_{i}"
    let val ← mkIdent <$> mkFreshUserName `val
    let output ← mkIdent <$> mkFreshUserName `output
    let validateRequired ← mkIdent <$> mkFreshUserName `validateRequired
    let body ←
      chunkFields.mapM
        (constructFieldBody .write val output validateRequired)
    let command ← `(partial def $chunkId:ident :
        $name → ByteArray → Bool →
          Except Protobuf.Encoding.ProtoError ByteArray :=
      fun $val $output $validateRequired => do
        $body*
        pure $output)
    pure (chunkId, command)

  let val ← mkIdent <$> mkFreshUserName `val
  let size ← mkIdent <$> mkFreshUserName `size
  let validateRequired ← mkIdent <$> mkFreshUserName `validateRequired
  let sizeCalls ← sizeChunks.mapM fun (chunkId, _) =>
    `(Parser.Term.doSeqItem|
      let $size:ident ←
        $chunkId:ident $val $size $validateRequired)
  let sizeCommand ← `(partial def $sizeId:ident :
      $name → Bool →
        Except Protobuf.Encoding.ProtoError Nat :=
    fun $val $validateRequired => do
      let $size:ident := 0
      $sizeCalls*
      let $size ← do
        let unknownSize ←
          Protobuf.Encoding.unknownFieldsValidateAndEncodedSize
            ($(mkIdentFrom name (name.getId.str "Unknown.Fields")) $val)
        pure ($size + unknownSize)
      pure $size)

  let output ← mkIdent <$> mkFreshUserName `output
  let writeCalls ← writeChunks.mapM fun (chunkId, _) =>
    `(Parser.Term.doSeqItem|
      let $output:ident ←
        $chunkId:ident $val $output $validateRequired)
  let writeCommand ← `(partial def $writeId:ident :
      $name → ByteArray → Bool →
        Except Protobuf.Encoding.ProtoError ByteArray :=
    fun $val $output $validateRequired => do
      $writeCalls*
      pure <| Protobuf.Encoding.unknownFieldsWriteTo
        $output
        ($(mkIdentFrom name (name.getId.str "Unknown.Fields")) $val))
  return {
    sizeId
    writeId
    commands :=
      sizeChunks.map Prod.snd ++
        writeChunks.map Prod.snd ++
        #[sizeCommand, writeCommand]
    useAtTopLevel
  }

def constructDirectEncode
    (name : Ident)
    (pushName : String → Ident)
    (direct : DirectEncodingResult) :
    CommandElabM (Ident × Command) := do
  let encodeId := pushName "encode"
  let command ← `(partial def $encodeId:ident :
      $name → Except Protobuf.Encoding.ProtoError ByteArray :=
    fun value => do
      let encodedSize ← $direct.sizeId:ident value true
      if encodedSize > (1 <<< 31) - 1 then
        throw (.userError
          "serialized protobuf message exceeds the 2 GiB limit")
      let output := ByteArray.emptyWithCapacity encodedSize
      let output ← $direct.writeId:ident value output true
      if output.size != encodedSize then
        throw (.userError
          "internal protobuf encoder size mismatch")
      pure output)
  return (encodeId, command)

end Protobuf.Notation
