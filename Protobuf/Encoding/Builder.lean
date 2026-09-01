module

import Binary.Basic
import Binary.Get
import Binary.Put
public import Protobuf.Encoding.Basic
public import Protobuf.Encoding.Binary
public import Protobuf.UnvalidatedString
public import Std

public section

namespace Protobuf.Encoding

open Binary

@[always_inline]
def Message.push (msg : Message) (r : Record) : Message := {msg with records := msg.records.push r }

@[always_inline]
def Message.set (msg : Message) (fieldNum : Nat) (value : ProtoVal) : Message := msg.push { fieldNum, value }

/-
Validate a raw wire tree and compute its exact encoded size before passing it
to `Binary.Put`.

Decoded unknown fields already satisfy these invariants, and statically
generated builders only construct valid values.  Generated message structures
also expose `Unknown.Fields`, however, so callers can inject an out-of-domain
`Nat` varint or field number.  Reject those values explicitly instead of
letting the low-level `UInt64.ofNat` conversion truncate them.
-/
@[always_inline]
private def varintSize (value : UInt64) : Nat :=
  if value < 0x80 then 1
  else if value < 0x4000 then 2
  else if value < 0x200000 then 3
  else if value < 0x10000000 then 4
  else if value < 0x800000000 then 5
  else if value < 0x40000000000 then 6
  else if value < 0x2000000000000 then 7
  else if value < 0x100000000000000 then 8
  else if value < 0x8000000000000000 then 9
  else 10

@[inline]
def varintUInt64EncodedSize (value : UInt64) : Nat :=
  varintSize value

@[inline]
def zigZagInt32ToUInt64 (value : Int32) : UInt64 :=
  let bits := value.toUInt32
  let signMask : UInt32 := (0 : UInt32) - (bits >>> 31)
  UInt64.ofNat (((bits <<< 1) ^^^ signMask).toNat)

@[inline]
def zigZagInt64ToUInt64 (value : Int64) : UInt64 :=
  let bits := value.toUInt64
  let signMask : UInt64 := (0 : UInt64) - (bits >>> 63)
  (bits <<< 1) ^^^ signMask

mutual
  partial def ProtoVal.validateAndEncodedSize :
      ProtoVal → Except ProtoError Nat
    | .VARINT value =>
        if value > (1 <<< 64) - 1 then
          throw .invalidVarint
        else
          pure (varintSize (UInt64.ofNat value))
    | .LEN data =>
        if data.size > (1 <<< 31) - 1 then
          throw (.userError
            "length-delimited protobuf value exceeds the 2 GiB limit")
        else
          pure (varintSize (UInt64.ofNat data.size) + data.size)
    | .GROUPED message =>
        message.validateAndEncodedSize
    | .I64 _
        => pure 8
    | .I32 _ =>
        pure 4

  partial def Record.validateAndEncodedSize
      (record : Record) : Except ProtoError Nat := do
    if record.fieldNum == 0 || record.fieldNum > (1 <<< 29) - 1 then
      throw (.invalidWireType
        s!"protobuf field number {record.fieldNum} is outside 1..536870911")
    let wireType : UInt64 :=
      match record.value with
      | .VARINT _ => 0
      | .I64 _ => 1
      | .LEN _ => 2
      | .GROUPED _ => 3
      | .I32 _ => 5
    let keySize :=
      varintSize ((UInt64.ofNat record.fieldNum <<< 3) ||| wireType)
    let payloadSize ← record.value.validateAndEncodedSize
    if record.value.isGROUPED then
      -- A group has both a start and an end tag of the same encoded size.
      return keySize + payloadSize + keySize
    return keySize + payloadSize

  partial def Message.validateAndEncodedSize
      (message : Message) : Except ProtoError Nat := do
    let mut size := 0
    for record in message.records do
      size := size + (← record.validateAndEncodedSize)
    return size
end

partial def ProtoVal.validateForEncoding
    (value : ProtoVal) : Except ProtoError Unit := do
  let _ ← value.validateAndEncodedSize
  pure ()

partial def Record.validateForEncoding
    (record : Record) : Except ProtoError Unit := do
  let _ ← record.validateAndEncodedSize
  pure ()

partial def Message.validateForEncoding
    (message : Message) : Except ProtoError Unit := do
  let _ ← message.validateAndEncodedSize
  pure ()

@[always_inline]
private def validateFieldNumber
    (fieldNum : Nat) : Except ProtoError Unit := do
  if fieldNum == 0 || fieldNum > (1 <<< 29) - 1 then
    throw (.invalidWireType
      s!"protobuf field number {fieldNum} is outside 1..536870911")

@[always_inline]
def varintFieldEncodedSize
    (fieldNum : Nat) (value : UInt64) : Except ProtoError Nat := do
  validateFieldNumber fieldNum
  let key := UInt64.ofNat fieldNum <<< 3
  pure (varintSize key + varintSize value)

@[always_inline]
def fixed32FieldEncodedSize
    (fieldNum : Nat) : Except ProtoError Nat := do
  validateFieldNumber fieldNum
  let key := (UInt64.ofNat fieldNum <<< 3) ||| (5 : UInt64)
  pure (varintSize key + 4)

@[always_inline]
def fixed64FieldEncodedSize
    (fieldNum : Nat) : Except ProtoError Nat := do
  validateFieldNumber fieldNum
  let key := (UInt64.ofNat fieldNum <<< 3) ||| (1 : UInt64)
  pure (varintSize key + 8)

/--
Encoded size of a length-delimited field with an already measured payload.

Generated typed encoders use this for embedded messages, whose bytes are
written directly into the parent output rather than first materialized as a
`ProtoVal.LEN`.
-/
@[always_inline]
def lengthDelimitedFieldEncodedSize
    (fieldNum payloadSize : Nat) : Except ProtoError Nat := do
  validateFieldNumber fieldNum
  if payloadSize > (1 <<< 31) - 1 then
    throw (.userError
      "length-delimited protobuf value exceeds the 2 GiB limit")
  let key :=
    (UInt64.ofNat fieldNum <<< 3) ||| (2 : UInt64)
  return (
    varintSize key +
      varintSize (UInt64.ofNat payloadSize) +
      payloadSize
  )

/--
Encoded size of a group field with an already measured body.

The start and end tags use the same field number and therefore have the same
encoded size.
-/
@[always_inline]
def groupFieldEncodedSize
    (fieldNum payloadSize : Nat) : Except ProtoError Nat := do
  validateFieldNumber fieldNum
  let key :=
    (UInt64.ofNat fieldNum <<< 3) ||| (3 : UInt64)
  return 2 * varintSize key + payloadSize

namespace Internal

@[inline]
partial def writeVarintUInt64To
    (output : ByteArray) (value : UInt64) : ByteArray :=
  let rec go (output : ByteArray) (value : UInt64) : ByteArray :=
    let byte :=
      UInt8.ofNat ((value &&& (0x7f : UInt64)).toNat)
    let next := value >>> 7
    if next == 0 then
      output.push byte
    else
      go (output.push (byte ||| (0x80 : UInt8))) next
  go output value

@[inline]
def writeKeyTo
    (output : ByteArray) (fieldNum : Nat)
    (wireType : UInt64) : ByteArray :=
  writeVarintUInt64To output <|
    (UInt64.ofNat fieldNum <<< 3) ||| wireType

@[inline]
def writeVarintFieldTo
    (output : ByteArray) (fieldNum : Nat)
    (value : UInt64) : ByteArray :=
  writeVarintUInt64To (writeKeyTo output fieldNum 0) value

@[inline]
def writeUInt32LETo
    (output : ByteArray) (value : UInt32) : ByteArray := Id.run do
  let mut output := output
  let mut value := value
  for _ in [:4] do
    output := output.push value.toUInt8
    value := value >>> 8
  return output

@[inline]
def writeUInt64LETo
    (output : ByteArray) (value : UInt64) : ByteArray := Id.run do
  let mut output := output
  let mut value := value
  for _ in [:8] do
    output := output.push value.toUInt8
    value := value >>> 8
  return output

@[inline]
def writeFixed32FieldTo
    (output : ByteArray) (fieldNum : Nat)
    (value : UInt32) : ByteArray :=
  writeUInt32LETo (writeKeyTo output fieldNum 5) value

@[inline]
def writeFixed64FieldTo
    (output : ByteArray) (fieldNum : Nat)
    (value : UInt64) : ByteArray :=
  writeUInt64LETo (writeKeyTo output fieldNum 1) value

@[inline]
def writeLengthDelimitedFieldTo
    (output : ByteArray) (fieldNum : Nat)
    (data : ByteArray) : ByteArray :=
  let output := writeKeyTo output fieldNum 2
  let output := writeVarintUInt64To output (UInt64.ofNat data.size)
  output ++ data

mutual

/--
Append one already validated compatibility record to an existing output.

This is the fallback used for unknown fields and compatibility-only paths.
Generated known message fields call their typed child writer directly.
-/
partial def writeRecordTo
    (output : ByteArray) (record : Record) : ByteArray :=
  match record.value with
  | .VARINT value =>
      writeVarintUInt64To
        (writeKeyTo output record.fieldNum 0)
        (UInt64.ofNat value)
  | .I64 value =>
      writeUInt64LETo
        (writeKeyTo output record.fieldNum 1)
        (UInt64.ofBitVec value)
  | .LEN data =>
      let output := writeKeyTo output record.fieldNum 2
      let output :=
        writeVarintUInt64To output (UInt64.ofNat data.size)
      output ++ data
  | .GROUPED message =>
      let output := writeKeyTo output record.fieldNum 3
      let output := writeMessageTo output message
      writeKeyTo output record.fieldNum 4
  | .I32 value =>
      writeUInt32LETo
        (writeKeyTo output record.fieldNum 5)
        (UInt32.ofBitVec value)

partial def writeMessageTo
    (output : ByteArray) (message : Message) : ByteArray :=
  message.records.foldl (init := output) writeRecordTo

end

end Internal

/--
Validate and measure generated-message unknown fields in their existing
`HashMap.fold` wire order.
-/
@[noinline]
private def unknownFieldsValidateAndEncodedSizeNonempty
    (fields : Std.HashMap Nat (Array ProtoVal)) :
    Except ProtoError Nat :=
  fields.fold (init := pure 0) fun result fieldNum values => do
    let mut size ← result
    for value in values do
      size := size +
        (← (Record.mk fieldNum value).validateAndEncodedSize)
    pure size

@[always_inline]
def unknownFieldsValidateAndEncodedSize
    (fields : Std.HashMap Nat (Array ProtoVal)) :
    Except ProtoError Nat :=
  if fields.isEmpty then
    pure 0
  else
    unknownFieldsValidateAndEncodedSizeNonempty fields

/--
Append already validated generated-message unknown fields in the same order as
`Message.wire_map`.
-/
@[noinline]
private def unknownFieldsWriteToNonempty
    (output : ByteArray)
    (fields : Std.HashMap Nat (Array ProtoVal)) : ByteArray :=
  fields.fold (init := output) fun output fieldNum values =>
    values.foldl (init := output) fun output value =>
      Internal.writeRecordTo output { fieldNum, value }

@[always_inline]
def unknownFieldsWriteTo
    (output : ByteArray)
    (fields : Std.HashMap Nat (Array ProtoVal)) : ByteArray :=
  if fields.isEmpty then
    output
  else
    unknownFieldsWriteToNonempty output fields

@[always_inline]
private def ProtoVal.ofLengthDelimited (data : ByteArray) :
    Except Protobuf.Encoding.ProtoError ProtoVal := do
  if data.size > (1 <<< 31) - 1 then
    throw (.userError "length-delimited protobuf value exceeds the 2 GiB limit")
  return ProtoVal.LEN data

@[noinline]
def ProtoVal.ofMessage : Message → Except Protobuf.Encoding.ProtoError ProtoVal := fun s =>
  do
    let encodedSize ← s.validateAndEncodedSize
    if encodedSize > (1 <<< 31) - 1 then
      throw (.userError "length-delimited protobuf value exceeds the 2 GiB limit")
    ProtoVal.ofLengthDelimited (Put.run (put s) encodedSize)

@[noinline]
def ProtoVal.ofGroup : Message → Except Protobuf.Encoding.ProtoError ProtoVal := fun s => do
  let _ ← s.validateAndEncodedSize
  return ProtoVal.GROUPED s

@[always_inline]
def ProtoVal.ofString : String → Except Protobuf.Encoding.ProtoError ProtoVal := fun s =>
  ProtoVal.ofLengthDelimited s.toUTF8

@[always_inline]
def ProtoVal.ofUnvalidatedString : Protobuf.UnvalidatedString → Except Protobuf.Encoding.ProtoError ProtoVal :=
  fun s => ProtoVal.ofLengthDelimited s.bytes

@[always_inline]
def ProtoVal.ofBytes : ByteArray → Except Protobuf.Encoding.ProtoError ProtoVal :=
  ProtoVal.ofLengthDelimited

@[always_inline]
def ProtoVal.ofBool : Bool → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT (if x then 1 else 0)

@[always_inline]
def ProtoVal.ofVarint_int32 : Int32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x =>
  -- `int32` uses the sign-extended 64-bit two's-complement value on the wire.
  -- In particular, every negative `int32` must occupy ten varint bytes.
  return ProtoVal.VARINT x.toInt64.toUInt64.toNat
@[always_inline]
def ProtoVal.ofVarint_uint32 : UInt32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT x.toNat
@[always_inline]
def ProtoVal.ofVarint_int64 : Int64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT x.toUInt64.toNat
@[always_inline]
def ProtoVal.ofVarint_uint64 : UInt64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT x.toNat
@[always_inline]
def ProtoVal.ofVarint_sint32 : Int32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x =>
  return ProtoVal.VARINT (zigZagInt32ToUInt64 x).toNat
@[always_inline]
def ProtoVal.ofVarint_sint64 : Int64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x =>
  return ProtoVal.VARINT (zigZagInt64ToUInt64 x).toNat

@[always_inline]
def ProtoVal.ofI64_double : Float → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I64 (x.toBits.toBitVec)
@[always_inline]
def ProtoVal.ofI64_fixed64 : UInt64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I64 (x.toBitVec)
@[always_inline]
def ProtoVal.ofI64_sfixed64 : Int64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I64 (x.toBitVec)

@[always_inline]
def ProtoVal.ofI32_float : Float32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I32 (x.toBits.toBitVec)
@[always_inline]
def ProtoVal.ofI32_fixed32 : UInt32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I32 (x.toBitVec)
@[always_inline]
def ProtoVal.ofI32_sfixed32 : Int32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I32 (x.toBitVec)

@[always_inline]
def ProtoVal.canBePacked : ProtoVal → Bool
  | .VARINT ..
  | .I64 ..
  | .I32 .. => true
  | .GROUPED ..
  | .LEN .. => false

open Binary.Primitive.LE in
@[noinline]
def ProtoVal.of_packed (xs : Array ProtoVal) : Except ProtoError ProtoVal := do
  -- Validate before entering `Put`, whose error type cannot carry ProtoError.
  -- The second pass writes directly from the source array instead of first
  -- allocating an array of writer closures.
  for value in xs do
    match value with
    | .VARINT x =>
        if x > (1 <<< 64) - 1 then
          throw .invalidVarint
    | .I64 _
    | .I32 _ =>
        pure ()
    | _ =>
        throw (.invalidWireType
          "only VARINT, I64, and I32 protobuf values can be packed")
  let data := Binary.Put.run do
    for value in xs do
      match value with
      | .VARINT x => put_varint x
      | .I64 x => put (UInt64.ofBitVec x)
      | .I32 x => put (UInt32.ofBitVec x)
      | _ => pure ()
  ProtoVal.ofLengthDelimited data

@[noinline]
private def ProtoVal.ofPackedWith
    (xs : Array α) (write : α → Put) : Except ProtoError ProtoVal :=
  ProtoVal.ofLengthDelimited <| Binary.Put.run do
    for value in xs do
      write value

@[noinline]
def ProtoVal.ofPackedBool (xs : Array Bool) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs fun value =>
    put_varint (if value then 1 else 0)

@[noinline]
def ProtoVal.ofPackedVarint_int32
    (xs : Array Int32) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs fun value =>
    put_varint value.toInt64.toUInt64.toNat

@[noinline]
def ProtoVal.ofPackedVarint_uint32
    (xs : Array UInt32) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs fun value => put_varint value.toNat

@[noinline]
def ProtoVal.ofPackedVarint_int64
    (xs : Array Int64) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs fun value => put_varint value.toUInt64.toNat

@[noinline]
def ProtoVal.ofPackedVarint_uint64
    (xs : Array UInt64) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs fun value => put_varint value.toNat

@[noinline]
def ProtoVal.ofPackedVarint_sint32
    (xs : Array Int32) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs fun value =>
    let y := value.toUInt32
    let signMask : UInt32 := (0 : UInt32) - (y >>> 31)
    put_varint ((y <<< 1) ^^^ signMask).toNat

@[noinline]
def ProtoVal.ofPackedVarint_sint64
    (xs : Array Int64) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs fun value =>
    let y := value.toUInt64
    let signMask : UInt64 := (0 : UInt64) - (y >>> 63)
    put_varint ((y <<< 1) ^^^ signMask).toNat

open Binary.Primitive.LE in
@[noinline]
def ProtoVal.ofPackedI64_double
    (xs : Array Float) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs put

open Binary.Primitive.LE in
@[noinline]
def ProtoVal.ofPackedI64_fixed64
    (xs : Array UInt64) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs put

open Binary.Primitive.LE in
@[noinline]
def ProtoVal.ofPackedI64_sfixed64
    (xs : Array Int64) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs put

open Binary.Primitive.LE in
@[noinline]
def ProtoVal.ofPackedI32_float
    (xs : Array Float32) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs put

open Binary.Primitive.LE in
@[noinline]
def ProtoVal.ofPackedI32_fixed32
    (xs : Array UInt32) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs put

open Binary.Primitive.LE in
@[noinline]
def ProtoVal.ofPackedI32_sfixed32
    (xs : Array Int32) : Except ProtoError ProtoVal :=
  ProtoVal.ofPackedWith xs put

@[noinline]
def Message.wire_map
    (msg : Message) (fields : Std.HashMap Nat (Array ProtoVal)) : Message :=
  fields.fold (init := msg) fun msg fieldNum values =>
    values.foldl (init := msg) fun msg value =>
      msg.push { fieldNum, value }

def merge_map (a b : Std.HashMap Nat (Array ProtoVal)) : Std.HashMap Nat (Array ProtoVal) :=
  b.fold (init := a) (fun a n v => a.alter n (fun | .none => some v | .some arr => some (arr ++ v)))

end Protobuf.Encoding

namespace Protobuf.Notation

set_option quotPrecheck false

scoped notation n " <~ " val " # " msg => show Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message from do
  let v ← val
  pure (Protobuf.Encoding.Message.set msg n v)

scoped notation n " <~? " val " # " msg =>
  show Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message from do
    if let Option.some v ← val then
      pure (Protobuf.Encoding.Message.set msg n v)
    else
      pure msg

/-- flattened repeated -/
scoped notation n " <~f " vs " # " msg => show Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message from do
  let xs ← vs
  pure (Array.foldl (init := msg) (fun acc x => Protobuf.Encoding.Message.set acc n x) xs)

/-- packed repeated -/
scoped notation n " <~p " vs " # " msg => show Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message from do
  let xs ← vs
  let packed ← Protobuf.Encoding.ProtoVal.of_packed xs
  pure (Protobuf.Encoding.Message.set msg n packed)

set_option quotPrecheck true

end Notation
