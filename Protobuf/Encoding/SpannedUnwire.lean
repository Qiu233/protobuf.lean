module

public import Protobuf.Encoding.Spanned
public import Protobuf.UnvalidatedString

public section

namespace Protobuf.Encoding

local macro "throwWireType! " err:term : term =>
  ``(throw (ProtoError.invalidWireType s!"{decl_name%}: {$err}"))
local macro "throwInvalidBuffer! " err:term : term =>
  ``(throw (ProtoError.invalidBuffer s!"{decl_name%}: {$err}"))

private def ByteSpan.validate (span : ByteSpan) : Except ProtoError Unit := do
  if span.start > span.stop || span.stop > span.source.size then
    throw (.invalidBuffer "protobuf byte span is outside its source buffer")

private def readSpanByte
    (source : ByteArray) (stop offset : Nat) :
    Except ProtoError (UInt8 × Nat) := do
  if offset >= stop then
    throw .truncated
  let some byte := source[offset]?
    | throw .truncated
  return (byte, offset + 1)

private partial def readSpanVarint
    (source : ByteArray) (stop offset : Nat) :
    Except ProtoError (UInt64 × Nat) := do
  let rec go
      (offset : Nat) (value shift : UInt64) (index : Nat) :
      Except ProtoError (UInt64 × Nat) := do
    let (byte, offset) ← readSpanByte source stop offset
    if index == 9 then
      if byte > 1 then
        throw .invalidVarint
      return (value ||| (UInt64.ofNat byte.toNat <<< shift), offset)
    let value :=
      value |||
        (UInt64.ofNat (byte &&& (0x7f : UInt8)).toNat <<< shift)
    if byte &&& (0x80 : UInt8) == 0 then
      return (value, offset)
    go offset value (shift + 7) (index + 1)
  go offset 0 0 0

private def readSpanFixed
    (source : ByteArray) (stop offset width : Nat) :
    Except ProtoError (UInt64 × Nat) := do
  let mut offset := offset
  let mut value : UInt64 := 0
  for index in [:width] do
    let (byte, next) ← readSpanByte source stop offset
    value := value |||
      (UInt64.ofNat byte.toNat <<< UInt64.ofNat (8 * index))
    offset := next
  return (value, offset)

@[noinline]
private def ByteSpan.appendVarints
    (span : ByteSpan) (out : Array α) (convert : UInt64 → α) :
    Except ProtoError (Array α) := do
  span.validate
  let mut offset := span.start
  let mut out := out
  while offset < span.stop do
    let (value, next) ←
      readSpanVarint span.source span.stop offset
    out := out.push (convert value)
    offset := next
  return out

@[noinline]
private def ByteSpan.appendFixed
    (span : ByteSpan) (out : Array α) (width : Nat)
    (convert : UInt64 → α) :
    Except ProtoError (Array α) := do
  span.validate
  let mut offset := span.start
  let mut out := out
  while offset < span.stop do
    let (value, next) ←
      readSpanFixed span.source span.stop offset width
    out := out.push (convert value)
    offset := next
  return out

private def zigzagDecode32 (value : UInt64) : Int32 :=
  let value := value.toUInt32
  let mask : UInt32 := 0 - (value &&& 1)
  Int32.ofBitVec (((value >>> 1) ^^^ mask).toBitVec)

private def zigzagDecode64 (value : UInt64) : Int64 :=
  let mask : UInt64 := 0 - (value &&& 1)
  Int64.ofBitVec (((value >>> 1) ^^^ mask).toBitVec)

@[noinline]
def SpannedRecord.getString
    (record : SpannedRecord) : Except ProtoError String := do
  let .len source start stop := record.value
    | throwWireType! "expected LEN"
  let some value := String.fromUTF8? (source.extract start stop)
    | throwInvalidBuffer! "invalid UTF-8 data"
  return value

@[noinline]
def SpannedRecord.getUnvalidatedString
    (record : SpannedRecord) :
    Except ProtoError Protobuf.UnvalidatedString := do
  let .len source start stop := record.value
    | throwWireType! "expected LEN"
  return .ofBytes (source.extract start stop)

@[noinline]
def SpannedRecord.getBytes
    (record : SpannedRecord) : Except ProtoError ByteArray := do
  let .len source start stop := record.value
    | throwWireType! "expected LEN"
  return source.extract start stop

@[noinline]
def SpannedRecord.getMessage
    (record : SpannedRecord)
    (recursionBudget : Nat := defaultMessageRecursionLimit) :
    Except ProtoError SpannedMessage := do
  let .len source start stop := record.value
    | throwWireType! "expected LEN"
  let childBudget ← descendMessageRecursion recursionBudget
  ByteSpan.decodeMessage { source, start, stop } childBudget

@[noinline]
def SpannedRecord.getGroup
    (record : SpannedRecord) : Except ProtoError SpannedMessage := do
  let .grouped message := record.value
    | throwWireType! "expected GROUPED"
  return message

@[noinline]
def SpannedRecord.getBool
    (record : SpannedRecord) : Except ProtoError Bool := do
  let .varint value := record.value | throwWireType! "expected VARINT"
  return value != 0

@[noinline]
def SpannedRecord.getVarint_int32
    (record : SpannedRecord) : Except ProtoError Int32 := do
  let .varint value := record.value | throwWireType! "expected VARINT"
  return Int32.ofBitVec value.toUInt32.toBitVec

@[noinline]
def SpannedRecord.getVarint_uint32
    (record : SpannedRecord) : Except ProtoError UInt32 := do
  let .varint value := record.value | throwWireType! "expected VARINT"
  return value.toUInt32

@[noinline]
def SpannedRecord.getVarint_int64
    (record : SpannedRecord) : Except ProtoError Int64 := do
  let .varint value := record.value | throwWireType! "expected VARINT"
  return Int64.ofBitVec value.toBitVec

@[noinline]
def SpannedRecord.getVarint_uint64
    (record : SpannedRecord) : Except ProtoError UInt64 := do
  let .varint value := record.value | throwWireType! "expected VARINT"
  return value

@[noinline]
def SpannedRecord.getVarint_sint32
    (record : SpannedRecord) : Except ProtoError Int32 := do
  let .varint value := record.value | throwWireType! "expected VARINT"
  return zigzagDecode32 value

@[noinline]
def SpannedRecord.getVarint_sint64
    (record : SpannedRecord) : Except ProtoError Int64 := do
  let .varint value := record.value | throwWireType! "expected VARINT"
  return zigzagDecode64 value

@[noinline]
def SpannedRecord.getI64_double
    (record : SpannedRecord) : Except ProtoError Float := do
  let .i64 value := record.value | throwWireType! "expected I64"
  return Float.ofBits value

@[noinline]
def SpannedRecord.getI64_fixed64
    (record : SpannedRecord) : Except ProtoError UInt64 := do
  let .i64 value := record.value | throwWireType! "expected I64"
  return value

@[noinline]
def SpannedRecord.getI64_sfixed64
    (record : SpannedRecord) : Except ProtoError Int64 := do
  let .i64 value := record.value | throwWireType! "expected I64"
  return Int64.ofBitVec value.toBitVec

@[noinline]
def SpannedRecord.getI32_float
    (record : SpannedRecord) : Except ProtoError Float32 := do
  let .i32 value := record.value | throwWireType! "expected I32"
  return Float32.ofBits value

@[noinline]
def SpannedRecord.getI32_fixed32
    (record : SpannedRecord) : Except ProtoError UInt32 := do
  let .i32 value := record.value | throwWireType! "expected I32"
  return value

@[noinline]
def SpannedRecord.getI32_sfixed32
    (record : SpannedRecord) : Except ProtoError Int32 := do
  let .i32 value := record.value | throwWireType! "expected I32"
  return Int32.ofBitVec value.toBitVec

@[noinline]
private def SpannedRecord.appendRepeatedVarintAs
    (record : SpannedRecord) (out : Array α) (convert : UInt64 → α) :
    Except ProtoError (Array α) := do
  match record.value with
  | .len source start stop =>
      ByteSpan.appendVarints { source, start, stop } out convert
  | .varint value => return out.push (convert value)
  | _ => throwWireType! "value of repeated field has the wrong wire type"

@[noinline]
private def SpannedRecord.appendRepeatedI64As
    (record : SpannedRecord) (out : Array α) (convert : UInt64 → α) :
    Except ProtoError (Array α) := do
  match record.value with
  | .len source start stop =>
      ByteSpan.appendFixed { source, start, stop } out 8 convert
  | .i64 value => return out.push (convert value)
  | _ => throwWireType! "value of repeated field has the wrong wire type"

@[noinline]
private def SpannedRecord.appendRepeatedI32As
    (record : SpannedRecord) (out : Array α) (convert : UInt32 → α) :
    Except ProtoError (Array α) := do
  match record.value with
  | .len source start stop =>
      ByteSpan.appendFixed { source, start, stop } out 4 fun value =>
        convert value.toUInt32
  | .i32 value => return out.push (convert value)
  | _ => throwWireType! "value of repeated field has the wrong wire type"

@[noinline]
def SpannedRecord.appendRepeatedBool
    (record : SpannedRecord) (out : Array Bool) :
    Except ProtoError (Array Bool) :=
  record.appendRepeatedVarintAs out (· != 0)

@[noinline]
def SpannedRecord.appendRepeatedString
    (record : SpannedRecord) (out : Array String) :
    Except ProtoError (Array String) := do
  return out.push (← record.getString)

@[noinline]
def SpannedRecord.appendRepeatedUnvalidatedString
    (record : SpannedRecord)
    (out : Array Protobuf.UnvalidatedString) :
    Except ProtoError (Array Protobuf.UnvalidatedString) := do
  return out.push (← record.getUnvalidatedString)

@[noinline]
def SpannedRecord.appendRepeatedBytes
    (record : SpannedRecord) (out : Array ByteArray) :
    Except ProtoError (Array ByteArray) := do
  return out.push (← record.getBytes)

@[noinline]
def SpannedRecord.appendRepeatedVarint_int32
    (record : SpannedRecord) (out : Array Int32) :
    Except ProtoError (Array Int32) :=
  record.appendRepeatedVarintAs out fun value =>
    Int32.ofBitVec value.toUInt32.toBitVec

@[noinline]
def SpannedRecord.appendRepeatedVarint_uint32
    (record : SpannedRecord) (out : Array UInt32) :
    Except ProtoError (Array UInt32) :=
  record.appendRepeatedVarintAs out UInt64.toUInt32

@[noinline]
def SpannedRecord.appendRepeatedVarint_int64
    (record : SpannedRecord) (out : Array Int64) :
    Except ProtoError (Array Int64) :=
  record.appendRepeatedVarintAs out fun value =>
    Int64.ofBitVec value.toBitVec

@[noinline]
def SpannedRecord.appendRepeatedVarint_uint64
    (record : SpannedRecord) (out : Array UInt64) :
    Except ProtoError (Array UInt64) :=
  record.appendRepeatedVarintAs out id

@[noinline]
def SpannedRecord.appendRepeatedVarint_sint32
    (record : SpannedRecord) (out : Array Int32) :
    Except ProtoError (Array Int32) :=
  record.appendRepeatedVarintAs out zigzagDecode32

@[noinline]
def SpannedRecord.appendRepeatedVarint_sint64
    (record : SpannedRecord) (out : Array Int64) :
    Except ProtoError (Array Int64) :=
  record.appendRepeatedVarintAs out zigzagDecode64

@[noinline]
def SpannedRecord.appendRepeatedI64_double
    (record : SpannedRecord) (out : Array Float) :
    Except ProtoError (Array Float) :=
  record.appendRepeatedI64As out Float.ofBits

@[noinline]
def SpannedRecord.appendRepeatedI64_fixed64
    (record : SpannedRecord) (out : Array UInt64) :
    Except ProtoError (Array UInt64) :=
  record.appendRepeatedI64As out id

@[noinline]
def SpannedRecord.appendRepeatedI64_sfixed64
    (record : SpannedRecord) (out : Array Int64) :
    Except ProtoError (Array Int64) :=
  record.appendRepeatedI64As out fun value =>
    Int64.ofBitVec value.toBitVec

@[noinline]
def SpannedRecord.appendRepeatedI32_float
    (record : SpannedRecord) (out : Array Float32) :
    Except ProtoError (Array Float32) :=
  record.appendRepeatedI32As out Float32.ofBits

@[noinline]
def SpannedRecord.appendRepeatedI32_fixed32
    (record : SpannedRecord) (out : Array UInt32) :
    Except ProtoError (Array UInt32) :=
  record.appendRepeatedI32As out id

@[noinline]
def SpannedRecord.appendRepeatedI32_sfixed32
    (record : SpannedRecord) (out : Array Int32) :
    Except ProtoError (Array Int32) :=
  record.appendRepeatedI32As out fun value =>
    Int32.ofBitVec value.toBitVec

end Protobuf.Encoding
