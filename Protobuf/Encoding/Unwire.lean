module

public import Protobuf.Encoding.Basic
public import Protobuf.Encoding.Binary
public import Std

public section

namespace Protobuf.Encoding

@[specialize, always_inline]
def Message.filterRecords (f : Record → Bool) (msg : Message) : Array Record := msg.records.filter f

@[always_inline]
def Message.getRecordsOf (msg : Message) (fieldNum : Nat) : Array Record := msg.filterRecords (fun x => x.fieldNum == fieldNum)

@[always_inline]
def Message.getLastRecordOf? (msg : Message) (fieldNum : Nat) : Option Record := msg.records.reverse.find? (fun x => x.fieldNum == fieldNum)

@[always_inline]
def Message.getValuesOf (msg : Message) (fieldNum : Nat) : Array ProtoVal := msg.getRecordsOf fieldNum |>.map Record.value

@[always_inline]
def Message.getLastValueOf? (msg : Message) (fieldNum : Nat) : Option ProtoVal := msg.records.reverse.find? (fun x => x.fieldNum == fieldNum) |>.map Record.value

open Binary
open Primitive.LE

@[always_inline]
private def getVarint : Get ProtoVal := do
  let v ← get_varint
  return ProtoVal.VARINT v

@[always_inline]
private def getI32 : Get ProtoVal := do
  let v ← getThe UInt32
  return ProtoVal.I32 v.toBitVec

@[always_inline]
private def getI64 : Get ProtoVal := do
  let v ← getThe UInt64
  return ProtoVal.I64 v.toBitVec

@[always_inline]
private partial def getPackedValue : Get ProtoVal := getVarint <|> getI32 <|> getI64

@[always_inline]
private partial def getPackedValues : Get (Array ProtoVal) := do
  let mut result := #[]
  repeat
    let r ← remaining
    if r == 0 then break
    let x ← getPackedValue
    result := result.push x
  return result

local macro "throwWireType! " err:term : term => ``(throw (ProtoDecodeError.invalidWireType s!"{decl_name%}: {$err}"))
local macro "throwUserError! " err:term : term => ``(throw (ProtoDecodeError.userError s!"{decl_name%}: {$err}"))
local macro "throwInvalidBuffer! " err:term : term => ``(throw (ProtoDecodeError.invalidBuffer s!"{decl_name%}: {$err}"))

def protoDecodeParseResultExcept : Except Binary.DecodeError α → Except ProtoDecodeError α
  | .ok r => pure r
  | .error .eoi => throw .truncated
  | .error (.userError e) => throwUserError! s!"error occured when parsing protobuf data: {e}"

def Message.concatPacked (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array ProtoVal) := do
  let xs := msg.getValuesOf fieldNum
  if xs.any (fun x => x.wireType != 2) then
    throwWireType! "packed data must be LEN"
  let xs := xs.map fun
    | .LEN data => data
    | _ => unreachable!
  let ys := xs.map fun x =>
    (Binary.Get.run getPackedValues x).toExcept
  let rs ← ys.mapM protoDecodeParseResultExcept
  return rs.flatten

@[always_inline]
def Message.getString? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option String) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    if let some v := x.isLEN? then
      let some str := String.fromUTF8? v | throwInvalidBuffer! "invalid UTF-8 data"
      return str
    throwWireType! "expected LEN"

@[always_inline]
def Message.getBytes? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option ByteArray) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    if let some v := x.isLEN? then
      return v
    throwWireType! "expected LEN"

@[always_inline]
def Message.getBool? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option Bool) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    let some v := x.isVARINT? | throwWireType! "expected VARINT"
    return v != 0

@[always_inline]
def Message.getRepeatedNonPacked (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array ProtoVal) := do
  let xs := msg.getValuesOf fieldNum
  if xs.size == 0 then return #[]
  let ks := xs.groupByKey ProtoVal.wireType
  if ks.size > 1 then
    throwWireType! "values of repeated field have more than one wire type"
  return xs

@[always_inline]
def Message.getVarint? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option Nat) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x =>
    match x.isVARINT? with
    | some v => return v
    | none => throwWireType! "expected VARINT"

@[always_inline]
def Message.getI64? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option (BitVec 64)) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x =>
    match x.isI64? with
    | some v => return v
    | none => throwWireType! "expected I64"

@[always_inline]
def Message.getI32? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option (BitVec 32)) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x =>
    match x.isI32? with
    | some v => return v
    | none => throwWireType! "expected I32"

@[always_inline]
private def zigzagDecode32 (n : Nat) : Int32 :=
  let y : UInt32 := UInt32.ofNat n
  let mask : UInt32 := 0 - (y &&& 1)
  let z : UInt32 := (y >>> 1) ^^^ mask
  Int32.ofBitVec z.toBitVec

@[always_inline]
private def zigzagDecode64 (n : Nat) : Int64 :=
  let y : UInt64 := UInt64.ofNat n
  let mask : UInt64 := 0 - (y &&& 1)
  let z : UInt64 := (y >>> 1) ^^^ mask
  Int64.ofBitVec z.toBitVec

@[always_inline]
def Message.getVarint_int32? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option Int32) := do
  let r ← msg.getVarint? fieldNum
  return r.map fun n => Int32.ofBitVec (UInt32.ofNat n).toBitVec

@[always_inline]
def Message.getVarint_uint32? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option UInt32) := do
  let r ← msg.getVarint? fieldNum
  return r.map UInt32.ofNat

@[always_inline]
def Message.getVarint_int64? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option Int64) := do
  let r ← msg.getVarint? fieldNum
  return r.map fun n => Int64.ofBitVec (UInt64.ofNat n).toBitVec

@[always_inline]
def Message.getVarint_uint64? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option UInt64) := do
  let r ← msg.getVarint? fieldNum
  return r.map UInt64.ofNat

@[always_inline]
def Message.getVarint_sint32? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option Int32) := do
  let r ← msg.getVarint? fieldNum
  return r.map zigzagDecode32

@[always_inline]
def Message.getVarint_sint64? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option Int64) := do
  let r ← msg.getVarint? fieldNum
  return r.map zigzagDecode64

@[always_inline]
def Message.getI64_double? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option Float) := do
  let r ← msg.getI64? fieldNum
  return r.map fun n => Float.ofBits (UInt64.ofBitVec n)

@[always_inline]
def Message.getI64_fixed64? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option UInt64) := do
  let r ← msg.getI64? fieldNum
  return r.map UInt64.ofBitVec

@[always_inline]
def Message.getI64_sfixed64? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option Int64) := do
  let r ← msg.getI64? fieldNum
  return r.map Int64.ofBitVec

@[always_inline]
def Message.getI32_float? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option Float32) := do
  let r ← msg.getI32? fieldNum
  return r.map fun n => Float32.ofBits (UInt32.ofBitVec n)

@[always_inline]
def Message.getI32_fixed32? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option UInt32) := do
  let r ← msg.getI32? fieldNum
  return r.map UInt32.ofBitVec

@[always_inline]
def Message.getI32_sfixed32? (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Option Int32) := do
  let r ← msg.getI32? fieldNum
  return r.map Int32.ofBitVec

@[always_inline]
private def Message.getPackedVarint (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Nat) := do
  let xs ← msg.concatPacked fieldNum
  xs.mapM fun x =>
    match x.isVARINT? with
    | some v => return v
    | none => throwWireType! "expected packed VARINT"

@[always_inline]
private def Message.getPackedI64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array (BitVec 64)) := do
  let xs ← msg.concatPacked fieldNum
  xs.mapM fun x =>
    match x.isI64? with
    | some v => return v
    | none => throwWireType! "expected packed I64"

@[always_inline]
private def Message.getPackedI32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array (BitVec 32)) := do
  let xs ← msg.concatPacked fieldNum
  xs.mapM fun x =>
    match x.isI32? with
    | some v => return v
    | none => throwWireType! "expected packed I32"

@[always_inline]
def Message.getPackedBool (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Bool) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map (fun v => v != 0)

@[always_inline]
def Message.getPackedVarint_int32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int32) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map fun n => Int32.ofBitVec (UInt32.ofNat n).toBitVec

@[always_inline]
def Message.getPackedVarint_uint32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array UInt32) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map UInt32.ofNat

@[always_inline]
def Message.getPackedVarint_int64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int64) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map fun n => Int64.ofBitVec (UInt64.ofNat n).toBitVec

@[always_inline]
def Message.getPackedVarint_uint64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array UInt64) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map UInt64.ofNat

@[always_inline]
def Message.getPackedVarint_sint32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int32) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map zigzagDecode32

@[always_inline]
def Message.getPackedVarint_sint64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int64) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map zigzagDecode64

@[always_inline]
def Message.getPackedI64_double (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Float) := do
  let xs ← msg.getPackedI64 fieldNum
  return xs.map fun n => Float.ofBits (UInt64.ofBitVec n)

@[always_inline]
def Message.getPackedI64_fixed64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array UInt64) := do
  let xs ← msg.getPackedI64 fieldNum
  return xs.map UInt64.ofBitVec

@[always_inline]
def Message.getPackedI64_sfixed64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int64) := do
  let xs ← msg.getPackedI64 fieldNum
  return xs.map Int64.ofBitVec

@[always_inline]
def Message.getPackedI32_float (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Float32) := do
  let xs ← msg.getPackedI32 fieldNum
  return xs.map fun n => Float32.ofBits (UInt32.ofBitVec n)

@[always_inline]
def Message.getPackedI32_fixed32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array UInt32) := do
  let xs ← msg.getPackedI32 fieldNum
  return xs.map UInt32.ofBitVec

@[always_inline]
def Message.getPackedI32_sfixed32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int32) := do
  let xs ← msg.getPackedI32 fieldNum
  return xs.map Int32.ofBitVec

@[always_inline]
private def Message.getRepeatedVarint (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Nat) := do
  let xs ← msg.getRepeatedNonPacked fieldNum
  xs.mapM fun x =>
    match x.isVARINT? with
    | some v => return v
    | none => throwWireType! "expected VARINT"

@[always_inline]
private def Message.getRepeatedI64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array (BitVec 64)) := do
  let xs ← msg.getRepeatedNonPacked fieldNum
  xs.mapM fun x =>
    match x.isI64? with
    | some v => return v
    | none => throwWireType! "expected I64"

@[always_inline]
private def Message.getRepeatedI32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array (BitVec 32)) := do
  let xs ← msg.getRepeatedNonPacked fieldNum
  xs.mapM fun x =>
    match x.isI32? with
    | some v => return v
    | none => throwWireType! "expected I32"

@[always_inline]
private def Message.getRepeatedLen (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array ByteArray) := do
  let xs ← msg.getRepeatedNonPacked fieldNum
  xs.mapM fun x =>
    match x.isLEN? with
    | some v => return v
    | none => throwWireType! "expected LEN"

@[always_inline]
def Message.getRepeatedString (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array String) := do
  let xs ← msg.getRepeatedLen fieldNum
  xs.mapM fun x => (String.fromUTF8? x).getDM (throwInvalidBuffer! "invalid UTF-8 data")

@[always_inline]
def Message.getRepeatedBytes (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array ByteArray) := do
  msg.getRepeatedLen fieldNum

@[always_inline]
def Message.getRepeatedBool (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Bool) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map (fun v => v != 0)

@[always_inline]
def Message.getRepeatedVarint_int32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int32) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map fun n => Int32.ofBitVec (UInt32.ofNat n).toBitVec

@[always_inline]
def Message.getRepeatedVarint_uint32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array UInt32) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map UInt32.ofNat

@[always_inline]
def Message.getRepeatedVarint_int64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int64) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map fun n => Int64.ofBitVec (UInt64.ofNat n).toBitVec

@[always_inline]
def Message.getRepeatedVarint_uint64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array UInt64) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map UInt64.ofNat

@[always_inline]
def Message.getRepeatedVarint_sint32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int32) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map zigzagDecode32

@[always_inline]
def Message.getRepeatedVarint_sint64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int64) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map zigzagDecode64

@[always_inline]
def Message.getRepeatedI64_double (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Float) := do
  let xs ← msg.getRepeatedI64 fieldNum
  return xs.map fun n => Float.ofBits (UInt64.ofBitVec n)

@[always_inline]
def Message.getRepeatedI64_fixed64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array UInt64) := do
  let xs ← msg.getRepeatedI64 fieldNum
  return xs.map UInt64.ofBitVec

@[always_inline]
def Message.getRepeatedI64_sfixed64 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int64) := do
  let xs ← msg.getRepeatedI64 fieldNum
  return xs.map Int64.ofBitVec

@[always_inline]
def Message.getRepeatedI32_float (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Float32) := do
  let xs ← msg.getRepeatedI32 fieldNum
  return xs.map fun n => Float32.ofBits (UInt32.ofBitVec n)

@[always_inline]
def Message.getRepeatedI32_fixed32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array UInt32) := do
  let xs ← msg.getRepeatedI32 fieldNum
  return xs.map UInt32.ofBitVec

@[always_inline]
def Message.getRepeatedI32_sfixed32 (msg : Message) (fieldNum : Nat) : Except ProtoDecodeError (Array Int32) := do
  let xs ← msg.getRepeatedI32 fieldNum
  return xs.map Int32.ofBitVec
