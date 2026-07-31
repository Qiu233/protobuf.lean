module

public import Protobuf.Encoding.Basic
public import Protobuf.Encoding.Binary
public import Protobuf.UnvalidatedString
public import Std

public section

namespace Protobuf.Encoding

/-
Generated decoders call the accessors below once per schema field.  Their
array traversals and `Except` state machines are intentionally kept behind
`noinline` boundaries: forcing them into every generated branch multiplies
downstream code size and is slower on current Lean.  Only the tiny primitive
wire readers and ZigZag arithmetic remain forced inline.
-/

@[noinline]
def Message.filterRecords (f : Record → Bool) (msg : Message) : Array Record := msg.records.filter f

@[noinline]
def Message.getRecordsOf (msg : Message) (fieldNum : Nat) : Array Record := msg.filterRecords (fun x => x.fieldNum == fieldNum)

@[noinline]
def Message.getLastRecordOf? (msg : Message) (fieldNum : Nat) : Option Record :=
  msg.records.findRev? fun record => record.fieldNum == fieldNum

@[noinline]
def Message.getValuesOf (msg : Message) (fieldNum : Nat) : Array ProtoVal := msg.getRecordsOf fieldNum |>.map Record.value

@[noinline]
def Message.getLastValueOf? (msg : Message) (fieldNum : Nat) : Option ProtoVal :=
  msg.records.findSomeRev? fun record =>
    if record.fieldNum == fieldNum then some record.value else none

open Binary
open Primitive.LE

@[always_inline]
private def getVarint : Get ProtoVal := do
  let v ← get_varint
  return ProtoVal.VARINT v

@[noinline]
private partial def getPackedValues (getValue : Get ProtoVal) : Get (Array ProtoVal) := do
  let mut result := #[]
  repeat
    let r ← remaining
    if r == 0 then break
    let x ← getValue
    result := result.push x
  return result

local macro "throwWireType! " err:term : term => ``(throw (ProtoError.invalidWireType s!"{decl_name%}: {$err}"))
local macro "throwUserError! " err:term : term => ``(throw (ProtoError.userError s!"{decl_name%}: {$err}"))
local macro "throwInvalidBuffer! " err:term : term => ``(throw (ProtoError.invalidBuffer s!"{decl_name%}: {$err}"))

@[noinline]
def protoDecodeParseResultExcept : Except Binary.DecodeError α → Except ProtoError α
  | .ok r => pure r
  | .error .eoi => throw .truncated
  | .error (.userError e) => throwUserError! s!"error occured when parsing protobuf data: {e}"

@[noinline]
private def decodePackedWith (getValue : Get ProtoVal) (data : ByteArray) : Except ProtoError (Array ProtoVal) := do
  protoDecodeParseResultExcept (Binary.Get.run (getPackedValues getValue) data).toExcept

@[noinline]
private partial def getPackedValuesInto
    (getValue : Get α) (initial : Array α) : Get (Array α) := do
  let mut out := initial
  repeat
    let r ← remaining
    if r == 0 then break
    out := out.push (← getValue)
  return out

@[noinline]
private def decodePackedInto
    (getValue : Get α) (data : ByteArray) (initial : Array α) :
    Except ProtoError (Array α) :=
  protoDecodeParseResultExcept <|
    Binary.Get.run (getPackedValuesInto getValue initial) data |>.toExcept

@[noinline]
private def Message.concatPackedWith
    (msg : Message) (fieldNum : Nat) (getValue : Get ProtoVal) :
    Except ProtoError (Array ProtoVal) := do
  let xs := msg.getValuesOf fieldNum
  if xs.any (fun x => !x.isLEN) then
    throwWireType! "packed data must be LEN"
  let xs := xs.map fun
    | .LEN data => data
    | _ => unreachable!
  let rs ← xs.mapM (decodePackedWith getValue)
  return rs.flatten

/--
Decode packed varints without schema information.

Packed payloads do not carry their element wire type, so callers decoding
fixed-width fields must use one of the typed `getPackedI32_*`/`getPackedI64_*`
accessors instead.
-/
def Message.concatPacked (msg : Message) (fieldNum : Nat) : Except ProtoError (Array ProtoVal) :=
  msg.concatPackedWith fieldNum getVarint

/--
Retain wire values that a generated enum-extension setter must not replace.

For an open enum every compatible value belongs to the typed extension. For a
closed enum, undeclared numeric values remain unknown fields even though they
use the enum's VARINT wire type. Packed closed-enum unknowns are unpacked and
canonicalized through uint32, matching protobuf's int32 enum parsing rules.

`isKnown` is generated from the concrete enum declaration; this helper carries
no descriptors and performs no runtime schema lookup.
-/
@[noinline]
def Message.retainEnumExtensionUnknownValues
    (values : Array ProtoVal) (isRepeated isClosed : Bool)
    (isKnown : Nat → Bool) : Except ProtoError (Array ProtoVal) := do
  if !isClosed then
    return values.filter fun
      | .VARINT _ => false
      | .LEN _ => !isRepeated
      | _ => true
  let mut retained : Array ProtoVal := #[]
  for value in values do
    match value with
    | .VARINT raw =>
        if !isKnown raw then
          -- Expanded values preserve their original uint64 varint.
          retained := retained.push value
    | .LEN data =>
        if isRepeated then
          let packed ← decodePackedWith getVarint data
          for packedValue in packed do
            match packedValue with
            | .VARINT raw =>
                if !isKnown raw then
                  -- Packed enum values are interpreted as int32 before being
                  -- transferred to unknown fields.
                  retained := retained.push (.VARINT (UInt32.ofNat raw).toNat)
            | _ =>
                throwWireType! "packed enum extension contained a non-varint value"
        else
          retained := retained.push value
    | _ =>
        retained := retained.push value
  return retained

@[noinline]
def Message.getString? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option String) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    if let some v := x.isLEN? then
      let some str := String.fromUTF8? v | throwInvalidBuffer! "invalid UTF-8 data"
      return str
    throwWireType! "expected LEN"

@[noinline]
def Message.getUnvalidatedString?
    (msg : Message) (fieldNum : Nat) :
    Except ProtoError (Option Protobuf.UnvalidatedString) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    if let some v := x.isLEN? then
      return .ofBytes v
    throwWireType! "expected LEN"

@[noinline]
def Message.getBytes? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option ByteArray) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    if let some v := x.isLEN? then
      return v
    throwWireType! "expected LEN"

@[noinline]
private def decodeEmbeddedMessage
    (data : ByteArray)
    (recursionBudget : Nat := defaultMessageRecursionLimit) :
    Except ProtoError Message := do
  let childBudget ← descendMessageRecursion recursionBudget
  let r :=
    Binary.Get.run
      (getMessageWithRecursionBudget childBudget) data
  protoDecodeParseResultExcept r.toExcept

@[noinline]
def Message.getMessage?
    (msg : Message) (fieldNum : Nat)
    (recursionBudget : Nat := defaultMessageRecursionLimit) :
    Except ProtoError (Option Message) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    match x with
    | .LEN data => decodeEmbeddedMessage data recursionBudget
    | _ => throwWireType! "expected LEN"

@[noinline]
def Message.getGroup? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Message) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    match x with
    | .GROUPED sub => return sub
    | _ => throwWireType! "expected GROUPED"

@[noinline]
def Message.getBool? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Bool) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    let some v := x.isVARINT? | throwWireType! "expected VARINT"
    return v != 0

@[noinline]
def Message.getVarint? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Nat) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    let some v := x.isVARINT? | throwWireType! "expected VARINT"
    return v

@[noinline]
def Message.getI64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option (BitVec 64)) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    let some v := x.isI64? | throwWireType! "expected I64"
    return v

@[noinline]
def Message.getI32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option (BitVec 32)) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    let some v := x.isI32? | throwWireType! "expected I32"
    return v

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

@[noinline]
def Message.getVarint_int32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int32) := do
  let r ← msg.getVarint? fieldNum
  return r.map fun n => Int32.ofBitVec (UInt32.ofNat n).toBitVec

@[noinline]
def Message.getVarint_uint32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option UInt32) := do
  let r ← msg.getVarint? fieldNum
  return r.map UInt32.ofNat

@[noinline]
def Message.getVarint_int64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int64) := do
  let r ← msg.getVarint? fieldNum
  return r.map fun n => Int64.ofBitVec (UInt64.ofNat n).toBitVec

@[noinline]
def Message.getVarint_uint64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option UInt64) := do
  let r ← msg.getVarint? fieldNum
  return r.map UInt64.ofNat

@[noinline]
def Message.getVarint_sint32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int32) := do
  let r ← msg.getVarint? fieldNum
  return r.map zigzagDecode32

@[noinline]
def Message.getVarint_sint64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int64) := do
  let r ← msg.getVarint? fieldNum
  return r.map zigzagDecode64

@[noinline]
def Message.getI64_double? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Float) := do
  let r ← msg.getI64? fieldNum
  return r.map fun n => Float.ofBits (UInt64.ofBitVec n)

@[noinline]
def Message.getI64_fixed64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option UInt64) := do
  let r ← msg.getI64? fieldNum
  return r.map UInt64.ofBitVec

@[noinline]
def Message.getI64_sfixed64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int64) := do
  let r ← msg.getI64? fieldNum
  return r.map Int64.ofBitVec

@[noinline]
def Message.getI32_float? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Float32) := do
  let r ← msg.getI32? fieldNum
  return r.map fun n => Float32.ofBits (UInt32.ofBitVec n)

@[noinline]
def Message.getI32_fixed32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option UInt32) := do
  let r ← msg.getI32? fieldNum
  return r.map UInt32.ofBitVec

@[noinline]
def Message.getI32_sfixed32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int32) := do
  let r ← msg.getI32? fieldNum
  return r.map Int32.ofBitVec

/-!
Generated decoders have already dispatched on `Record.fieldNum`. These
record-level readers avoid rebuilding a singleton `Message` and searching it
again for every scalar occurrence.
-/

@[noinline]
def Record.getString (record : Record) : Except ProtoError String := do
  let .LEN data := record.value | throwWireType! "expected LEN"
  let some value := String.fromUTF8? data
    | throwInvalidBuffer! "invalid UTF-8 data"
  return value

@[noinline]
def Record.getUnvalidatedString
    (record : Record) : Except ProtoError Protobuf.UnvalidatedString := do
  let .LEN data := record.value | throwWireType! "expected LEN"
  return .ofBytes data

@[noinline]
def Record.getBytes (record : Record) : Except ProtoError ByteArray := do
  let .LEN data := record.value | throwWireType! "expected LEN"
  return data

@[noinline]
def Record.getMessage
    (record : Record)
    (recursionBudget : Nat := defaultMessageRecursionLimit) :
    Except ProtoError Message := do
  let .LEN data := record.value | throwWireType! "expected LEN"
  decodeEmbeddedMessage data recursionBudget

@[noinline]
def Record.getGroup (record : Record) : Except ProtoError Message := do
  let .GROUPED message := record.value | throwWireType! "expected GROUPED"
  return message

@[noinline]
def Record.getBool (record : Record) : Except ProtoError Bool := do
  let .VARINT value := record.value | throwWireType! "expected VARINT"
  return value != 0

@[noinline]
def Record.getVarint_int32 (record : Record) : Except ProtoError Int32 := do
  let .VARINT value := record.value | throwWireType! "expected VARINT"
  return Int32.ofBitVec (UInt32.ofNat value).toBitVec

@[noinline]
def Record.getVarint_uint32 (record : Record) : Except ProtoError UInt32 := do
  let .VARINT value := record.value | throwWireType! "expected VARINT"
  return UInt32.ofNat value

@[noinline]
def Record.getVarint_int64 (record : Record) : Except ProtoError Int64 := do
  let .VARINT value := record.value | throwWireType! "expected VARINT"
  return Int64.ofBitVec (UInt64.ofNat value).toBitVec

@[noinline]
def Record.getVarint_uint64 (record : Record) : Except ProtoError UInt64 := do
  let .VARINT value := record.value | throwWireType! "expected VARINT"
  return UInt64.ofNat value

@[noinline]
def Record.getVarint_sint32 (record : Record) : Except ProtoError Int32 := do
  let .VARINT value := record.value | throwWireType! "expected VARINT"
  return zigzagDecode32 value

@[noinline]
def Record.getVarint_sint64 (record : Record) : Except ProtoError Int64 := do
  let .VARINT value := record.value | throwWireType! "expected VARINT"
  return zigzagDecode64 value

@[noinline]
def Record.getI64_double (record : Record) : Except ProtoError Float := do
  let .I64 value := record.value | throwWireType! "expected I64"
  return Float.ofBits (UInt64.ofBitVec value)

@[noinline]
def Record.getI64_fixed64 (record : Record) : Except ProtoError UInt64 := do
  let .I64 value := record.value | throwWireType! "expected I64"
  return UInt64.ofBitVec value

@[noinline]
def Record.getI64_sfixed64 (record : Record) : Except ProtoError Int64 := do
  let .I64 value := record.value | throwWireType! "expected I64"
  return Int64.ofBitVec value

@[noinline]
def Record.getI32_float (record : Record) : Except ProtoError Float32 := do
  let .I32 value := record.value | throwWireType! "expected I32"
  return Float32.ofBits (UInt32.ofBitVec value)

@[noinline]
def Record.getI32_fixed32 (record : Record) : Except ProtoError UInt32 := do
  let .I32 value := record.value | throwWireType! "expected I32"
  return UInt32.ofBitVec value

@[noinline]
def Record.getI32_sfixed32 (record : Record) : Except ProtoError Int32 := do
  let .I32 value := record.value | throwWireType! "expected I32"
  return Int32.ofBitVec value

@[noinline]
private def Message.getPackedAs
    (msg : Message) (fieldNum : Nat) (getValue : Get α) :
    Except ProtoError (Array α) := do
  -- Decode directly into the final typed array. The schema-neutral
  -- `concatPacked` API remains available above, but generated code need not
  -- allocate ProtoVal arrays merely to map them immediately afterwards.
  let mut out := #[]
  for record in msg.records do
    if record.fieldNum == fieldNum then
      match record.value with
      | .LEN data =>
          out ← decodePackedInto getValue data out
      | _ =>
          throwWireType! "packed data must be LEN"
  return out

@[noinline]
private def Message.getPackedVarintAs
    (msg : Message) (fieldNum : Nat) (convert : Nat → α) :
    Except ProtoError (Array α) :=
  msg.getPackedAs fieldNum do
    return convert (← get_varint)

@[noinline]
private def Message.getPackedI64As
    (msg : Message) (fieldNum : Nat) (convert : UInt64 → α) :
    Except ProtoError (Array α) :=
  msg.getPackedAs fieldNum do
    return convert (← getThe UInt64)

@[noinline]
private def Message.getPackedI32As
    (msg : Message) (fieldNum : Nat) (convert : UInt32 → α) :
    Except ProtoError (Array α) :=
  msg.getPackedAs fieldNum do
    return convert (← getThe UInt32)

@[noinline]
def Message.getPackedBool
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Bool) :=
  msg.getPackedVarintAs fieldNum (· != 0)

@[noinline]
def Message.getPackedVarint_int32
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) :=
  msg.getPackedVarintAs fieldNum fun n =>
    Int32.ofBitVec (UInt32.ofNat n).toBitVec

@[noinline]
def Message.getPackedVarint_uint32
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) :=
  msg.getPackedVarintAs fieldNum UInt32.ofNat

@[noinline]
def Message.getPackedVarint_int64
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) :=
  msg.getPackedVarintAs fieldNum fun n =>
    Int64.ofBitVec (UInt64.ofNat n).toBitVec

@[noinline]
def Message.getPackedVarint_uint64
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) :=
  msg.getPackedVarintAs fieldNum UInt64.ofNat

@[noinline]
def Message.getPackedVarint_sint32
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) :=
  msg.getPackedVarintAs fieldNum zigzagDecode32

@[noinline]
def Message.getPackedVarint_sint64
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) :=
  msg.getPackedVarintAs fieldNum zigzagDecode64

@[noinline]
def Message.getPackedI64_double
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float) :=
  msg.getPackedI64As fieldNum Float.ofBits

@[noinline]
def Message.getPackedI64_fixed64
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) :=
  msg.getPackedI64As fieldNum id

@[noinline]
def Message.getPackedI64_sfixed64
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) :=
  msg.getPackedI64As fieldNum fun n => Int64.ofBitVec n.toBitVec

@[noinline]
def Message.getPackedI32_float
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float32) :=
  msg.getPackedI32As fieldNum Float32.ofBits

@[noinline]
def Message.getPackedI32_fixed32
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) :=
  msg.getPackedI32As fieldNum id

@[noinline]
def Message.getPackedI32_sfixed32
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) :=
  msg.getPackedI32As fieldNum fun n => Int32.ofBitVec n.toBitVec

@[noinline]
private def Message.getExpandedVarint (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Nat) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x => do
    let some v := x.isVARINT? | throwWireType! "expected VARINT"
    return v

@[noinline]
private def Message.getExpandedI64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array (BitVec 64)) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x => do
    let some v := x.isI64? | throwWireType! "expected I64"
    return v

@[noinline]
private def Message.getExpandedI32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array (BitVec 32)) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x => do
    let some v := x.isI32? | throwWireType! "expected I32"
    return v

@[noinline]
private def Message.getExpandedLen (msg : Message) (fieldNum : Nat) : Except ProtoError (Array ByteArray) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x => do
    let some v := x.isLEN? | throwWireType! "expected LEN"
    return v

@[noinline]
def Message.getExpandedString (msg : Message) (fieldNum : Nat) : Except ProtoError (Array String) := do
  let xs ← msg.getExpandedLen fieldNum
  xs.mapM fun x => (String.fromUTF8? x).getDM (throwInvalidBuffer! "invalid UTF-8 data")

@[noinline]
def Message.getExpandedUnvalidatedString
    (msg : Message) (fieldNum : Nat) :
    Except ProtoError (Array Protobuf.UnvalidatedString) := do
  let xs ← msg.getExpandedLen fieldNum
  return xs.map Protobuf.UnvalidatedString.ofBytes

@[noinline]
def Message.getExpandedBytes (msg : Message) (fieldNum : Nat) : Except ProtoError (Array ByteArray) := do
  msg.getExpandedLen fieldNum

@[noinline]
def Message.getExpandedMessage
    (msg : Message) (fieldNum : Nat)
    (recursionBudget : Nat := defaultMessageRecursionLimit) :
    Except ProtoError (Array Message) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x => do
    match x with
    | .LEN data => decodeEmbeddedMessage data recursionBudget
    | _ => throwWireType! "expected LEN"

@[noinline]
def Message.getExpandedGroup (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Message) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x => do
    match x with
    | .GROUPED sub => return sub
    | _ => throwWireType! "expected GROUPED"

@[noinline]
def Message.getExpandedBool (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Bool) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map (fun v => v != 0)

@[noinline]
def Message.getExpandedVarint_int32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map fun n => Int32.ofBitVec (UInt32.ofNat n).toBitVec

@[noinline]
def Message.getExpandedVarint_uint32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map UInt32.ofNat

@[noinline]
def Message.getExpandedVarint_int64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map fun n => Int64.ofBitVec (UInt64.ofNat n).toBitVec

@[noinline]
def Message.getExpandedVarint_uint64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map UInt64.ofNat

@[noinline]
def Message.getExpandedVarint_sint32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map zigzagDecode32

@[noinline]
def Message.getExpandedVarint_sint64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map zigzagDecode64

@[noinline]
def Message.getExpandedI64_double (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float) := do
  let xs ← msg.getExpandedI64 fieldNum
  return xs.map fun n => Float.ofBits (UInt64.ofBitVec n)

@[noinline]
def Message.getExpandedI64_fixed64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) := do
  let xs ← msg.getExpandedI64 fieldNum
  return xs.map UInt64.ofBitVec

@[noinline]
def Message.getExpandedI64_sfixed64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getExpandedI64 fieldNum
  return xs.map Int64.ofBitVec

@[noinline]
def Message.getExpandedI32_float (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float32) := do
  let xs ← msg.getExpandedI32 fieldNum
  return xs.map fun n => Float32.ofBits (UInt32.ofBitVec n)

@[noinline]
def Message.getExpandedI32_fixed32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) := do
  let xs ← msg.getExpandedI32 fieldNum
  return xs.map UInt32.ofBitVec

@[noinline]
def Message.getExpandedI32_sfixed32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getExpandedI32 fieldNum
  return xs.map Int32.ofBitVec

@[noinline]
private def Record.appendRepeatedAs
    (record : Record) (getPackedValue : Get α)
    (getExpandedValue : ProtoVal → Option α) :
    Array α → Except ProtoError (Array α) := fun out => do
  match record.value with
  | .LEN data =>
      decodePackedInto getPackedValue data out
  | value =>
      let some value := getExpandedValue value
        | throwWireType! "value of repeated field has the wrong wire type"
      return out.push value

@[noinline]
private def Message.getRepeatedAs
    (msg : Message) (fieldNum : Nat) (getPackedValue : Get α)
    (getExpandedValue : ProtoVal → Option α) :
    Except ProtoError (Array α) := do
  -- Preserve the interleaving of packed and expanded occurrences while
  -- growing one final typed accumulator.
  let mut out := #[]
  for record in msg.records do
    if record.fieldNum == fieldNum then
      out ← record.appendRepeatedAs getPackedValue getExpandedValue out
  return out

@[noinline]
private def Message.getRepeatedVarintAs
    (msg : Message) (fieldNum : Nat) (convert : Nat → α) :
    Except ProtoError (Array α) :=
  msg.getRepeatedAs fieldNum
    (do return convert (← get_varint))
    (fun
      | .VARINT value => some (convert value)
      | _ => none)

@[noinline]
private def Message.getRepeatedI64As
    (msg : Message) (fieldNum : Nat) (convert : UInt64 → α) :
    Except ProtoError (Array α) :=
  msg.getRepeatedAs fieldNum
    (do return convert (← getThe UInt64))
    (fun
      | .I64 value => some (convert (UInt64.ofBitVec value))
      | _ => none)

@[noinline]
private def Message.getRepeatedI32As
    (msg : Message) (fieldNum : Nat) (convert : UInt32 → α) :
    Except ProtoError (Array α) :=
  msg.getRepeatedAs fieldNum
    (do return convert (← getThe UInt32))
    (fun
      | .I32 value => some (convert (UInt32.ofBitVec value))
      | _ => none)

@[noinline]
def Record.appendRepeatedBool
    (record : Record) (out : Array Bool) : Except ProtoError (Array Bool) :=
  record.appendRepeatedAs
    (do return (← get_varint) != 0)
    (fun
      | .VARINT value => some (value != 0)
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedString
    (record : Record) (out : Array String) :
    Except ProtoError (Array String) := do
  return out.push (← record.getString)

@[noinline]
def Record.appendRepeatedUnvalidatedString
    (record : Record) (out : Array Protobuf.UnvalidatedString) :
    Except ProtoError (Array Protobuf.UnvalidatedString) := do
  return out.push (← record.getUnvalidatedString)

@[noinline]
def Record.appendRepeatedBytes
    (record : Record) (out : Array ByteArray) :
    Except ProtoError (Array ByteArray) := do
  return out.push (← record.getBytes)

@[noinline]
def Record.appendRepeatedVarint_int32
    (record : Record) (out : Array Int32) :
    Except ProtoError (Array Int32) :=
  let convert := fun n => Int32.ofBitVec (UInt32.ofNat n).toBitVec
  record.appendRepeatedAs
    (do return convert (← get_varint))
    (fun
      | .VARINT value => some (convert value)
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedVarint_uint32
    (record : Record) (out : Array UInt32) :
    Except ProtoError (Array UInt32) :=
  record.appendRepeatedAs
    (do return UInt32.ofNat (← get_varint))
    (fun
      | .VARINT value => some (UInt32.ofNat value)
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedVarint_int64
    (record : Record) (out : Array Int64) :
    Except ProtoError (Array Int64) :=
  let convert := fun n => Int64.ofBitVec (UInt64.ofNat n).toBitVec
  record.appendRepeatedAs
    (do return convert (← get_varint))
    (fun
      | .VARINT value => some (convert value)
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedVarint_uint64
    (record : Record) (out : Array UInt64) :
    Except ProtoError (Array UInt64) :=
  record.appendRepeatedAs
    (do return UInt64.ofNat (← get_varint))
    (fun
      | .VARINT value => some (UInt64.ofNat value)
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedVarint_sint32
    (record : Record) (out : Array Int32) :
    Except ProtoError (Array Int32) :=
  record.appendRepeatedAs
    (do return zigzagDecode32 (← get_varint))
    (fun
      | .VARINT value => some (zigzagDecode32 value)
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedVarint_sint64
    (record : Record) (out : Array Int64) :
    Except ProtoError (Array Int64) :=
  record.appendRepeatedAs
    (do return zigzagDecode64 (← get_varint))
    (fun
      | .VARINT value => some (zigzagDecode64 value)
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedI64_double
    (record : Record) (out : Array Float) :
    Except ProtoError (Array Float) :=
  record.appendRepeatedAs
    (do return Float.ofBits (← getThe UInt64))
    (fun
      | .I64 value => some (Float.ofBits (UInt64.ofBitVec value))
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedI64_fixed64
    (record : Record) (out : Array UInt64) :
    Except ProtoError (Array UInt64) :=
  record.appendRepeatedAs
    (getThe UInt64)
    (fun
      | .I64 value => some (UInt64.ofBitVec value)
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedI64_sfixed64
    (record : Record) (out : Array Int64) :
    Except ProtoError (Array Int64) :=
  record.appendRepeatedAs
    (do return Int64.ofBitVec (← getThe UInt64).toBitVec)
    (fun
      | .I64 value => some (Int64.ofBitVec value)
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedI32_float
    (record : Record) (out : Array Float32) :
    Except ProtoError (Array Float32) :=
  record.appendRepeatedAs
    (do return Float32.ofBits (← getThe UInt32))
    (fun
      | .I32 value => some (Float32.ofBits (UInt32.ofBitVec value))
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedI32_fixed32
    (record : Record) (out : Array UInt32) :
    Except ProtoError (Array UInt32) :=
  record.appendRepeatedAs
    (getThe UInt32)
    (fun
      | .I32 value => some (UInt32.ofBitVec value)
      | _ => none)
    out

@[noinline]
def Record.appendRepeatedI32_sfixed32
    (record : Record) (out : Array Int32) :
    Except ProtoError (Array Int32) :=
  record.appendRepeatedAs
    (do return Int32.ofBitVec (← getThe UInt32).toBitVec)
    (fun
      | .I32 value => some (Int32.ofBitVec value)
      | _ => none)
    out

@[noinline]
def Message.getRepeatedBool
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Bool) :=
  msg.getRepeatedVarintAs fieldNum (· != 0)

@[noinline]
def Message.getRepeatedVarint_int32
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) :=
  msg.getRepeatedVarintAs fieldNum fun n =>
    Int32.ofBitVec (UInt32.ofNat n).toBitVec

@[noinline]
def Message.getRepeatedVarint_uint32
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) :=
  msg.getRepeatedVarintAs fieldNum UInt32.ofNat

@[noinline]
def Message.getRepeatedVarint_int64
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) :=
  msg.getRepeatedVarintAs fieldNum fun n =>
    Int64.ofBitVec (UInt64.ofNat n).toBitVec

@[noinline]
def Message.getRepeatedVarint_uint64
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) :=
  msg.getRepeatedVarintAs fieldNum UInt64.ofNat

@[noinline]
def Message.getRepeatedVarint_sint32
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) :=
  msg.getRepeatedVarintAs fieldNum zigzagDecode32

@[noinline]
def Message.getRepeatedVarint_sint64
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) :=
  msg.getRepeatedVarintAs fieldNum zigzagDecode64

@[noinline]
def Message.getRepeatedI64_double
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float) :=
  msg.getRepeatedI64As fieldNum Float.ofBits

@[noinline]
def Message.getRepeatedI64_fixed64
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) :=
  msg.getRepeatedI64As fieldNum id

@[noinline]
def Message.getRepeatedI64_sfixed64
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) :=
  msg.getRepeatedI64As fieldNum fun n => Int64.ofBitVec n.toBitVec

@[noinline]
def Message.getRepeatedI32_float
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float32) :=
  msg.getRepeatedI32As fieldNum Float32.ofBits

@[noinline]
def Message.getRepeatedI32_fixed32
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) :=
  msg.getRepeatedI32As fieldNum id

@[noinline]
def Message.getRepeatedI32_sfixed32
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) :=
  msg.getRepeatedI32As fieldNum fun n => Int32.ofBitVec n.toBitVec
