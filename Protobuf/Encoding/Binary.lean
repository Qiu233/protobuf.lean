module

public import Binary
public import Protobuf.Encoding.Basic

public section

namespace Protobuf.Encoding

open Binary

inductive ProtoError where
  | truncated
  | invalidVarint
  | invalidWireType (err : String)
  | invalidBuffer (err : String)
  | missingRequiredField (err : String)
  | userError (err : String)
deriving Repr

def ProtoError.toString : ProtoError → String
  | .truncated => "proto decode error: truncated input"
  | .invalidVarint => "proto decode error: invalid varint"
  | .invalidWireType err => s!"proto decode error: invalid wire type: {err}"
  | .invalidBuffer err => s!"proto decode error: invalid buffer: {err}"
  | .missingRequiredField err => s!"proto decode error: missing required field: {err}"
  | .userError err => s!"proto decode error: {err}"

instance : ToString ProtoError := ⟨ProtoError.toString⟩

/--
The default maximum number of nested, schema-known messages accepted while
decoding.

Official protobuf runtimes use 100 as their default recursion limit.  The root
message itself does not consume this budget; each embedded message does.
-/
def defaultMessageRecursionLimit : Nat := 100

/--
Consume one level of the schema-known embedded-message recursion budget.

Length-delimited wire values are not intrinsically messages: strings, bytes,
packed scalars, and unknown fields must remain opaque.  Generated,
schema-specialized decoders therefore call this helper only when they enter a
known message field (including map-entry messages).
-/
@[always_inline]
def descendMessageRecursion (remaining : Nat) : Except ProtoError Nat :=
  if remaining = 0 then
    throw (.userError "protobuf: message recursion limit exceeded")
  else
    pure (remaining - 1)

@[always_inline]
private partial def get_varint_bytes : Get ((bs : ByteArray) ×' bs.size > 0) := do
  let rec go (acc : ByteArray) : Get ((bs : ByteArray) ×' bs.size > 0) := do
    if acc.size ≥ 10 then
      throw (.userError "protobuf: varint too long")
    let b ← getThe UInt8
    -- A protobuf varint represents an unsigned 64-bit value.  The tenth byte
    -- therefore has exactly one payload bit and may only be 0x00 or 0x01.
    if acc.size = 9 && b > 1 then
      throw (.userError "protobuf: varint overflow")
    let acc := acc.push b
    if !b.toBitVec.msb then
      return ⟨acc, by simp [acc, ByteArray.push]; unfold ByteArray.size; simp⟩
    go acc
  go (ByteArray.emptyWithCapacity 10)

@[always_inline]
partial def get_varint : Get Nat := do
  let ⟨bs, h⟩ ← get_varint_bytes
  let rec go (acc : Nat) (shift : Nat) (idx : USize) (h : idx.toNat < bs.size) : Nat :=
    let b := bs.uget idx h
    let j := idx + 1
    let acc := acc ||| ((b &&& 0x7F).toNat <<< shift)
    if h' : j.toNat < bs.size then
      go acc (shift + 7) j h'
    else
      acc
  return go 0 0 0 h

@[always_inline]
partial def put_varint (n : Nat) : Put := do
  let rec go (acc : ByteArray) (v : UInt64) : ByteArray :=
    let byte : UInt8 := UInt8.ofNat ((v &&& (0x7F : UInt64)).toNat)
    let v := v >>> 7
    if v = 0 then
      acc.push byte
    else
      go (acc.push (byte ||| (0x80 : UInt8))) v
  let bs := go (ByteArray.emptyWithCapacity 10) (UInt64.ofNat n)
  put_bytes bs

open Primitive.LE in
@[always_inline]
partial instance : Encode Record where
  put x := do
    let rec go (x : Record) : Put := do
      let putKey (wireType : Nat) : Put :=
        put_varint <| (x.fieldNum <<< 3) ||| wireType
      match x.value with
      | .GROUPED sub =>
        putKey 3 -- SGROUP
        sub.records.forM go
        putKey 4 -- EGROUP
      | .VARINT v =>
        putKey 0
        put_varint v
      | .I64 v =>
        putKey 1
        put (UInt64.ofBitVec v)
      | .LEN data =>
        putKey 2
        put_varint data.size
        put_bytes data
      | .I32 v =>
        putKey 5
        put (UInt32.ofBitVec v)
    go x

open Primitive.LE in
@[always_inline]
partial def getRecordWithRecursionBudget
    (recursionBudget : Nat) : Get Record := do
  let maxFieldNumber : Nat := (1 <<< 29) - 1
  let maxLength : Nat := (1 <<< 31) - 1
  let rec go
      (expectedEnd? : Option Nat) (remainingRecursion : Nat) :
      Get (Option Record) := do
      let key ← get_varint
      let wire_type := (key &&& 0b111)
      let num := (key >>> 3)
      if num = 0 || num > maxFieldNumber then
        throw (.userError "protobuf: invalid field number")
      match wire_type with
      | 0 =>
        let v ← get_varint
        return some ⟨num, .VARINT v⟩
      | 1 =>
        let v ← getThe UInt64
        return some ⟨num, .I64 v.toBitVec⟩
      | 2 =>
        let size ← get_varint
        if size > maxLength then
          throw (.userError "protobuf: length-delimited field exceeds 2 GiB limit")
        let bytes ← get_bytes size
        return some ⟨num, .LEN bytes⟩
      | 3 =>
        if remainingRecursion = 0 then
          throw (.userError "protobuf: group recursion limit exceeded")
        let mut rs := #[]
        repeat
          let some x ← go (some num) (remainingRecursion - 1) | break
          rs := rs.push x
        return some ⟨num, .GROUPED ⟨rs⟩⟩
      | 4 =>
        match expectedEnd? with
        | some expected =>
          if num = expected then
            return none
          else
            throw (.userError "protobuf: mismatching EGROUP field number")
        | none =>
          throw (.userError "protobuf: unexpected EGROUP")
      | 5 =>
        let v ← getThe UInt32
        return some ⟨num, .I32 v.toBitVec⟩
      | _ => throw (.userError "protobuf: invalid wire type encountered")
  match ← go none recursionBudget with
  | some r => return r
  | none =>
      throw
        (.userError
          "protobuf: internal error: a top-level record decoded as an end-group")

@[always_inline]
partial instance : Decode Record where
  get := getRecordWithRecursionBudget defaultMessageRecursionLimit

@[always_inline]
instance : Encode Message where
  put x := x.records.forM put

/--
Parse one raw wire message while allowing at most `recursionBudget` nested
legacy groups. Generated decoders pass the remaining schema-message budget
here, so known LEN messages and groups share the official recursion limit.
-/
@[always_inline]
partial def getMessageWithRecursionBudget
    (recursionBudget : Nat) : Get Message := do
  if (← remaining) > (1 <<< 31) - 1 then
    throw (.userError "protobuf: serialized message exceeds 2 GiB limit")
  let rec go (acc : Array Record) : Get (Array Record) := do
    if (← remaining) = 0 then
      return acc
    let r ← getRecordWithRecursionBudget recursionBudget
    go (acc.push r)
  Message.mk <$> go (Array.emptyWithCapacity 32)

@[always_inline]
partial instance : Decode Message where
  get := getMessageWithRecursionBudget defaultMessageRecursionLimit
