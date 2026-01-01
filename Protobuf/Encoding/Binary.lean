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

@[always_inline]
private partial def get_varint_bytes : Get ((bs : ByteArray) ×' bs.size > 0) := do
  let rec go (acc : ByteArray) : Get ((bs : ByteArray) ×' bs.size > 0) := do
    if acc.size ≥ 10 then
      throw (.userError "protobuf: varint too long")
    let b ← getThe UInt8
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
      let wireType : ProtoVal → Nat
        | .VARINT .. => 0
        | .I64 .. => 1
        | .LEN .. => 2
        | .GROUPED .. => unreachable!
        | .I32 .. => 5
      match x.value with
      | .GROUPED sub =>
        put_varint <| (x.fieldNum <<< 3) ||| 3 -- SGROUP
        sub.records.forM go
        put_varint <| (x.fieldNum <<< 3) ||| 4 -- EGROUP
      | _ =>
        let v : Nat := (x.fieldNum <<< 3) ||| (wireType x.value)
        put_varint v
        match x.value with
        | .VARINT v => put_varint v
        | .I64 v => put (UInt64.ofBitVec v)
        | .I32 v => put (UInt32.ofBitVec v)
        | .GROUPED _ => unreachable!
        | .LEN data =>
          put_varint data.size
          put_bytes data
    go x

open Primitive.LE in
@[always_inline]
partial instance : Decode Record where
  get := do
    let rec go : Get (Option Record) := do
      let key ← get_varint
      let wire_type := (key &&& 0b111)
      let num := (key >>> 3)
      match wire_type with
      | 0 =>
        let v ← get_varint
        return some ⟨num, .VARINT v⟩
      | 1 =>
        let v ← getThe UInt64
        return some ⟨num, .I64 v.toBitVec⟩
      | 2 =>
        let size ← get_varint
        let bytes ← get_bytes size
        return some ⟨num, .LEN bytes⟩
      | 3 =>
        let mut rs := #[]
        repeat
          let some x ← go | break
          rs := rs.push x
        return some ⟨num, .GROUPED ⟨rs⟩⟩
      | 4 => return none
      | 5 =>
        let v ← getThe UInt32
        return some ⟨num, .I32 v.toBitVec⟩
      | _ => throw (.userError "protobuf: invalid wire type encountered")
    let some r ← go | throw (.userError "protobuf: unexpected EGROUP")
    return r

@[always_inline]
instance : Encode Message where
  put x := x.records.forM put

@[always_inline]
partial instance : Decode Message where
  get := do
    let rec go (acc : Array Record) : Get (Array Record) := do
      if (← remaining) = 0 then
        return acc
      let r ← getThe Record
      go (acc.push r)
    Message.mk <$> go (Array.emptyWithCapacity 32)
