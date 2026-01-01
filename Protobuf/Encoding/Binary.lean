module

public import Binary
public import Protobuf.Encoding.Basic

public section

namespace Protobuf.Encoding

open Binary

@[always_inline]
private def get_varint_bytes : Get ByteArray := do
  let mut bs := ByteArray.emptyWithCapacity 4 -- TODO: maybe another value?
  let mut count := 0
  repeat
    let b ← getThe UInt8
    bs := bs.push b
    count := count + 1
    if count > 10 then
      throw (.userError "protobuf: varint too long")
  until !b.toBitVec.msb
  return bs

@[always_inline]
def get_varint : Get Nat := do
  let bs ← get_varint_bytes
  let shifts := Array.range' 0 bs.size 7
  return runST fun σ => do
    let v ← ST.mkRef (σ := σ) 0
    _ ← bs.data.zipWithM (bs := shifts) fun b shift => do
      v.modify fun x => (x ||| ((b &&& 0x7F).toNat <<< shift))
    v.get

def put_varint (n : Nat) : Put := do
  let bv := BitVec.ofNat 64 n
  let bv := bv.extractLsb' 0 80 -- 10 bytes
  let mut bs : Array Bool := #[]
  for i in [0:80] do
    bs := bs.push bv[i]!
  let mut cs := bs.toList
  let mut es := #[]
  repeat
    let (l, r) := cs.splitAt 7
    cs := r
    let stop := r.all (· == false)
    if stop then
      es := es.push (l ++ [false])
      break
    else
      es := es.push (l ++ [true])
  let ts := es.map fun e =>
    if h : e.length = 8 then
      h ▸ BitVec.ofBoolListLE e
    else
      unreachable!
  let ts := ts.map UInt8.ofBitVec
  put_bytes ⟨ts⟩

open Primitive.LE in
@[always_inline]
instance : Encode Record where
  put x := do
    let wire_type : Nat := match x.value with
      | .VARINT _ => 0
      | .I64 _ => 1
      | .LEN _ => 2
      | .I32 _ => 5
    let v : Nat := (x.fieldNum <<< 3) ||| wire_type
    put_varint v
    match x.value with
    | .VARINT v => put_varint v
    | .I64 v => put (UInt64.ofBitVec v)
    | .I32 v => put (UInt32.ofBitVec v)
    | .LEN data =>
      let size := data.size
      put_varint size
      put_bytes data

open Primitive.LE in
@[always_inline]
instance : Decode Record where
  get := do
    let key ← get_varint
    let wire_type := (key &&& 0b111)
    let num := (key >>> 3)
    match wire_type with
    | 0 =>
      let v ← get_varint
      return ⟨num, .VARINT v⟩
    | 1 =>
      let v ← getThe UInt64
      return ⟨num, .I64 v.toBitVec⟩
    | 2 =>
      let size ← get_varint
      let bytes ← get_bytes size
      return ⟨num, .LEN bytes⟩
    | 5 =>
      let v ← getThe UInt32
      return ⟨num, .I32 v.toBitVec⟩
    | _ => throw (.userError "protobuf: invalid wire type encountered")

@[always_inline]
instance : Encode Message where
  put x := x.records.forM put

@[always_inline]
instance : Decode Message where
  get := do
    let mut rs := #[]
    while True do
      let r ←
        try getThe Record
        catch e =>
          match e with
          | .eoi => break -- TODO: check the position
          | _ => throw e
      rs := rs.push r
    return Message.mk rs
