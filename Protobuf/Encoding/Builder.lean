module

import Binary
public import Protobuf.Encoding.Basic
public import Protobuf.Encoding.Binary
import Std

public section

namespace Protobuf.Encoding

open Binary

@[always_inline]
def Message.push (msg : Message) (r : Record) : Message := {msg with records := msg.records.push r }

@[always_inline]
def Message.set (msg : Message) (fieldNum : Nat) (value : ProtoVal) : Message := msg.push { fieldNum, value }

@[always_inline]
def ProtoVal.ofMessage : Message → Except Protobuf.Encoding.ProtoError ProtoVal := fun s => return ProtoVal.LEN (Put.run (put s))

@[always_inline]
def ProtoVal.ofString : String → Except Protobuf.Encoding.ProtoError ProtoVal := fun s => return ProtoVal.LEN s.toUTF8

@[always_inline]
def ProtoVal.ofBytes : ByteArray → Except Protobuf.Encoding.ProtoError ProtoVal := fun s => return ProtoVal.LEN s

@[always_inline]
def ProtoVal.ofBool : Bool → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT (if x then 1 else 0)

@[always_inline]
def ProtoVal.ofVarint_int32 : Int32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT x.toUInt32.toNat
@[always_inline]
def ProtoVal.ofVarint_uint32 : UInt32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT x.toNat
@[always_inline]
def ProtoVal.ofVarint_int64 : Int64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT x.toUInt64.toNat
@[always_inline]
def ProtoVal.ofVarint_uint64 : UInt64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT x.toNat
@[always_inline]
def ProtoVal.ofVarint_sint32 : Int32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x =>
  let y := x.toUInt32
  let n := (y <<< 1) ^^^ (y >>> 31)
  return ProtoVal.VARINT n.toNat
@[always_inline]
def ProtoVal.ofVarint_sint64 : Int64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x =>
  let y := x.toUInt64
  let n := (y <<< 1) ^^^ (y >>> 63)
  return ProtoVal.VARINT n.toNat

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
@[always_inline]
private def put_packed! : ProtoVal → Put
  | .VARINT x => put_varint x
  | .I64 x => put (UInt64.ofBitVec x)
  | .I32 x => put (UInt32.ofBitVec x)
  | _ => unreachable!

@[always_inline]
def ProtoVal.of_packed : Array ProtoVal → ProtoVal := fun xs =>
  assert! xs.all ProtoVal.canBePacked
  let data := Binary.Put.run do
    xs.forM put_packed!
  ProtoVal.LEN data

@[always_inline]
def Message.wire_map (msg : Message) : Std.HashMap Nat (Array ProtoVal) → Message := fun m =>
  let xs := m.toArray.map fun (n, xs) => xs.map fun x => Record.mk n x
  {msg with records := msg.records.append xs.flatten}

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
  pure (Protobuf.Encoding.Message.set msg n (Protobuf.Encoding.ProtoVal.of_packed xs))

set_option quotPrecheck true

end Notation
