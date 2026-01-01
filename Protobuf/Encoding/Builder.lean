module

import Binary
public import Protobuf.Encoding.Basic
public import Protobuf.Encoding.Binary

public section

namespace Protobuf.Encoding

open Binary

@[always_inline]
def Message.push (msg : Message) (r : Record) : Message := {msg with records := msg.records.push r }

@[always_inline]
def Message.set (msg : Message) (fieldNum : Nat) (value : ProtoVal) : Message := msg.push { fieldNum, value }

namespace Notation

scoped notation n " <~ " val " # " msg => Message.set msg n val

scoped notation n " <~? " val " # " msg => Option.getD (Option.map (Message.set msg n) val) msg

/-- flattened repeated -/
scoped notation n " <~f " vs " # " msg => Array.foldl (init := msg) (fun acc x => Message.set acc n x) vs

end Notation

@[always_inline]
def ProtoVal.ofMessage : Message → ProtoVal := fun s => ProtoVal.LEN (Put.run 128 (put s))

@[always_inline]
def ProtoVal.ofString : String → ProtoVal := fun s => ProtoVal.LEN s.toUTF8

@[always_inline]
def ProtoVal.ofBytes : ByteArray → ProtoVal := fun s => ProtoVal.LEN s

@[always_inline]
def ProtoVal.ofBool : Bool → ProtoVal := fun x => ProtoVal.VARINT (if x then 1 else 0)

@[always_inline]
def ProtoVal.ofVarint_int32 : Int32 → ProtoVal := fun x => ProtoVal.VARINT x.toUInt32.toNat
@[always_inline]
def ProtoVal.ofVarint_uint32 : UInt32 → ProtoVal := fun x => ProtoVal.VARINT x.toNat
@[always_inline]
def ProtoVal.ofVarint_int64 : Int64 → ProtoVal := fun x => ProtoVal.VARINT x.toUInt64.toNat
@[always_inline]
def ProtoVal.ofVarint_uint64 : UInt64 → ProtoVal := fun x => ProtoVal.VARINT x.toNat
@[always_inline]
def ProtoVal.ofVarint_sint32 : Int32 → ProtoVal := fun x =>
  let y := x.toUInt32
  let n := (y <<< 1) ^^^ (y >>> 31)
  ProtoVal.VARINT n.toNat
@[always_inline]
def ProtoVal.ofVarint_sint64 : Int64 → ProtoVal := fun x =>
  let y := x.toUInt64
  let n := (y <<< 1) ^^^ (y >>> 63)
  ProtoVal.VARINT n.toNat

@[always_inline]
def ProtoVal.ofI64_double : Float → ProtoVal := fun x => ProtoVal.I64 (x.toBits.toBitVec)
@[always_inline]
def ProtoVal.ofI64_fixed64 : UInt64 → ProtoVal := fun x => ProtoVal.I64 (x.toBitVec)
@[always_inline]
def ProtoVal.ofI64_sfixed64 : Int64 → ProtoVal := fun x => ProtoVal.I64 (x.toBitVec)

@[always_inline]
def ProtoVal.ofI32_float : Float32 → ProtoVal := fun x => ProtoVal.I32 (x.toBits.toBitVec)
@[always_inline]
def ProtoVal.ofI32_fixed32 : UInt32 → ProtoVal := fun x => ProtoVal.I32 (x.toBitVec)
@[always_inline]
def ProtoVal.ofI32_sfixed32 : Int32 → ProtoVal := fun x => ProtoVal.I32 (x.toBitVec)

@[always_inline]
def ProtoVal.canBePacked : ProtoVal → Bool
  | .VARINT ..
  | .I64 ..
  | .I32 .. => true
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
  let data := Binary.Put.run 128 do
    xs.forM put_packed!
  ProtoVal.LEN data

/-- packed repeated -/
scoped notation n " <~p " vs " # " msg => Message.set msg n (ProtoVal.of_packed vs)
