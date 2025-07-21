import Protobuf.Encoding
import Protobuf.Encoding.Pretty
import Protobuf.Class

namespace Protobuf

open Protobuf.Encoding
open Binary

#eval Get.run (getThe Message) hex!"089601" |>.toExcept

#eval Get.run (getThe Message) hex!"0a06616263313233" |>.toExcept

#eval Get.run get_varint ⟨#[0b10010110, 0b00000001]⟩ |>.toExcept

#eval Put.run 128 <| put_varint 150

#eval Put.run 128 <| put_varint (-2 : Int64).toUInt64.toNat

#eval ((0x7FFFFFFF : Int32) <<< 1).xor ((0x7FFFFFFF : Int32) >>> 31)

def from_sint32 (x : Int32) : Nat := UInt32.toNat <| Int32.toUInt32 <| (x <<< 1).xor (x >>> 31)
def from_sint64 (x : Int64) : Nat := UInt64.toNat <| Int64.toUInt64 <| (x <<< 1).xor (x >>> 63)

def to_sint32 : Nat → Int32 := fun v =>
  let v := UInt32.ofNat v |>.toInt32
  if v % 2 == 0 then
    v <<< 1
  else
    (0 : Int32) - (v <<< 1) - 1

def to_sint64 : Nat → Int64 := fun v =>
  let v := UInt64.ofNat v |>.toInt64
  if v % 2 == 0 then
    v <<< 1
  else
    (0 : Int64) - (v <<< 1) - 1

-- def put_sint32 (x : Int32) : Put := do
--   put_varint <| UInt32.toNat <| Int32.toUInt32 <| (x <<< 1).xor (x >>> 31)

-- def put_sint64 (x : Int64) : Put := do
--   put_varint <| UInt64.toNat <| Int64.toUInt64 <| (x <<< 1).xor (x >>> 63)

-- def get_sint32 : Get Int32 := do
--   let v ← get_varint
--   let v := UInt32.ofNat v |>.toInt32
--   if v % 2 == 0 then
--     return v <<< 1
--   else
--     return (0 : Int32) - (v <<< 1) - 1

-- def get_sint64 : Get Int64 := do
--   let v ← get_varint
--   let v := UInt64.ofNat v |>.toInt64
--   if v % 2 == 0 then
--     return v <<< 1
--   else
--     return (0 : Int64) - (v <<< 1) - 1

-- def put_fixed32  (x : UInt32)  : Put := Primitive.LE.instEncodeUInt32.put x
-- def put_fixed64  (x : UInt64)  : Put := Primitive.LE.instEncodeUInt64.put x
-- def put_sfixed32 (x : Int32)   : Put := Primitive.LE.instEncodeInt32.put x
-- def put_sfixed64 (x : Int64)   : Put := Primitive.LE.instEncodeInt64.put x
-- def put_float32  (x : Float32) : Put := Primitive.LE.instEncodeFloat32.put x
-- def put_float64  (x : Float)   : Put := Primitive.LE.instEncodeFloat.put x

-- def get_fixed32 :  Get UInt32   := Primitive.LE.instDecodeUInt32.get
-- def get_fixed64 :  Get UInt64   := Primitive.LE.instDecodeUInt64.get
-- def get_sfixed32 : Get Int32    := Primitive.LE.instDecodeInt32.get
-- def get_sfixed64 : Get Int64    := Primitive.LE.instDecodeInt64.get
-- def get_float32 :  Get Float32  :=  Primitive.LE.instDecodeFloat32.get
-- def get_float64 :  Get Float    := Primitive.LE.instDecodeFloat.get

structure A where
  a : Int32
  b : Option String
deriving Inhabited

instance : ProtoMessage A where
  encode x :=
    let r := Message.empty
    let r := r.update 0 <| ProtoVal.VARINT <| from_sint32 x.a
    let r := r.update? 1 <| x.b.map fun b => ProtoVal.LEN <| String.toUTF8 b
    r
  decode msg := do
    let a ← msg.find? 0 |>.mapM fun x =>
      match x with
      | .VARINT v => pure <| to_sint32 v
      | _ => throw s!"expected wire_type varint for variable \"A.a\""
    let a := a.getD default
    let b ← msg.find? 1 |>.mapM fun x =>
      match x with
      | .LEN bs =>
        match String.fromUTF8? bs with
        | some s => pure s
        | none => throw "invalid bytes encountered for utf-8 string"
      | _ => throw s!"expected wire_type len for variable \"A.b\""
    return { a := a, b := b }
