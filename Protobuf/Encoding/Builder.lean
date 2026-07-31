module

import Binary
public import Protobuf.Encoding.Basic
public import Protobuf.Encoding.Binary
public import Protobuf.UnvalidatedString
import Std

public section

namespace Protobuf.Encoding

open Binary

@[always_inline]
def Message.push (msg : Message) (r : Record) : Message := {msg with records := msg.records.push r }

@[always_inline]
def Message.set (msg : Message) (fieldNum : Nat) (value : ProtoVal) : Message := msg.push { fieldNum, value }

/-
Validate a raw wire tree before a generated encoder passes it to `Binary.Put`.

Decoded unknown fields already satisfy these invariants, and statically
generated builders only construct valid values.  Generated message structures
also expose `Unknown.Fields`, however, so callers can inject an out-of-domain
`Nat` varint or field number.  Reject those values explicitly instead of
letting the low-level `UInt64.ofNat` conversion truncate them.
-/
mutual
  partial def ProtoVal.validateForEncoding : ProtoVal → Except ProtoError Unit
    | .VARINT value =>
        if value > (1 <<< 64) - 1 then
          throw .invalidVarint
        else
          pure ()
    | .LEN data =>
        if data.size > (1 <<< 31) - 1 then
          throw (.userError
            "length-delimited protobuf value exceeds the 2 GiB limit")
        else
          pure ()
    | .GROUPED message =>
        message.validateForEncoding
    | .I64 _
    | .I32 _ =>
        pure ()

  partial def Record.validateForEncoding
      (record : Record) : Except ProtoError Unit := do
    if record.fieldNum == 0 || record.fieldNum > (1 <<< 29) - 1 then
      throw (.invalidWireType
        s!"protobuf field number {record.fieldNum} is outside 1..536870911")
    record.value.validateForEncoding

  partial def Message.validateForEncoding
      (message : Message) : Except ProtoError Unit :=
    message.records.forM Record.validateForEncoding
end

@[always_inline]
private def ProtoVal.ofLengthDelimited (data : ByteArray) :
    Except Protobuf.Encoding.ProtoError ProtoVal := do
  if data.size > (1 <<< 31) - 1 then
    throw (.userError "length-delimited protobuf value exceeds the 2 GiB limit")
  return ProtoVal.LEN data

@[noinline]
def ProtoVal.ofMessage : Message → Except Protobuf.Encoding.ProtoError ProtoVal := fun s =>
  do
    s.validateForEncoding
    ProtoVal.ofLengthDelimited (Put.run (put s))

@[noinline]
def ProtoVal.ofGroup : Message → Except Protobuf.Encoding.ProtoError ProtoVal := fun s => do
  s.validateForEncoding
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
  let y := x.toUInt32
  -- `y >>> 31` is only 0 or 1 because `y` is unsigned.  ZigZag needs the
  -- arithmetic right-shift of the signed input, i.e. an all-zero/all-one mask.
  let signMask : UInt32 := (0 : UInt32) - (y >>> 31)
  let n := (y <<< 1) ^^^ signMask
  return ProtoVal.VARINT n.toNat
@[always_inline]
def ProtoVal.ofVarint_sint64 : Int64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x =>
  let y := x.toUInt64
  let signMask : UInt64 := (0 : UInt64) - (y >>> 63)
  let n := (y <<< 1) ^^^ signMask
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
