import Binary
import Protobuf.Encoding.Basic

namespace Protobuf.Encoding

open Binary

private def get_varint_bytes : Get ByteArray := do
  let mut bs := ByteArray.emptyWithCapacity 4 -- TODO: maybe another value?
  while True do
    let b ← getThe UInt8
    bs := bs.push b
    if !b.toBitVec.msb then
      break
  return bs

def get_varint : Get Nat := do
  let bs ← get_varint_bytes
  let mut v := 0
  for b in bs do
    v := (v <<< 7) ||| (b &&& 0x7F).toNat
  return v

def put_varint (n : Nat) : Put := do
  let bv := BitVec.ofNat 64 n
  let bv := bv.extractLsb' 0 80 -- 10 bytes
  let mut bs : Array Bool := #[]
  for i in [0:80] do
    bs := bs.push bv[i]!
  let mut cs := bs.toList
  let mut es := #[]
  while True do
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
instance : Encode Record where
  put x := do
    let wire_type : Nat := match x.value with
      | .VARINT _ => 0
      | .I64 _ => 1
      | .LEN _ => 2
      | .I32 _ => 5
    let v : Nat := (x.field_num <<< 3) ||| wire_type
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
    | _ => throw "protobuf: invalid wire type encountered"

instance : Encode Message where
  put x := x.records.forM put

instance : Decode Message where
  get := do
    let mut rs := #[]
    while True do
      let r ←
        try getThe Record
        catch e =>
          if e = "EOI" then
            break -- TODO: check the position
          else
            throw e
      rs := rs.push r
    return Message.mk rs

def wrap_encode {α} (f : α → Protobuf.Encoding.PMEncoder Unit) : Nat → α → Protobuf.Encoding.PMEncoder Unit := fun i a => do
  let m := Binary.Put.run 128 <| Binary.put (f a |>.run)
  Encoding.encode_bytes i m

def wrap_decode {α} (f : Protobuf.Encoding.PMDecoder α) : Nat → Protobuf.Encoding.PMDecoder α := fun i => do
  let d ← Encoding.decode_bytes i
  let r := Binary.Get.run (Binary.getThe Encoding.Message) d
  match r with
  | Binary.DecodeResult.error err _ => throw <| .other s!"failed to decode protobuf message due to internal error: {err}"
  | Binary.DecodeResult.pending .. => throw <| .other "failed to decode protobuf message due to not enough bytes"
  | Binary.DecodeResult.success e .. =>
    match f.run e with
    | .error err => throw <| .other s!"protobuf message decoded but failed to be interpreted, internal error: {err}"
    | .ok r => return r

def wrap_decode? {α} (f : Protobuf.Encoding.PMDecoder α) : Nat → Protobuf.Encoding.PMDecoder (Option α) := fun i => do
  let d ← Encoding.decode_bytes i
  let r := Binary.Get.run (Binary.getThe Encoding.Message) d
  match r with
  | Binary.DecodeResult.error ..
  | Binary.DecodeResult.pending .. => return none
  | Binary.DecodeResult.success e .. =>
    match f.run e with
    | .error err => throw <| .other s!"protobuf message decoded but failed to be interpreted, internal error: {err}"
    | .ok r => return r

section

open Primitive.LE

def put_uint32    (x : UInt32)   : Binary.Put := put_varint x.toNat
def put_uint64    (x : UInt64)   : Binary.Put := put_varint x.toNat
def put_int32     (x : Int32)    : Binary.Put := put_varint x.toUInt32.toNat
def put_int64     (x : Int64)    : Binary.Put := put_varint x.toUInt64.toNat
def put_bool      (x : Bool)     : Binary.Put := put_varint <| if x then 1 else 0
def put_sint32    (x : Int32)    : Binary.Put := put_varint <| from_sint32 x
def put_sint64    (x : Int64)    : Binary.Put := put_varint <| from_sint64 x
def put_fixed32   (x : UInt32)   : Binary.Put := put x
def put_fixed64   (x : UInt64)   : Binary.Put := put x
def put_sfixed32  (x : Int32)    : Binary.Put := put x
def put_sfixed64  (x : Int64)    : Binary.Put := put x
def put_float32   (x : Float32)  : Binary.Put := put x
def put_float64   (x : Float)    : Binary.Put := put x

def get_uint32    : Binary.Get UInt32  := UInt32.ofNat <$> get_varint
def get_uint64    : Binary.Get UInt64  := UInt64.ofNat <$> get_varint
def get_int32     : Binary.Get Int32   := Int32.ofNat  <$> get_varint
def get_int64     : Binary.Get Int64   := Int64.ofNat  <$> get_varint
def get_bool      : Binary.Get Bool    := (· == 1) <$> get_varint
def get_sint32    : Binary.Get Int32   := to_sint32 <$> get_varint
def get_sint64    : Binary.Get Int64   := to_sint64 <$> get_varint
def get_fixed32   : Binary.Get UInt32  := Binary.get
def get_fixed64   : Binary.Get UInt64  := Binary.get
def get_sfixed32  : Binary.Get Int32   := Binary.get
def get_sfixed64  : Binary.Get Int64   := Binary.get
def get_float32   : Binary.Get Float32 := Binary.get
def get_float64   : Binary.Get Float   := Binary.get

end

def packed_encode {α} (f : α → Binary.Put) : Nat → Array α → Protobuf.Encoding.PMEncoder Unit := fun i a => do
  let m := Binary.Put.run 128 (a.forM f)
  Encoding.encode_bytes i m

def packed_decode {α} (f : Binary.Get α) : Nat → Protobuf.Encoding.PMDecoder (Array α) := fun i => do
  let g : Binary.Get (Array α) := do
    let mut vs := Array.emptyWithCapacity 8
    while True do
      let v ← try f catch _ => break
      vs := vs.push v
    return vs
  let data ← PMDecoder.getAll i Validator.bytes
  let r := data.map g.run
  r.flatMapM fun r => do
    match r with
    | Binary.DecodeResult.error err _ => throw <| .other s!"failed to decode packed bytes due to internal error: {err}"
    | Binary.DecodeResult.pending .. => throw <| .other "failed to decode packed bytes due to not enough bytes"
    | Binary.DecodeResult.success e .. => return e

def repeated_string_decode : Nat → Protobuf.Encoding.PMDecoder (Array String) := fun i => PMDecoder.getAll i Validator.string
def repeated_bytes_decode : Nat → Protobuf.Encoding.PMDecoder (Array ByteArray) := fun i => PMDecoder.getAll i Validator.bytes

def repeated_wrap_decode {α} (f : Protobuf.Encoding.PMDecoder α) : Nat → Protobuf.Encoding.PMDecoder (Array α) := fun i => do
  let data ← PMDecoder.getAll i Validator.bytes
  let r := data.map fun d => Binary.Get.run (Binary.getThe Encoding.Message) d
  r.mapM fun r => do
    match r with
    | Binary.DecodeResult.error err _ => throw <| .other s!"failed to decode protobuf message due to internal error: {err}"
    | Binary.DecodeResult.pending .. => throw <| .other "failed to decode protobuf message due to not enough bytes"
    | Binary.DecodeResult.success e .. =>
      match f.run e with
      | .error err => throw <| .other s!"protobuf message decoded but failed to be interpreted, internal error: {err}"
      | .ok r => return r
