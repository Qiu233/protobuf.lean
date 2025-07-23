import Binary

namespace Protobuf.Encoding

inductive ProtoVal where
  | VARINT (val : Nat)      -- 0
  | I64 (val : BitVec 64)   -- 1
  | LEN (data : ByteArray)  -- 2
  | I32 (val : BitVec 32)   -- 5

structure Record where
  field_num : Nat
  value : ProtoVal

structure Message where
  records : Array Record

/-!
* We only derive the instances if `Repr ByteArray` is present.
* These instances are `scoped`, that is, only have effect when the namespace is opened.
-/
section

variable [Repr ByteArray]

scoped instance : Repr ProtoVal where
  reprPrec x prec := match x with
      | ProtoVal.VARINT a =>
        Repr.addAppParen
          (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
              (Std.Format.text "Protobuf.Encoding.ProtoVal.VARINT" ++ Std.Format.line ++ reprArg a)).group
          prec
      | ProtoVal.I64 a =>
        Repr.addAppParen
          (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
              (Std.Format.text "Protobuf.Encoding.ProtoVal.I64" ++ Std.Format.line ++ reprArg a)).group
          prec
      | ProtoVal.LEN a =>
        Repr.addAppParen
          (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
              (Std.Format.text "Protobuf.Encoding.ProtoVal.LEN" ++ Std.Format.line ++ reprArg a)).group
          prec
      | ProtoVal.I32 a =>
        Repr.addAppParen
          (Std.Format.nest (if prec ≥ 1024 then 1 else 2)
              (Std.Format.text "Protobuf.Encoding.ProtoVal.I32" ++ Std.Format.line ++ reprArg a)).group
          prec

scoped instance : Repr Record where
  reprPrec x prec :=
      Std.Format.bracket "{ "
        (Std.Format.nil ++ Std.Format.text "field_num" ++ Std.Format.text " := " ++
                    (Std.Format.nest 13 (repr x.field_num)).group ++
                  Std.Format.text "," ++
                Std.Format.line ++
              Std.Format.text "value" ++
            Std.Format.text " := " ++
          (Std.Format.nest 9 (repr x.value)).group)
        " }"

scoped instance : Repr Message where
  reprPrec x prec :=
      Std.Format.bracket "{ "
        (Std.Format.nil ++ Std.Format.text "records" ++ Std.Format.text " := " ++
          (Std.Format.nest 11 (repr x.records)).group)
        " }"

end

@[inline]
def Message.find? (m : Message) (n : Nat) : Option ProtoVal :=
  m.records.find? (fun x => x.field_num == n) |>.map fun x => x.value

@[inline]
def Message.update (m : Message) (n : Nat) (v : ProtoVal) : Message :=
  let rs := m.records
  let rs := rs.eraseP (fun x => x.field_num == n)
  let rs := rs.push <| Record.mk n v
  ⟨rs⟩

@[inline]
def Message.update? (m : Message) (n : Nat) (v : Option ProtoVal) : Message := Option.getD (dflt := m) <| v.map fun v =>
  let rs := m.records
  let rs := rs.eraseP (fun x => x.field_num == n)
  let rs := rs.push <| Record.mk n v
  ⟨rs⟩

@[inline]
def Message.empty : Message := ⟨#[]⟩


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

/-- very efficient monadic builder of protobuf message encoding -/
def PMEncoder := StateRefT Encoding.Message (ST Unit)

instance : Monad PMEncoder := by unfold PMEncoder; infer_instance
local instance : MonadStateOf Encoding.Message PMEncoder := by unfold PMEncoder; infer_instance

@[inline]
def PMEncoder.run (x : PMEncoder Unit) : Encoding.Message :=
  let st := StateRefT'.run x Encoding.Message.empty
  let t := EStateM.run st ()
  match t with
  | .error e _ => by cases e
  | .ok r _ => r.snd

@[inline]
def PMEncoder.put (i : Nat) (val : ProtoVal) : PMEncoder Unit := do
  modify fun rs => {rs with records := rs.records.push ⟨i, val⟩}

private abbrev NonemptyArray (α : Type) := { a : Array α // a.size > 0 }

@[inline]
private def NonemptyArray.push {α} (arr : NonemptyArray α) (a : α) : NonemptyArray α := ⟨arr.val.push a, by simp⟩

@[inline]
private def NonemptyArray.last {α} (arr : NonemptyArray α) : α := arr.val[arr.val.size - 1]

private abbrev FastLookupTable := Std.HashMap Nat (NonemptyArray Encoding.ProtoVal)

inductive WireType where
  | VARINT
  | I64
  | LEN
  | I32
deriving Repr

def ProtoVal.getType : ProtoVal → WireType
  | .VARINT .. => .VARINT
  | .I64 .. => .I64
  | .LEN .. => .LEN
  | .I32 .. => .I32

instance : ToString WireType where
  toString x := repr x |>.pretty

inductive PMDecoder.Error where
  | field_wrong_wire_type (got expected : WireType)
  | field_invalid_utf8
  | other (s : String)
deriving Repr

instance : ToString PMDecoder.Error where
  toString x := repr x |>.pretty

def PMDecoder : Type → Type := ExceptT PMDecoder.Error <| ReaderM FastLookupTable

instance : Monad PMDecoder := by unfold PMDecoder; infer_instance
local instance : MonadReaderOf FastLookupTable PMDecoder := by unfold PMDecoder; infer_instance
instance : MonadExceptOf PMDecoder.Error PMDecoder := by unfold PMDecoder; infer_instance

abbrev Validator (α : Type) := ProtoVal → PMDecoder α

@[inline]
private def build_lookup_table : Encoding.Message → FastLookupTable := fun m =>
  m.records.foldl (init := Std.HashMap.emptyWithCapacity (m.records.size)) fun x y =>
    if x.contains y.field_num then
      x.modify y.field_num fun s => s.push y.value
    else
      x.alter y.field_num fun _ => (⟨#[y.value], by simp⟩ : NonemptyArray Encoding.ProtoVal)

@[inline]
def PMDecoder.run {α} (x : PMDecoder α) : Encoding.Message → Except PMDecoder.Error α := fun m =>
  ExceptT.run x (build_lookup_table m)

@[inline, specialize]
def PMDecoder.getD {α} (i : Nat) (validate : Validator α) (dflt : PMDecoder α) : PMDecoder α := do
  let c ← read
  match c.get? i with
  | none => dflt
  | some v => validate v.last

@[inline, specialize]
def PMDecoder.get {α} [Inhabited α] (i : Nat) (validate : Validator α) : PMDecoder α := do
  let c ← read
  match c.get? i with
  | none => return default
  | some v => validate v.last

@[inline, specialize]
def PMDecoder.get? {α} (i : Nat) (validate : Validator α) : PMDecoder (Option α) := do
  PMDecoder.getD i (fun x => some <$> validate x) (pure none)

namespace Validator

@[inline]
def float32 : Validator Float32
  | .I32 v => return Float32.ofBits <| UInt32.ofBitVec v
  | t => throw <| .field_wrong_wire_type .I32 t.getType

@[inline]
def float64 : Validator Float
  | .I64 v => return Float.ofBits <| UInt64.ofBitVec v
  | t => throw <| .field_wrong_wire_type .I64 t.getType

@[inline]
def fixed32 : Validator UInt32
  | .I32 v => return UInt32.ofBitVec v
  | t => throw <| .field_wrong_wire_type .I32 t.getType

@[inline]
def fixed64 : Validator UInt64
  | .I64 v => return UInt64.ofBitVec v
  | t => throw <| .field_wrong_wire_type .I64 t.getType

@[inline]
def sfixed32 : Validator Int32
  | .I32 v => return UInt32.toInt32 <| UInt32.ofBitVec v
  | t => throw <| .field_wrong_wire_type .I32 t.getType

@[inline]
def sfixed64 : Validator Int64
  | .I64 v => return UInt64.toInt64 <| UInt64.ofBitVec v
  | t => throw <| .field_wrong_wire_type .I64 t.getType

@[inline]
def int32 : Validator Int32
  | .VARINT v => return (UInt32.ofNat v).toInt32
  | t => throw <| .field_wrong_wire_type .VARINT t.getType

@[inline]
def uint32 : Validator UInt32
  | .VARINT v => return UInt32.ofNat v
  | t => throw <| .field_wrong_wire_type .VARINT t.getType

@[inline]
def int64 : Validator Int64
  | .VARINT v => return (UInt64.ofNat v).toInt64
  | t => throw <| .field_wrong_wire_type .VARINT t.getType

@[inline]
def uint64 : Validator UInt64
  | .VARINT v => return UInt64.ofNat v
  | t => throw <| .field_wrong_wire_type .VARINT t.getType

@[inline]
def sint32 : Validator Int32
  | .VARINT v => return to_sint32 v
  | t => throw <| .field_wrong_wire_type .VARINT t.getType

@[inline]
def sint64 : Validator Int64
  | .VARINT v => return to_sint64 v
  | t => throw <| .field_wrong_wire_type .VARINT t.getType

@[inline]
def bool : Validator Bool
  | .VARINT v => return v == 1
  | t => throw <| .field_wrong_wire_type .VARINT t.getType

@[inline]
def string : Validator String
  | .LEN bs =>
    match String.fromUTF8? bs with
    | some s => pure s
    | none => throw .field_invalid_utf8
  | t => throw <| .field_wrong_wire_type .LEN t.getType

@[inline]
def bytes : Validator ByteArray
  | .LEN bs => pure bs
  | t => throw <| .field_wrong_wire_type .LEN t.getType

end Validator

def encode_uint32  (i : Nat) (x : UInt32)  : PMEncoder Unit := PMEncoder.put i <| ProtoVal.VARINT x.toNat
def encode_uint64  (i : Nat) (x : UInt64)  : PMEncoder Unit := PMEncoder.put i <| ProtoVal.VARINT x.toNat
def encode_int32   (i : Nat) (x : Int32)  : PMEncoder Unit := PMEncoder.put i <| ProtoVal.VARINT x.toUInt32.toNat
def encode_int64   (i : Nat) (x : Int64)  : PMEncoder Unit := PMEncoder.put i <| ProtoVal.VARINT x.toUInt64.toNat

def encode_bool  (i : Nat) (x : Bool)  : PMEncoder Unit := PMEncoder.put i <| ProtoVal.VARINT <| if x then 1 else 0

def encode_sint32  (i : Nat) (x : Int32)  : PMEncoder Unit := PMEncoder.put i <| ProtoVal.VARINT <| from_sint32 x
def encode_sint64  (i : Nat) (x : Int64)  : PMEncoder Unit := PMEncoder.put i <| ProtoVal.VARINT <| from_sint64 x

def encode_fixed32  (i : Nat) (x : UInt32)  : PMEncoder Unit := PMEncoder.put i <| ProtoVal.I32 x.toBitVec
def encode_fixed64  (i : Nat) (x : UInt64)  : PMEncoder Unit := PMEncoder.put i <| ProtoVal.I64 x.toBitVec
def encode_sfixed32 (i : Nat) (x : Int32)   : PMEncoder Unit := PMEncoder.put i <| ProtoVal.I32 x.toBitVec
def encode_sfixed64 (i : Nat) (x : Int64)   : PMEncoder Unit := PMEncoder.put i <| ProtoVal.I64 x.toBitVec
def encode_float32  (i : Nat) (x : Float32) : PMEncoder Unit := PMEncoder.put i <| ProtoVal.I32 x.toBits.toBitVec
def encode_float64  (i : Nat) (x : Float)   : PMEncoder Unit := PMEncoder.put i <| ProtoVal.I64 x.toBits.toBitVec

def encode_string  (i : Nat) (x : String) : PMEncoder Unit := PMEncoder.put i <| ProtoVal.LEN x.toUTF8
def encode_bytes   (i : Nat) (x : ByteArray) : PMEncoder Unit := PMEncoder.put i <| ProtoVal.LEN x

--

def decode_uint32  (i : Nat) : PMDecoder UInt32   := PMDecoder.get i Validator.uint32
def decode_uint64  (i : Nat) : PMDecoder UInt64   := PMDecoder.get i Validator.uint64
def decode_int32   (i : Nat) : PMDecoder Int32    := PMDecoder.get i Validator.int32
def decode_int64   (i : Nat) : PMDecoder Int64    := PMDecoder.get i Validator.int64

def decode_bool  (i : Nat) : PMDecoder Bool := PMDecoder.get i Validator.bool

def decode_sint32  (i : Nat)  : PMDecoder Int32 := PMDecoder.get i Validator.sint32
def decode_sint64  (i : Nat)  : PMDecoder Int64 := PMDecoder.get i Validator.sint64

def decode_fixed32  (i : Nat) : PMDecoder UInt32   := PMDecoder.get i Validator.fixed32
def decode_fixed64  (i : Nat) : PMDecoder UInt64   := PMDecoder.get i Validator.fixed64
def decode_sfixed32 (i : Nat) : PMDecoder Int32    := PMDecoder.get i Validator.sfixed32
def decode_sfixed64 (i : Nat) : PMDecoder Int64    := PMDecoder.get i Validator.sfixed64
def decode_float32  (i : Nat) : PMDecoder Float32  := PMDecoder.get i Validator.float32
def decode_float64  (i : Nat) : PMDecoder Float    := PMDecoder.get i Validator.float64

def decode_string  (i : Nat) : PMDecoder String := PMDecoder.get i Validator.string
def decode_bytes   (i : Nat) : PMDecoder ByteArray := PMDecoder.get i Validator.bytes

---

def decode_uint32?  (i : Nat) : PMDecoder <| Option UInt32   := PMDecoder.get? i Validator.uint32
def decode_uint64?  (i : Nat) : PMDecoder <| Option UInt64   := PMDecoder.get? i Validator.uint64
def decode_int32?   (i : Nat) : PMDecoder <| Option Int32    := PMDecoder.get? i Validator.int32
def decode_int64?   (i : Nat) : PMDecoder <| Option Int64    := PMDecoder.get? i Validator.int64

def decode_bool?  (i : Nat) : PMDecoder <| Option Bool := PMDecoder.get? i Validator.bool

def decode_sint32?  (i : Nat)  : PMDecoder <| Option Int32 := PMDecoder.get? i Validator.sint32
def decode_sint64?  (i : Nat)  : PMDecoder <| Option Int64 := PMDecoder.get? i Validator.sint64

def decode_fixed32?  (i : Nat) : PMDecoder <| Option UInt32   := PMDecoder.get? i Validator.fixed32
def decode_fixed64?  (i : Nat) : PMDecoder <| Option UInt64   := PMDecoder.get? i Validator.fixed64
def decode_sfixed32? (i : Nat) : PMDecoder <| Option Int32    := PMDecoder.get? i Validator.sfixed32
def decode_sfixed64? (i : Nat) : PMDecoder <| Option Int64    := PMDecoder.get? i Validator.sfixed64
def decode_float32?  (i : Nat) : PMDecoder <| Option Float32  := PMDecoder.get? i Validator.float32
def decode_float64?  (i : Nat) : PMDecoder <| Option Float    := PMDecoder.get? i Validator.float64

def decode_string?  (i : Nat) : PMDecoder <| Option String    := PMDecoder.get? i Validator.string
def decode_bytes?   (i : Nat) : PMDecoder <| Option ByteArray := PMDecoder.get? i Validator.bytes

class ProtoMessage (α : Type) where
  encode : α → PMEncoder Unit
  decode : PMDecoder α

namespace AuxNotation

scoped syntax "checked% " colGt term:max colGt term:max colGt ("at" lineEq num) : term

scoped
macro_rules
  | `(checked% $name:term $fn:term at $n:num) => do
    `(try $fn:term $n:term
        catch e =>
          match e with
          | .field_wrong_wire_type g e => throw <| .other s!"\"{$(Lean.mkIdent ``Lean.Name.toString) $name}\":{$n}: wire type expected {e}, but got {g}"
          | .field_invalid_utf8 => throw <| .other s!"\"{$(Lean.mkIdent ``Lean.Name.toString) $name}\":{$n}: bad utf-8 bytes"
          | .other _ => throw e
      )

end AuxNotation
