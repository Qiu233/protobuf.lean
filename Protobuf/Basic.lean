import Binary

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

def _root_.ByteArray.toHexLiteral (arr : ByteArray) (lower : Bool := false) : String :=
  let b2c : UInt8 → Char := fun x =>
    if x < 10 then
      Char.ofUInt8 (x + '0'.toUInt8)
    else
      Char.ofUInt8 (x - 10 + if lower then 'a'.toUInt8 else 'A'.toUInt8)
  let b2h : UInt8 → List Char := fun x =>
    let high := x / 16
    let low := x % 16
    [b2c high, b2c low]
  let s := arr.data.toList.map b2h |>.flatMap id
  String.mk s

scoped syntax:max (name := hexBytesLiteral) "hex!" str : term

open Lean Elab Meta Term in
@[scoped term_elab hexBytesLiteral]
def elabHexBytesLiteral : TermElab := fun stx _ => do
  let `(hex! $str) := stx | throwUnsupportedSyntax
  let val := str.getString
  if val.length % 2 = 1 then
    throwErrorAt str "hex bytes literal must have even number of length"
  let cs := val.data.toArray
  for x in cs do
    let r := x.isDigit || (x ≥ 'a' && x ≤ 'f') || (x ≥ 'A' && x ≤ 'F')
    if !r then
      throwErrorAt str "invalid character '{x}'"
  let c2v : Char → UInt8 := fun c =>
    if c.isDigit then
      (c.val - '0'.val).toUInt8
    else if (c ≥ 'a' && c ≤ 'f') then
      (c.val + 10 - 'a'.val).toUInt8
    else
      (c.val + 10 - 'A'.val).toUInt8
  let half := cs.size / 2
  let highs := List.range half |>.map (· * 2) |>.map (c2v cs[·]!)
  let lows := List.range half |>.map (· * 2 + 1) |>.map (c2v cs[·]!)
  let vs := highs.zipWith (ys := lows) fun h l => (h * 16) ||| l
  let u8Type := Expr.const ``UInt8 []
  let es ← vs.mapM fun v => mkNumeral u8Type v.toNat
  let r ← mkArrayLit u8Type es
  return Expr.app (Expr.const ``ByteArray.mk []) r

scoped instance : Repr ByteArray where
  reprPrec x _ := s!"hex!\"{x.toHexLiteral}\""

inductive ProtoVal where
  | VARINT (val : Nat)      -- 0
  | I64 (val : BitVec 64)   -- 1
  | LEN (data : ByteArray)  -- 2
  | I32 (val : BitVec 32)   -- 5
deriving instance Repr for ProtoVal

structure Record where
  field_num : Nat
  value : ProtoVal
deriving Repr

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

-- #eval Get.run get_varint ⟨#[0b10010110, 0b00000001]⟩ |>.toExcept

-- #eval put_varint 150 ⟨#[]⟩

structure Message where
  records : Array Record
deriving Repr

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


#eval Get.run (getThe Message) hex!"089601" |>.toExcept

#eval Get.run (getThe Message) hex!"0a06616263313233" |>.toExcept
