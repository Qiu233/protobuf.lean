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
partial def get_varint : Get Nat := fun decoder =>
  /-
  Accumulate directly from the input cursor into protobuf's exact UInt64
  varint domain. Keep the cursor and intermediate shifts machine-sized, then
  convert to Nat only once after validating the terminating byte.
  -/
  let rec go
      (acc shift : UInt64) (index : UInt8) (offset : USize) :
      DecodeResult Nat :=
    if h : offset.toNat < decoder.data.size then
      let byte := decoder.data.uget offset h
      let next := offset + 1
      -- A protobuf varint has at most ten bytes. The tenth byte has exactly
      -- one payload bit, so 0x00 and 0x01 are its only valid values.
      if index == 9 then
        if byte > 1 then
          .error (.userError "protobuf: varint overflow")
            { decoder with offset := next.toNat }
        else
          let value := acc ||| (UInt64.ofNat byte.toNat <<< shift)
          .success value.toNat { decoder with offset := next.toNat }
      else
        let payload := UInt64.ofNat (byte &&& 0x7f).toNat
        let value := acc ||| (payload <<< shift)
        if byte &&& 0x80 == 0 then
          .success value.toNat { decoder with offset := next.toNat }
        else
          go value (shift + 7) (index + 1) next
    else
      DecodeResult.mkEOI { decoder with offset := offset.toNat }
  go 0 0 0 (USize.ofNat decoder.offset)

@[always_inline]
partial def Internal.putVarintUInt64 (value : UInt64) : Put := fun output =>
  let rec go (output : ByteArray) (v : UInt64) : ByteArray :=
    let byte : UInt8 := UInt8.ofNat ((v &&& (0x7F : UInt64)).toNat)
    let v := v >>> 7
    if v = 0 then
      output.push byte
    else
      go (output.push (byte ||| (0x80 : UInt8))) v
  ((), go output value)

@[always_inline]
partial def put_varint (n : Nat) : Put :=
  Internal.putVarintUInt64 (UInt64.ofNat n)

open Primitive.LE in
partial instance : Encode Record where
  put x := do
    let rec go (x : Record) : Put := do
      let putKey (wireType : UInt64) : Put :=
        Internal.putVarintUInt64 <|
          (UInt64.ofNat x.fieldNum <<< 3) ||| wireType
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
      let beforeKey ← remaining
      let key ← get_varint
      let afterKey ← remaining
      /-
      A protobuf tag is a uint32 value.  The general varint reader accepts
      uint64-sized values, but accepting an overlong tag makes malformed input
      alias a valid low-numbered field after shifting.
      -/
      if beforeKey - afterKey > 5 then
        throw (.userError "protobuf: field tag varint is longer than 5 bytes")
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
  let some r ← go none recursionBudget
    | throw
        (.userError
          "protobuf: internal error: a top-level record decoded as an end-group")
  return r

partial instance : Decode Record where
  get := getRecordWithRecursionBudget defaultMessageRecursionLimit

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

partial instance : Decode Message where
  get := getMessageWithRecursionBudget defaultMessageRecursionLimit
