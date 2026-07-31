module

public import Protobuf.Encoding.Basic
public import Protobuf.Encoding.Binary

public section

namespace Protobuf.Encoding

/--
A borrowed interval of a protobuf input buffer.

Parsed length-delimited values keep this view until schema-aware decoding
decides whether the payload is an embedded message, packed data, a string, raw
bytes, or an unknown field. This avoids copying every LEN payload eagerly.
-/
structure ByteSpan where
  source : ByteArray
  start : Nat
  stop : Nat
deriving Inhabited

def ByteSpan.size (span : ByteSpan) : Nat :=
  span.stop - span.start

def ByteSpan.toByteArray (span : ByteSpan) : ByteArray :=
  span.source.extract span.start span.stop

mutual

/-- Schema-neutral wire value whose LEN case borrows the input buffer. -/
inductive SpannedValue where
  | varint (value : UInt64)
  | i64 (value : UInt64)
  | len (value : ByteSpan)
  | grouped (value : SpannedMessage)
  | i32 (value : UInt32)
deriving Inhabited

structure SpannedRecord where
  fieldNum : Nat
  value : SpannedValue
deriving Inhabited

structure SpannedMessage where
  records : Array SpannedRecord
deriving Inhabited

end

private structure WireCursor where
  source : ByteArray
  offset : Nat
  stop : Nat

private def WireCursor.readByte
    (cursor : WireCursor) : Except ProtoError (UInt8 × WireCursor) := do
  if cursor.offset < cursor.stop then
    if h : cursor.offset < cursor.source.size then
      let byte := cursor.source[cursor.offset]
      return (byte, { cursor with offset := cursor.offset + 1 })
  throw .truncated

private partial def WireCursor.readVarint
    (cursor : WireCursor) :
    Except ProtoError (UInt64 × Nat × WireCursor) := do
  let rec go
      (cursor : WireCursor) (value shift : UInt64) (index : Nat) :
      Except ProtoError (UInt64 × Nat × WireCursor) := do
    let (byte, cursor) ← cursor.readByte
    if index == 9 then
      if byte > 1 then
        throw .invalidVarint
      return (value ||| (UInt64.ofNat byte.toNat <<< shift), 10, cursor)
    let value :=
      value |||
        (UInt64.ofNat (byte &&& (0x7f : UInt8)).toNat <<< shift)
    if byte &&& (0x80 : UInt8) == 0 then
      return (value, index + 1, cursor)
    go cursor value (shift + 7) (index + 1)
  go cursor 0 0 0

private def WireCursor.readFixed
    (cursor : WireCursor) (width : Nat) :
    Except ProtoError (UInt64 × WireCursor) := do
  let mut cursor := cursor
  let mut value : UInt64 := 0
  for index in [:width] do
    let (byte, next) ← cursor.readByte
    value := value |||
      (UInt64.ofNat byte.toNat <<< UInt64.ofNat (8 * index))
    cursor := next
  return (value, cursor)

private partial def parseSpannedRecords
    (cursor : WireCursor) (expectedEnd? : Option Nat)
    (groupBudget : Nat) :
    Except ProtoError (Array SpannedRecord × WireCursor) := do
  let mut cursor := cursor
  let mut records := Array.emptyWithCapacity 32
  repeat
    if cursor.offset == cursor.stop then
      if expectedEnd?.isSome then
        throw .truncated
      return (records, cursor)
    let (key, keyBytes, afterKey) ← cursor.readVarint
    if keyBytes > 5 then
      throw (.userError "protobuf: field tag varint is longer than 5 bytes")
    let wireType := key &&& 0b111
    let fieldNum64 := key >>> 3
    if fieldNum64 == 0 || fieldNum64 > (0x1fffffff : UInt64) then
      throw (.userError "protobuf: invalid field number")
    let fieldNum := fieldNum64.toNat
    cursor := afterKey
    match wireType with
    | 0 =>
        let (value, _, next) ← cursor.readVarint
        records := records.push ⟨fieldNum, .varint value⟩
        cursor := next
    | 1 =>
        let (value, next) ← cursor.readFixed 8
        records := records.push ⟨fieldNum, .i64 value⟩
        cursor := next
    | 2 =>
        let (length64, _, afterLength) ← cursor.readVarint
        if length64 > 0x7fffffff then
          throw (.userError
            "protobuf: length-delimited field exceeds 2 GiB limit")
        let length := length64.toNat
        if length > afterLength.stop - afterLength.offset then
          throw .truncated
        let stop := afterLength.offset + length
        records := records.push ⟨fieldNum, .len {
          source := afterLength.source
          start := afterLength.offset
          stop
        }⟩
        cursor := { afterLength with offset := stop }
    | 3 =>
        if groupBudget == 0 then
          throw (.userError "protobuf: group recursion limit exceeded")
        let (nested, next) ←
          parseSpannedRecords cursor (some fieldNum) (groupBudget - 1)
        records := records.push
          ⟨fieldNum, .grouped { records := nested }⟩
        cursor := next
    | 4 =>
        match expectedEnd? with
        | some expected =>
            if fieldNum == expected then
              return (records, cursor)
            throw (.userError "protobuf: mismatching EGROUP field number")
        | none =>
            throw (.userError "protobuf: unexpected EGROUP")
    | 5 =>
        let (value, next) ← cursor.readFixed 4
        records := records.push ⟨fieldNum, .i32 value.toUInt32⟩
        cursor := next
    | _ =>
        throw (.userError "protobuf: invalid wire type encountered")
  throw (.userError "protobuf: internal wire cursor loop terminated")

/-- Parse a complete input while borrowing all length-delimited payloads. -/
def SpannedMessage.decode
    (bytes : ByteArray)
    (groupBudget : Nat := defaultMessageRecursionLimit) :
    Except ProtoError SpannedMessage := do
  if bytes.size > 0x7fffffff then
    throw (.invalidBuffer "protobuf messages must be smaller than 2 GiB")
  let cursor : WireCursor := {
    source := bytes
    offset := 0
    stop := bytes.size
  }
  let (records, finalCursor) ←
    parseSpannedRecords cursor none groupBudget
  if finalCursor.offset != finalCursor.stop then
    throw (.userError "protobuf: parser did not consume the complete input")
  return { records }

/-- Parse an embedded message directly inside a borrowed LEN payload. -/
def ByteSpan.decodeMessage
    (span : ByteSpan)
    (groupBudget : Nat := defaultMessageRecursionLimit) :
    Except ProtoError SpannedMessage := do
  if span.start > span.stop || span.stop > span.source.size then
    throw (.invalidBuffer "protobuf byte span is outside its source buffer")
  if span.size > 0x7fffffff then
    throw (.invalidBuffer "protobuf messages must be smaller than 2 GiB")
  let cursor : WireCursor := {
    source := span.source
    offset := span.start
    stop := span.stop
  }
  let (records, finalCursor) ←
    parseSpannedRecords cursor none groupBudget
  if finalCursor.offset != finalCursor.stop then
    throw (.userError "protobuf: parser did not consume the complete span")
  return { records }

mutual

/-- Materialize a borrowed wire value for the compatibility/reflection API. -/
partial def SpannedValue.toProtoVal : SpannedValue → ProtoVal
  | .varint value => .VARINT value.toNat
  | .i64 value => .I64 value.toBitVec
  | .len span => .LEN span.toByteArray
  | .grouped message => .GROUPED message.toMessage
  | .i32 value => .I32 value.toBitVec

partial def SpannedRecord.toRecord
    (record : SpannedRecord) : Record :=
  ⟨record.fieldNum, record.value.toProtoVal⟩

partial def SpannedMessage.toMessage
    (message : SpannedMessage) : Message :=
  ⟨message.records.map SpannedRecord.toRecord⟩

end

end Protobuf.Encoding
