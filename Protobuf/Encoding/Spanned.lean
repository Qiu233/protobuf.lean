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
  | len (source : ByteArray) (start stop : Nat)
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

structure SpannedCursor where
  source : ByteArray
  offset : Nat
  stop : Nat
  validStop : stop ≤ source.size

@[always_inline]
private partial def SpannedCursor.readVarintAt
    (cursor : SpannedCursor) (initialOffset : Nat) :
    Except ProtoError (UInt64 × Nat × Nat) := do
  let rec go
      (offset : Nat) (value shift : UInt64) (index : Nat) :
      Except ProtoError (UInt64 × Nat × Nat) := do
    if hStop : offset < cursor.stop then
      have hSource : offset < cursor.source.size :=
        Nat.lt_of_lt_of_le hStop cursor.validStop
      let byte := cursor.source[offset]
      let next := offset + 1
      if index == 9 then
        if byte > 1 then
          throw .invalidVarint
        return (
          value ||| (UInt64.ofNat byte.toNat <<< shift),
          10,
          next
        )
      let value :=
        value |||
          (UInt64.ofNat (byte &&& (0x7f : UInt8)).toNat <<< shift)
      if byte &&& (0x80 : UInt8) == 0 then
        return (value, index + 1, next)
      return ← go next value (shift + 7) (index + 1)
    throw .truncated
  go initialOffset 0 0 0

@[always_inline]
private def SpannedCursor.readFixedAt
    (cursor : SpannedCursor) (offset width : Nat) :
    Except ProtoError (UInt64 × Nat) := do
  if width > cursor.stop - offset then
    throw .truncated
  let mut value : UInt64 := 0
  for index in [:width] do
    let byte := cursor.source[offset + index]!
    value := value |||
      (UInt64.ofNat byte.toNat <<< UInt64.ofNat (8 * index))
  return (value, offset + width)

private def SpannedCursor.readVarint
    (cursor : SpannedCursor) :
    Except ProtoError (UInt64 × Nat × SpannedCursor) := do
  let (value, width, offset) ← cursor.readVarintAt cursor.offset
  return (value, width, { cursor with offset })

private def SpannedCursor.readFixed
    (cursor : SpannedCursor) (width : Nat) :
    Except ProtoError (UInt64 × SpannedCursor) := do
  let (value, offset) ← cursor.readFixedAt cursor.offset width
  return (value, { cursor with offset })

private partial def foldSpannedRecordsM
    {α : Type}
    (cursor : SpannedCursor) (expectedEnd? : Option Nat)
    (groupBudget : Nat) (init : α)
    (step : α → SpannedRecord → Except ProtoError α) :
    Except ProtoError (α × SpannedCursor) := do
  let mut cursor := cursor
  let mut acc := init
  repeat
    if cursor.offset == cursor.stop then
      if expectedEnd?.isSome then
        throw .truncated
      return (acc, cursor)
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
        acc ← step acc ⟨fieldNum, .varint value⟩
        cursor := next
    | 1 =>
        let (value, next) ← cursor.readFixed 8
        acc ← step acc ⟨fieldNum, .i64 value⟩
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
        acc ← step acc
          ⟨fieldNum,
            .len afterLength.source afterLength.offset stop⟩
        cursor := { afterLength with offset := stop }
    | 3 =>
        if groupBudget == 0 then
          throw (.userError "protobuf: group recursion limit exceeded")
        let (nested, next) ←
          foldSpannedRecordsM cursor (some fieldNum) (groupBudget - 1)
            (Array.emptyWithCapacity 8)
            fun records record => pure (records.push record)
        acc ← step acc
          ⟨fieldNum, .grouped { records := nested }⟩
        cursor := next
    | 4 =>
        match expectedEnd? with
        | some expected =>
            if fieldNum == expected then
              return (acc, cursor)
            throw (.userError "protobuf: mismatching EGROUP field number")
        | none =>
            throw (.userError "protobuf: unexpected EGROUP")
    | 5 =>
        let (value, next) ← cursor.readFixed 4
        acc ← step acc ⟨fieldNum, .i32 value.toUInt32⟩
        cursor := next
    | _ =>
        throw (.userError "protobuf: invalid wire type encountered")
  throw (.userError "protobuf: internal wire cursor loop terminated")

private def parseSpannedRecords
    (cursor : SpannedCursor) (expectedEnd? : Option Nat)
    (groupBudget : Nat) :
    Except ProtoError (Array SpannedRecord × SpannedCursor) :=
  foldSpannedRecordsM cursor expectedEnd? groupBudget
    (Array.emptyWithCapacity 8)
    fun records record => pure (records.push record)

/-- Validate a borrowed message interval and create a streaming cursor. -/
def SpannedCursor.ofSpan
    (source : ByteArray) (start stop : Nat) :
    Except ProtoError SpannedCursor := do
  if start > stop then
    throw
      (.invalidBuffer
        "protobuf byte span is outside its source buffer")
  if validStop : stop ≤ source.size then
    if stop - start > 0x7fffffff then
      throw
        (.invalidBuffer
          "protobuf messages must be smaller than 2 GiB")
    return { source, offset := start, stop, validStop }
  throw
    (.invalidBuffer
      "protobuf byte span is outside its source buffer")

/--
Result of advancing a borrowed wire cursor by one record.

`next` stores only the new byte offset, so a streaming generated decoder keeps
one shared cursor instead of allocating a replacement cursor and nested
`Option`/pair objects for every field.
-/
inductive SpannedCursorStep where
  | done
  | next (record : SpannedRecord) (offset : Nat)
deriving Inhabited

/--
Read one top-level wire record starting at `offset`.

Length-delimited payloads remain intervals of `cursor.source`. A legacy group
is materialized only through its matching end tag because groups have no
length-delimited boundary.
-/
@[noinline]
partial def SpannedCursor.nextAt
    (cursor : SpannedCursor)
    (offset : Nat)
    (groupBudget : Nat := defaultMessageRecursionLimit) :
    Except ProtoError SpannedCursorStep := do
  if offset == cursor.stop then
    return .done
  if offset < cursor.offset || offset > cursor.stop then
    throw
      (.invalidBuffer
        "protobuf cursor offset is outside its source interval")
  let (key, keyBytes, afterKey) ← cursor.readVarintAt offset
  if keyBytes > 5 then
    throw (.userError "protobuf: field tag varint is longer than 5 bytes")
  let wireType := key &&& 0b111
  let fieldNum64 := key >>> 3
  if fieldNum64 == 0 || fieldNum64 > (0x1fffffff : UInt64) then
    throw (.userError "protobuf: invalid field number")
  let fieldNum := fieldNum64.toNat
  match wireType with
  | 0 =>
      let (value, _, next) ← cursor.readVarintAt afterKey
      return .next ⟨fieldNum, .varint value⟩ next
  | 1 =>
      let (value, next) ← cursor.readFixedAt afterKey 8
      return .next ⟨fieldNum, .i64 value⟩ next
  | 2 =>
      let (length64, _, afterLength) ←
        cursor.readVarintAt afterKey
      if length64 > 0x7fffffff then
        throw (.userError
          "protobuf: length-delimited field exceeds 2 GiB limit")
      let length := length64.toNat
      if length > cursor.stop - afterLength then
        throw .truncated
      let stop := afterLength + length
      return .next
        ⟨fieldNum,
          .len cursor.source afterLength stop⟩
        stop
  | 3 =>
      if groupBudget == 0 then
        throw (.userError "protobuf: group recursion limit exceeded")
      let afterKeyCursor := { cursor with offset := afterKey }
      let (nested, next) ←
        parseSpannedRecords afterKeyCursor
          (some fieldNum) (groupBudget - 1)
      return .next
        ⟨fieldNum, .grouped { records := nested }⟩
        next.offset
  | 4 =>
      throw (.userError "protobuf: unexpected EGROUP")
  | 5 =>
      let (value, next) ← cursor.readFixedAt afterKey 4
      return .next ⟨fieldNum, .i32 value.toUInt32⟩ next
  | _ =>
      throw (.userError "protobuf: invalid wire type encountered")

/-- Parse a complete input while borrowing all length-delimited payloads. -/
def SpannedMessage.decode
    (bytes : ByteArray)
    (groupBudget : Nat := defaultMessageRecursionLimit) :
    Except ProtoError SpannedMessage := do
  if bytes.size > 0x7fffffff then
    throw (.invalidBuffer "protobuf messages must be smaller than 2 GiB")
  let cursor : SpannedCursor := {
    source := bytes
    offset := 0
    stop := bytes.size
    validStop := Nat.le_refl bytes.size
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
  if span.start > span.stop then
    throw (.invalidBuffer "protobuf byte span is outside its source buffer")
  if validStop : span.stop ≤ span.source.size then
    if span.size > 0x7fffffff then
      throw (.invalidBuffer "protobuf messages must be smaller than 2 GiB")
    let cursor : SpannedCursor := {
      source := span.source
      offset := span.start
      stop := span.stop
      validStop
    }
    let (records, finalCursor) ←
      parseSpannedRecords cursor none groupBudget
    if finalCursor.offset != finalCursor.stop then
      throw (.userError "protobuf: parser did not consume the complete span")
    return { records }
  throw (.invalidBuffer "protobuf byte span is outside its source buffer")

/--
One wire-message input for generated schema-aware decoding.

`span` is the zero-copy fast path used for serialized root and embedded
messages. `spanned` represents a legacy group that the schema-neutral parser
has already delimited. `owned` adapts the public compatibility `Message` API
without first copying its complete record array.
-/
inductive SpannedMessageSource where
  | span (source : ByteArray) (start stop : Nat)
  | spanned (message : SpannedMessage)
  | owned (message : Message)
deriving Inhabited

/--
Amortized-constant collection of wire-message occurrences.

Singular protobuf message fields merge all their occurrences before required
initialization is checked. Keeping the common zero/one cases inline avoids an
array allocation, while `many` preserves occurrence order.
-/
inductive SpannedMessageChunks where
  | empty
  | single (source : SpannedMessageSource)
  | many (sources : Array SpannedMessageSource)
deriving Inhabited

def SpannedMessageChunks.push
    (chunks : SpannedMessageChunks)
    (source : SpannedMessageSource) : SpannedMessageChunks :=
  match chunks with
  | .empty => .single source
  | .single first => .many #[first, source]
  | .many sources => .many (sources.push source)

def SpannedMessageChunks.isEmpty : SpannedMessageChunks → Bool
  | .empty => true
  | _ => false

mutual

/-- Materialize a borrowed wire value for the compatibility/reflection API. -/
partial def SpannedValue.toProtoVal : SpannedValue → ProtoVal
  | .varint value => .VARINT value.toNat
  | .i64 value => .I64 value.toBitVec
  | .len source start stop => .LEN (source.extract start stop)
  | .grouped message => .GROUPED message.toMessage
  | .i32 value => .I32 value.toBitVec

partial def SpannedRecord.toRecord
    (record : SpannedRecord) : Record :=
  ⟨record.fieldNum, record.value.toProtoVal⟩

partial def SpannedMessage.toMessage
    (message : SpannedMessage) : Message :=
  ⟨message.records.map SpannedRecord.toRecord⟩

end

mutual

/-- Borrow an owned compatibility value without serializing it. -/
partial def ProtoVal.toSpannedValue : ProtoVal → SpannedValue
  | .VARINT value => .varint (UInt64.ofNat value)
  | .I64 value => .i64 (UInt64.ofBitVec value)
  | .LEN data => .len data 0 data.size
  | .GROUPED message => .grouped message.toSpannedMessage
  | .I32 value => .i32 (UInt32.ofBitVec value)

partial def Record.toSpannedRecord
    (record : Record) : SpannedRecord :=
  ⟨record.fieldNum, record.value.toSpannedValue⟩

partial def Message.toSpannedMessage
    (message : Message) : SpannedMessage :=
  ⟨message.records.map Record.toSpannedRecord⟩

end

private def SpannedMessageSource.foldlM
    (source : SpannedMessageSource) (init : α)
    (step : α → SpannedRecord → Except ProtoError α)
    (groupBudget : Nat) : Except ProtoError α := do
  match source with
  | .span bytes start stop =>
      if start > stop then
        throw
          (.invalidBuffer
            "protobuf byte span is outside its source buffer")
      if validStop : stop ≤ bytes.size then
        if stop - start > 0x7fffffff then
          throw
            (.invalidBuffer
              "protobuf messages must be smaller than 2 GiB")
        let cursor : SpannedCursor := {
          source := bytes
          offset := start
          stop
          validStop
        }
        return (←
          foldSpannedRecordsM cursor none groupBudget init step).1
      throw
        (.invalidBuffer
          "protobuf byte span is outside its source buffer")
  | .spanned message =>
      message.records.foldlM (init := init) step
  | .owned message =>
      message.records.foldlM (init := init) fun acc record =>
        step acc record.toSpannedRecord

/--
Visit the wire records in all message occurrences without concatenating or
materializing their borrowed LEN payloads.

The callback observes the same record order as protobuf message merging:
records of each occurrence are visited in occurrence order. Legacy group
bodies are the only recursively materialized records because their end tags,
unlike LEN bounds, cannot be represented by a byte interval alone.
-/
@[noinline]
def SpannedMessageChunks.foldlM
    (chunks : SpannedMessageChunks) (init : α)
    (step : α → SpannedRecord → Except ProtoError α)
    (groupBudget : Nat := defaultMessageRecursionLimit) :
    Except ProtoError α := do
  match chunks with
  | .empty => pure init
  | .single source =>
      source.foldlM init step groupBudget
  | .many sources =>
      sources.foldlM (init := init) fun acc source =>
        source.foldlM acc step groupBudget

def SpannedMessageChunks.ofBytes
    (bytes : ByteArray) : SpannedMessageChunks :=
  .single (.span bytes 0 bytes.size)

def SpannedMessageChunks.ofMessage
    (message : Message) : SpannedMessageChunks :=
  .single (.owned message)

end Protobuf.Encoding
