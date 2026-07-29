import Protobuf.Encoding
import Binary

open Binary
open Protobuf.Encoding

namespace Test.EncodingWire

abbrev assertTrue (condition : Bool) (message : String) : Except String Unit := do
  unless condition do
    throw message

abbrev assertEq [BEq α] (actual expected : α) (message : String) : Except String Unit :=
  assertTrue (actual == expected) message

abbrev ofProtoExcept (result : Except ProtoError α) : Except String α :=
  match result with
  | .ok value => pure value
  | .error error => throw error.toString

abbrev assertProtoFails (result : Except ProtoError α) (message : String) : Except String Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw message

abbrev builtVarint (result : Except ProtoError ProtoVal) : Except String Nat := do
  match ← ofProtoExcept result with
  | .VARINT value => pure value
  | _ => throw "builder produced a non-varint value"

abbrev packedPayload (result : Except ProtoError ProtoVal) : Except String ByteArray := do
  match ← ofProtoExcept result with
  | .LEN payload => pure payload
  | _ => throw "packed builder produced a non-length-delimited value"

abbrev testPackedBuilderVectors : Except String Unit := do
  assertEq (← packedPayload (ProtoVal.of_packed #[])) ByteArray.empty
    "an empty packed sequence must produce a valid empty payload"

  let varints ← packedPayload <| ProtoVal.of_packed #[
    .VARINT 0,
    .VARINT 1,
    .VARINT 150,
    .VARINT 0xffffffffffffffff
  ]
  assertEq varints (⟨#[
    0x00, 0x01, 0x96, 0x01,
    0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0x01
  ]⟩ : ByteArray)
    "packed varint payload differs from the official runtime encoding"

  let fixed32 ← packedPayload <| ProtoVal.of_packed #[
    .I32 (1 : UInt32).toBitVec,
    .I32 (0x12345678 : UInt32).toBitVec
  ]
  assertEq fixed32 (⟨#[
    0x01, 0x00, 0x00, 0x00,
    0x78, 0x56, 0x34, 0x12
  ]⟩ : ByteArray)
    "packed fixed32 payload must use little-endian elements"

  let fixed64 ← packedPayload <| ProtoVal.of_packed #[
    .I64 (1 : UInt64).toBitVec,
    .I64 (0x0123456789abcdef : UInt64).toBitVec
  ]
  assertEq fixed64 (⟨#[
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01
  ]⟩ : ByteArray)
    "packed fixed64 payload must use little-endian elements"

  assertProtoFails (ProtoVal.of_packed #[.LEN ByteArray.empty])
    "length-delimited values are not packable"
  assertProtoFails (ProtoVal.of_packed #[.GROUPED Message.empty])
    "groups are not packable"
  assertProtoFails (ProtoVal.of_packed #[.VARINT (1 <<< 64)])
    "packed varints must fit in the protobuf uint64 wire domain"

abbrev testRawEncodingValidation : Except String Unit := do
  let oversizedVarint :=
    Message.set Message.empty 1 (.VARINT (1 <<< 64))
  assertProtoFails oversizedVarint.validateForEncoding
    "raw varints larger than uint64 must be rejected before encoding"

  let zeroTag := Message.set Message.empty 0 (.VARINT 1)
  assertProtoFails zeroTag.validateForEncoding
    "raw field number zero must be rejected before encoding"

  let oversizedTag :=
    Message.set Message.empty (1 <<< 29) (.VARINT 1)
  assertProtoFails oversizedTag.validateForEncoding
    "raw field numbers above the protobuf maximum must be rejected"

  let invalidGroup :=
    Message.set Message.empty 1
      (.GROUPED (Message.set Message.empty 0 (.VARINT 1)))
  assertProtoFails invalidGroup.validateForEncoding
    "invalid records nested in a group must be rejected"

  discard <| ofProtoExcept <|
    (Message.set Message.empty 1 (.VARINT 0xffffffffffffffff)).validateForEncoding

abbrev testZigZagVectors : Except String Unit := do
  assertEq (← builtVarint (ProtoVal.ofVarint_sint32 0)) 0
    "sint32 ZigZag(0) must be 0"
  assertEq (← builtVarint (ProtoVal.ofVarint_sint32 (-1))) 1
    "sint32 ZigZag(-1) must be 1"
  assertEq (← builtVarint (ProtoVal.ofVarint_sint32 1)) 2
    "sint32 ZigZag(1) must be 2"
  assertEq (← builtVarint (ProtoVal.ofVarint_sint32 (-2))) 3
    "sint32 ZigZag(-2) must be 3"
  assertEq (← builtVarint (ProtoVal.ofVarint_sint32 Int32.maxValue)) 0xfffffffe
    "sint32 ZigZag(max) mismatch"
  assertEq (← builtVarint (ProtoVal.ofVarint_sint32 Int32.minValue)) 0xffffffff
    "sint32 ZigZag(min) mismatch"

  assertEq (← builtVarint (ProtoVal.ofVarint_sint64 0)) 0
    "sint64 ZigZag(0) must be 0"
  assertEq (← builtVarint (ProtoVal.ofVarint_sint64 (-1))) 1
    "sint64 ZigZag(-1) must be 1"
  assertEq (← builtVarint (ProtoVal.ofVarint_sint64 1)) 2
    "sint64 ZigZag(1) must be 2"
  assertEq (← builtVarint (ProtoVal.ofVarint_sint64 (-2))) 3
    "sint64 ZigZag(-2) must be 3"
  assertEq (← builtVarint (ProtoVal.ofVarint_sint64 Int64.maxValue))
    0xfffffffffffffffe "sint64 ZigZag(max) mismatch"
  assertEq (← builtVarint (ProtoVal.ofVarint_sint64 Int64.minValue))
    0xffffffffffffffff "sint64 ZigZag(min) mismatch"

  let values32 := #[Int32.minValue, (-2), (-1), 0, 1, 2, Int32.maxValue]
  for value in values32 do
    let encoded ← builtVarint (ProtoVal.ofVarint_sint32 value)
    let decoded ← ofProtoExcept <|
      Message.getVarint_sint32? (Message.set Message.empty 1 (.VARINT encoded)) 1
    assertEq decoded (some value) "sint32 ZigZag round-trip mismatch"

  let values64 := #[Int64.minValue, (-2), (-1), 0, 1, 2, Int64.maxValue]
  for value in values64 do
    let encoded ← builtVarint (ProtoVal.ofVarint_sint64 value)
    let decoded ← ofProtoExcept <|
      Message.getVarint_sint64? (Message.set Message.empty 1 (.VARINT encoded)) 1
    assertEq decoded (some value) "sint64 ZigZag round-trip mismatch"

abbrev testSignedInt32WireEncoding : Except String Unit := do
  let minusOne ← ofProtoExcept (ProtoVal.ofVarint_int32 (-1))
  let .VARINT minusOne := minusOne
    | throw "int32 builder produced a non-varint value"
  assertEq minusOne 0xffffffffffffffff
    "negative int32 must be sign-extended to the 64-bit varint input"

  let positive ← ofProtoExcept (ProtoVal.ofVarint_int32 150)
  let .VARINT positive := positive
    | throw "int32 builder produced a non-varint value"
  assertEq positive 150
    "positive int32 varint encoding changed unexpectedly"

abbrev testPackedFixed32 : Except String Unit := do
  let first : UInt32 := 1
  let second : UInt32 := 0x12345678
  let payload : ByteArray := ⟨#[0x01, 0x00, 0x00, 0x00, 0x78, 0x56, 0x34, 0x12]⟩
  let packed := Message.set Message.empty 1 (.LEN payload)
  assertEq (← ofProtoExcept (Message.getPackedI32_fixed32 packed 1)) #[first, second]
    "packed fixed32 values were not decoded as four-byte little-endian elements"
  assertEq (← ofProtoExcept (Message.getRepeatedI32_fixed32 packed 1)) #[first, second]
    "repeated fixed32 did not accept packed encoding"

  let mixed := Message.set Message.empty 1 (.LEN ⟨#[0x01, 0x00, 0x00, 0x00]⟩)
  let mixed := Message.set mixed 1 (.I32 second.toBitVec)
  let mixed := Message.set mixed 1 (.LEN ⟨#[0xef, 0xcd, 0xab, 0x90]⟩)
  assertEq (← ofProtoExcept (Message.getRepeatedI32_fixed32 mixed 1))
    #[first, second, (0x90abcdef : UInt32)]
    "repeated fixed32 did not preserve mixed packed/unpacked wire order"

  let incomplete := Message.set Message.empty 1 (.LEN ⟨#[0x01, 0x00, 0x00, 0x00, 0xff]⟩)
  assertProtoFails (Message.getRepeatedI32_fixed32 incomplete 1)
    "packed fixed32 payload with a partial final element must be rejected"

abbrev testPackedFixed64 : Except String Unit := do
  let first : UInt64 := 1
  let second : UInt64 := 0x0123456789abcdef
  let payload : ByteArray := ⟨#[
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01
  ]⟩
  let packed := Message.set Message.empty 1 (.LEN payload)
  assertEq (← ofProtoExcept (Message.getPackedI64_fixed64 packed 1)) #[first, second]
    "packed fixed64 values were not decoded as eight-byte little-endian elements"
  assertEq (← ofProtoExcept (Message.getRepeatedI64_fixed64 packed 1)) #[first, second]
    "repeated fixed64 did not accept packed encoding"

  let incomplete := Message.set Message.empty 1 (.LEN ⟨#[
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff
  ]⟩)
  assertProtoFails (Message.getRepeatedI64_fixed64 incomplete 1)
    "packed fixed64 payload with a partial final element must be rejected"

-- Keep these as separate evaluations. Imported `partial` decoder helpers can
-- be evaluated directly, while wrapping them in an interpreted runner would
-- require native symbols unavailable to `#eval`. `#guard_msgs` also turns a
-- printed `false` into a compilation failure.
/-- info: true -/
#guard_msgs (info) in
#eval (match testZigZagVectors with | .ok () => true | .error _ => false)

/-- info: true -/
#guard_msgs (info) in
#eval
  match ProtoVal.ofVarint_int32 (-1) with
  | .ok (.VARINT value) =>
    value == 0xffffffffffffffff &&
      Binary.Put.run (put_varint value) ==
        (⟨#[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01]⟩ : ByteArray)
  | _ => false

/-- info: true -/
#guard_msgs (info) in
#eval (match testPackedFixed32 with | .ok () => true | .error _ => false)

/-- info: true -/
#guard_msgs (info) in
#eval (match testPackedFixed64 with | .ok () => true | .error _ => false)

/-- info: true -/
#guard_msgs (info) in
#eval (match testPackedBuilderVectors with | .ok () => true | .error _ => false)

/-- info: true -/
#guard_msgs (info) in
#eval (match testRawEncodingValidation with | .ok () => true | .error _ => false)

/-- info: true -/
#guard_msgs (info) in
#eval
  let packed := Message.set Message.empty 1 (.LEN ⟨#[0x01, 0x96, 0x01]⟩)
  let mixed := Message.set (Message.set packed 1 (.VARINT 3)) 1 (.LEN ⟨#[0x04]⟩)
  let mixedOk :=
    match Message.getRepeatedVarint_uint64 mixed 1 with
    | .ok values => values == #[(1 : UInt64), 150, 3, 4]
    | .error _ => false
  let overflow := Message.set Message.empty 1 (.LEN ⟨#[
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02
  ]⟩)
  let overflowRejected :=
    match Message.getRepeatedVarint_uint64 overflow 1 with
    | .error _ => true
    | .ok _ => false
  mixedOk && overflowRejected

/-- info: true -/
#guard_msgs (info) in
#eval
  let rejects := fun (data : ByteArray) =>
    match (Binary.Get.run (Binary.getThe Message) data).toExcept with
    | .error _ => true
    | .ok _ => false
  let accepts := fun (data : ByteArray) =>
    match (Binary.Get.run (Binary.getThe Message) data).toExcept with
    | .ok _ => true
    | .error _ => false
  accepts ⟨#[0x08, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01]⟩ &&
  accepts ⟨#[0xf8, 0xff, 0xff, 0xff, 0x0f, 0x01]⟩ &&
  rejects ⟨#[0x08, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x02]⟩ &&
  rejects ⟨#[0x08, 0x80]⟩ &&
  rejects ⟨#[0x00, 0x00]⟩ &&
  rejects ⟨#[0x80, 0x80, 0x80, 0x80, 0x10, 0x00]⟩ &&
  rejects ⟨#[0x0e]⟩ &&
  rejects ⟨#[0x09, 0x01, 0x02, 0x03]⟩ &&
  rejects ⟨#[0x0d, 0x01, 0x02, 0x03]⟩ &&
  rejects ⟨#[0x0a, 0x05, 0x01, 0x02]⟩ &&
  rejects ⟨#[0x0a, 0x80, 0x80, 0x80, 0x80, 0x08]⟩

/-- info: true -/
#guard_msgs (info) in
#eval
  let decode := fun (data : ByteArray) =>
    (Binary.Get.run (Binary.getThe Message) data).toExcept
  let valid :=
    match decode ⟨#[0x43, 0x08, 0x02, 0x44]⟩ with
    | .ok message =>
      message.records.size == 1 &&
        match message.records[0]!.value with
        | .GROUPED sub => sub.records.size == 1
        | _ => false
    | .error _ => false
  let rejects := fun (data : ByteArray) =>
    match decode data with
    | .error _ => true
    | .ok _ => false
  valid && rejects ⟨#[0x43, 0x3c]⟩ && rejects ⟨#[0x44]⟩ && rejects ⟨#[0x43]⟩

/-- info: true -/
#guard_msgs (info) in
#eval
  let encoded : ByteArray := ⟨#[
    0x08, 0x96, 0x01,
    0x11, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
    0x1a, 0x03, 0xaa, 0xbb, 0xcc,
    0x23, 0x08, 0x07, 0x24,
    0x2d, 0x78, 0x56, 0x34, 0x12
  ]⟩
  match (Binary.Get.run (Binary.getThe Message) encoded).toExcept with
  | .ok message =>
    message.records.size == 5 &&
      message.records[0]!.value.isVARINT &&
      message.records[1]!.value.isI64 &&
      message.records[2]!.value.isLEN &&
      message.records[3]!.value.isGROUPED &&
      message.records[4]!.value.isI32
  | .error _ => false

end Test.EncodingWire
