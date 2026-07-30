module

import Protobuf

open Protobuf Encoding
open scoped Protobuf.Notation

#load_proto_file "Test/ClosedEnumProto2.proto"
#load_proto_file "Test/ClosedEnumEditions.proto"

private def assert (condition : Bool) (failure : String) : IO Unit := do
  unless condition do
    throw (IO.userError failure)

private def ofProtoExcept (result : Except ProtoError α) : IO α :=
  IO.ofExcept result

private def unknownVarints
    (fields : Std.HashMap Nat (Array ProtoVal)) (number : Nat) : Array Nat :=
  (fields[number]?).getD #[] |>.filterMap ProtoVal.isVARINT?

private def compositeWire : ByteArray :=
  ⟨#[
    0x08, 0x7b,
    0x10, 0x01, 0x10, 0x7b, 0x10, 0x00,
    0x1a, 0x03, 0x01, 0x7b, 0x00,
    0x22, 0x04, 0x08, 0x07, 0x10, 0x7b,
    0x22, 0x04, 0x08, 0x08, 0x10, 0x01,
    0x28, 0x7b,
    0xa0, 0x06, 0x7b,
    0xa8, 0x06, 0x01, 0xa8, 0x06, 0x7b, 0xa8, 0x06, 0x00,
    0xb2, 0x06, 0x03, 0x01, 0x7b, 0x00
  ]⟩

private def testProto2 : IO Unit := do
  let value ← ofProtoExcept (Protobuf.decodeThe _root_.test.closed.proto2.ClosedMessage compositeWire)
  assert value.singular.isNone "closed singular enum accepted an unknown value"
  assert (value.expanded == #[
    _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE,
    _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ZERO
  ]) "closed expanded enum did not filter unknown values"
  assert (value.packed == #[
    _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE,
    _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ZERO
  ]) "closed packed enum did not filter unknown values"
  assert (value.mapped.size == 1 &&
    value.mapped[(8 : Int32)]? ==
      some _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE)
    "map entry with an unknown closed enum was not moved to unknown fields"
  assert value.choice.isNone "unknown closed enum selected a oneof case"
  assert (unknownVarints value.«Unknown.Fields» 1 == #[123])
    "singular closed-enum unknown value was not retained"
  assert (unknownVarints value.«Unknown.Fields» 2 == #[123])
    "expanded closed-enum unknown value was not retained"
  assert (unknownVarints value.«Unknown.Fields» 3 == #[123])
    "packed closed-enum unknown value was not expanded into unknown fields"
  assert (((value.«Unknown.Fields»[4]?).getD #[]).size == 1)
    "closed-enum map entry was not retained as one outer unknown record"
  assert (unknownVarints value.«Unknown.Fields» 5 == #[123])
    "closed-enum oneof unknown value was not retained"

  assert (!( _root_.test.closed.proto2.ClosedMessage.has_singular_ext value))
    "unknown-only singular closed enum extension reported presence"
  assert ((← ofProtoExcept
      (_root_.test.closed.proto2.ClosedMessage.get_singular_ext? value)).isNone)
    "unknown singular closed enum extension leaked into the typed getter"
  assert ((← ofProtoExcept
      (_root_.test.closed.proto2.ClosedMessage.get_expanded_ext? value)) == #[
        _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE,
        _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ZERO
      ]) "expanded closed enum extension did not filter unknown values"
  assert ((← ofProtoExcept
      (_root_.test.closed.proto2.ClosedMessage.get_packed_ext? value)) == #[
        _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE,
        _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ZERO
      ]) "packed closed enum extension did not filter unknown values"

  let singularSet ← ofProtoExcept
    (_root_.test.closed.proto2.ClosedMessage.set_singular_ext value
      _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE)
  assert ((unknownVarints singularSet.«Unknown.Fields» 100).contains 123)
    "setting a singular closed enum extension discarded its unknown value"
  assert ((← ofProtoExcept
      (_root_.test.closed.proto2.ClosedMessage.get_singular_ext?
        singularSet)) ==
      some _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE)
    "setting a singular closed enum extension did not install the known value"

  let expandedSet ← ofProtoExcept
    (_root_.test.closed.proto2.ClosedMessage.set_expanded_ext value #[
      _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE
    ])
  assert ((unknownVarints expandedSet.«Unknown.Fields» 101).contains 123)
    "setting an expanded closed enum extension discarded its unknown value"
  assert ((← ofProtoExcept
      (_root_.test.closed.proto2.ClosedMessage.get_expanded_ext?
        expandedSet)) == #[
      _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE
    ]) "setting an expanded closed enum extension leaked an unknown value"

  let packedSet ← ofProtoExcept
    (_root_.test.closed.proto2.ClosedMessage.set_packed_ext value #[
      _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE
    ])
  assert (unknownVarints packedSet.«Unknown.Fields» 102 == #[123])
    "setting a packed closed enum extension discarded its unknown value"
  assert ((← ofProtoExcept
      (_root_.test.closed.proto2.ClosedMessage.get_packed_ext? packedSet)) == #[
      _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE
    ]) "setting a packed closed enum extension leaked an unknown value"

  let overlongPackedBase :
      _root_.test.closed.proto2.ClosedMessage := default
  let overlongPacked : _root_.test.closed.proto2.ClosedMessage :=
    { overlongPackedBase with
      «Unknown.Fields» := ({} : Std.HashMap Nat (Array ProtoVal)).insert 102 #[
        .LEN ⟨#[
          0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0x01
        ]⟩
      ] }
  let overlongPackedSet ← ofProtoExcept
    (_root_.test.closed.proto2.ClosedMessage.set_packed_ext
      overlongPacked #[])
  assert (unknownVarints overlongPackedSet.«Unknown.Fields» 102 ==
      #[0xffffffff])
    "packed closed enum extension did not canonicalize its unknown int32"

  let knownThenUnknown := Message.mk #[
    ⟨1, .VARINT 1⟩,
    ⟨1, .VARINT 123⟩,
    ⟨5, .VARINT 1⟩,
    ⟨5, .VARINT 123⟩
  ]
  let ordered ← ofProtoExcept
    (_root_.test.closed.proto2.ClosedMessage.«protobuf.internal».fromMessage knownThenUnknown)
  assert (ordered.singular ==
      some _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE)
    "unknown closed enum overwrote a previously known singular value"
  assert (match ordered.choice with
    | some (.selected value) =>
        value == _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE
    | _ => false)
    "unknown closed enum overwrote a previously selected oneof case"

  let packedNegative := Message.mk #[
    ⟨2, .VARINT 0xffffffffffffffff⟩,
    ⟨3, .LEN ⟨#[
      0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0x01
    ]⟩⟩,
    ⟨3, .LEN ⟨#[0x81, 0x80, 0x80, 0x80, 0x10]⟩⟩
  ]
  let edge ← ofProtoExcept
    (_root_.test.closed.proto2.ClosedMessage.«protobuf.internal».fromMessage packedNegative)
  assert (edge.packed == #[
      _root_.test.closed.proto2.ClosedEnum.CLOSED_ENUM_ONE])
    "packed closed enum did not recognize a value after int32 truncation"
  assert (unknownVarints edge.«Unknown.Fields» 2 == #[0xffffffffffffffff])
    "expanded closed enum did not preserve the original uint64 varint"
  assert (unknownVarints edge.«Unknown.Fields» 3 == #[0xffffffff])
    "packed closed enum did not canonicalize an unknown value as uint32"

  let entry := Message.mk #[
    ⟨1, .VARINT 7⟩,
    ⟨2, .VARINT 123⟩,
    ⟨2, .VARINT 1⟩
  ]
  let outer := Message.mk #[⟨4, ← ofProtoExcept (ProtoVal.ofMessage entry)⟩]
  let mapped ← ofProtoExcept
    (_root_.test.closed.proto2.ClosedMessage.«protobuf.internal».fromMessage outer)
  assert mapped.mapped.isEmpty
    "map entry containing both unknown and known closed enum values was accepted"
  assert (((mapped.«Unknown.Fields»[4]?).getD #[]).size == 1)
    "rejected closed-enum map entry was not retained"

  match _root_.test.closed.proto2.ClosedEnum.«protobuf.internal».builder
      (_root_.test.closed.proto2.ClosedEnum.«Unknown.Value» 123) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "closed enum builder accepted Unknown.Value")

private def testEditions : IO Unit := do
  let editionWire : ByteArray := ⟨compositeWire.data.extract 0 27⟩
  let value ← ofProtoExcept
    (Protobuf.decodeThe _root_.test.closed.editions.ClosedMessage editionWire)
  assert value.singular.isNone "Editions CLOSED singular accepted unknown"
  assert (value.expanded == #[
    _root_.test.closed.editions.ClosedEnum.CLOSED_ENUM_ONE,
    _root_.test.closed.editions.ClosedEnum.CLOSED_ENUM_ZERO
  ]) "Editions CLOSED expanded field did not filter unknown"
  assert (value.packed == #[
    _root_.test.closed.editions.ClosedEnum.CLOSED_ENUM_ONE,
    _root_.test.closed.editions.ClosedEnum.CLOSED_ENUM_ZERO
  ]) "Editions CLOSED packed field did not filter unknown"
  assert (value.mapped.size == 1 && value.mapped.contains (8 : Int32))
    "Editions CLOSED map semantics differ from proto2"
  assert value.choice.isNone "Editions CLOSED unknown selected a oneof"

public def main : IO Unit := do
  testProto2
  testEditions

#eval! main
