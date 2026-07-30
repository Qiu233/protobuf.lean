module

import Protobuf

open Protobuf Encoding
open scoped Protobuf.Notation

#load_proto_file "Test/Utf8NoneProto2.proto"
#load_proto_file "Test/Utf8NoneEditions.proto"

private def assert (condition : Bool) (failure : String) : IO Unit := do
  unless condition do
    throw (IO.userError failure)

private def ofProtoExcept (result : Except ProtoError α) : IO α :=
  IO.ofExcept result

private def raw (bytes : Array UInt8) : UnvalidatedString :=
  .ofBytes ⟨bytes⟩

private def rawWire : ByteArray :=
  ⟨#[
    0x0a, 0x03, 0xff, 0xfe, 0x61,
    0x12, 0x02, 0xc3, 0x28,
    0x12, 0x02, 0x6f, 0x6b,
    0x1a, 0x07, 0x0a, 0x01, 0xff, 0x12, 0x02, 0xc3, 0x28,
    0x22, 0x02, 0xff, 0x61,
    0xa2, 0x06, 0x02, 0xff, 0x62,
    0xaa, 0x06, 0x02, 0xfe, 0x63,
    0xaa, 0x06, 0x02, 0x6f, 0x6b
  ]⟩

private def testProto2 : IO Unit := do
  let absent : _root_.test.utf8.proto2.RawStrings := default
  assert
    (_root_.test.utf8.proto2.RawStrings.«Explicit.Default.Accessors».singular.get
      absent == raw #[0xff])
    "proto2 invalid UTF-8 schema default was not preserved by its value accessor"
  assert
    (!_root_.test.utf8.proto2.RawStrings.«Explicit.Default.Accessors».singular.has
      absent)
    "proto2 invalid UTF-8 schema default manufactured presence"
  let value ← ofProtoExcept
    (Protobuf.decodeThe _root_.test.utf8.proto2.RawStrings rawWire)
  assert (value.singular == some (raw #[0xff, 0xfe, 0x61]))
    "proto2 singular string did not preserve invalid UTF-8"
  assert (value.repeated == #[raw #[0xc3, 0x28], raw #[0x6f, 0x6b]])
    "proto2 repeated string did not preserve invalid UTF-8"
  assert (value.mapped[(raw #[0xff])]? == some (raw #[0xc3, 0x28]))
    "proto2 map string key/value did not preserve invalid UTF-8"
  assert (match value.choice with
    | some (.selected selected) => selected == raw #[0xff, 0x61]
    | _ => false)
    "proto2 oneof string did not preserve invalid UTF-8"
  assert ((← ofProtoExcept
      (_root_.test.utf8.proto2.RawStrings.get_singular_ext? value)) ==
        some (raw #[0xff, 0x62]))
    "proto2 string extension did not preserve invalid UTF-8"
  assert ((← ofProtoExcept
      (_root_.test.utf8.proto2.RawStrings.get_repeated_ext? value)) ==
        #[raw #[0xfe, 0x63], raw #[0x6f, 0x6b]])
    "proto2 repeated string extension did not preserve invalid UTF-8"
  let encoded ← ofProtoExcept
    (Protobuf.encode value)
  let reparsed ← ofProtoExcept
    (Protobuf.decodeThe _root_.test.utf8.proto2.RawStrings encoded)
  assert (reparsed.singular == value.singular &&
      reparsed.repeated == value.repeated &&
      reparsed.mapped[(raw #[0xff])]? == value.mapped[(raw #[0xff])]?)
    "proto2 invalid UTF-8 was not stable across reserialization"

private def testEditions : IO Unit := do
  let editionWire : ByteArray := ⟨rawWire.data.extract 0 26⟩
  let value ← ofProtoExcept
    (Protobuf.decodeThe _root_.test.utf8.editions.RawStrings editionWire)
  assert (value.singular == some (raw #[0xff, 0xfe, 0x61]))
    "Editions NONE singular string did not preserve invalid UTF-8"
  assert (value.repeated == #[raw #[0xc3, 0x28], raw #[0x6f, 0x6b]])
    "Editions NONE repeated string did not preserve invalid UTF-8"
  assert (value.mapped[(raw #[0xff])]? == some (raw #[0xc3, 0x28]))
    "Editions NONE map did not inherit UTF-8 behavior"
  assert (match value.choice with
    | some (.selected selected) => selected == raw #[0xff, 0x61]
    | _ => false)
    "Editions NONE oneof did not inherit UTF-8 behavior"

  let invalidVerified : ByteArray := ⟨#[0x32, 0x01, 0xff]⟩
  match
      Protobuf.decodeThe _root_.test.utf8.editions.RawStrings invalidVerified with
  | .error (.invalidBuffer _) => pure ()
  | .error error =>
      throw (IO.userError s!"VERIFY returned the wrong error: {error}")
  | .ok _ =>
      throw (IO.userError "field-level VERIFY accepted invalid UTF-8")

public def main : IO Unit := do
  testProto2
  testEditions

#eval! main
