module

import Protobuf.Encoding
import Protobuf.Reflection
meta import Protobuf.Notation
meta import Protobuf.Elab

open Protobuf Encoding
open scoped Protobuf.Notation

#load_proto_file "Test/official/google/protobuf/unittest_proto3.proto" in "Test/official"

#check _root_.proto3_unittest.TestAllTypes

private def packedSample : _root_.proto3_unittest.TestPackedTypes := {
  (default : _root_.proto3_unittest.TestPackedTypes) with
  packed_int32 := #[(150 : Int32), (-1 : Int32)]
  packed_sint32 := #[(-1 : Int32), (1 : Int32)]
  packed_fixed32 := #[(0x12345678 : UInt32)]
}

private def expectedPackedWire : ByteArray := ⟨#[
  0xd2, 0x05, 0x0c, 0x96, 0x01,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01,
  0xf2, 0x05, 0x02, 0x01, 0x02,
  0x82, 0x06, 0x04, 0x78, 0x56, 0x34, 0x12
]⟩

private def allTypesSample : _root_.proto3_unittest.TestAllTypes := {
  (default : _root_.proto3_unittest.TestAllTypes) with
  optional_int32 := (-1 : Int32)
  optional_sint32 := (-2 : Int32)
  optional_string := "hi"
  optional_nested_enum := _root_.proto3_unittest.TestAllTypes.NestedEnum.NEG
  repeated_int32 := #[(1 : Int32), (150 : Int32), (-1 : Int32)]
  repeated_sint32 := #[(-1 : Int32), (1 : Int32)]
}

private def expectedAllTypesWire : ByteArray := ⟨#[
  0x08, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01,
  0x28, 0x03,
  0x72, 0x02, 0x68, 0x69,
  0xa8, 0x01, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01,
  0xfa, 0x01, 0x0d, 0x01, 0x96, 0x01,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01,
  0x9a, 0x02, 0x02, 0x01, 0x02
]⟩

/-- info: true -/
#guard_msgs (info) in
#eval
  match packedSample.encode with
  | .ok wire => wire == expectedPackedWire
  | .error _ => false

/-- info: true -/
#guard_msgs (info) in
#eval
  match allTypesSample.encode with
  | .ok wire => wire == expectedAllTypesWire
  | .error _ => false

/-- info: true -/
#guard_msgs (info) in
#eval
  match _root_.proto3_unittest.TestPackedTypes.decode expectedPackedWire with
  | .ok value =>
      value.packed_int32 == #[(150 : Int32), (-1 : Int32)] &&
      value.packed_sint32 == #[(-1 : Int32), (1 : Int32)] &&
      value.packed_fixed32 == #[(0x12345678 : UInt32)]
  | .error _ => false
