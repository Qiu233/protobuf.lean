module

import Protobuf

open Protobuf Encoding
open scoped Protobuf.Notation

message ExtensionHost {
}

extend ExtensionHost {
  repeated fixed32 values = 100 [packed = true];
  optional int32 scalar = 101;
  repeated int32 numbers = 102 [packed = true];
  optional int32 with_default = 103 [default = 17];
}

private def assert (condition : Bool) (failure : String) : IO Unit := do
  unless condition do
    throw (IO.userError failure)

private def ofProtoExcept (result : Except ProtoError α) : IO α := do
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.toString)

public def main : IO Unit := do
  -- Although this extension prefers packed output, its accessor must accept a
  -- wire stream that freely mixes packed and unpacked occurrences.
  let packed : ProtoVal := .LEN ⟨#[
    0x01, 0x00, 0x00, 0x00,
    0x78, 0x56, 0x34, 0x12
  ]⟩
  let unpacked : ProtoVal := .I32 (0x90abcdef : UInt32).toBitVec
  let value : ExtensionHost := {
    «Unknown.Fields» :=
      ({} : Std.HashMap Nat (Array ProtoVal)).insert 100 #[packed, unpacked]
  }
  let decoded ← ofProtoExcept (ExtensionHost.get_values? value)
  assert (decoded == #[
    (1 : UInt32),
    (0x12345678 : UInt32),
    (0x90abcdef : UInt32)
  ]) "packed extension accessor rejected or reordered unpacked data"

  let set ← ofProtoExcept (ExtensionHost.set_values default #[(1 : UInt32), 2])
  let some stored := set.«Unknown.Fields»[100]?
    | throw (IO.userError "extension setter did not store its wire value")
  assert (stored.size == 1 && stored[0]!.isLEN)
    "packed extension setter did not emit packed representation"

  let mixedScalar : ExtensionHost := {
    «Unknown.Fields» :=
      ({} : Std.HashMap Nat (Array ProtoVal)).insert 101 #[
        .VARINT 7,
        .I32 (0xdeadbeef : UInt32).toBitVec
      ]
  }
  assert ((← ofProtoExcept (ExtensionHost.get_scalar? mixedScalar)) == some (7 : Int32))
    "singular extension getter rejected a valid value followed by wrong-wire unknown data"
  assert (ExtensionHost.has_scalar mixedScalar)
    "singular extension presence ignored its valid wire value"
  let replacedScalar ←
    ofProtoExcept (ExtensionHost.set_scalar mixedScalar (9 : Int32))
  assert ((← ofProtoExcept (ExtensionHost.get_scalar? replacedScalar)) == some (9 : Int32))
    "singular extension setter did not replace its compatible wire value"
  let some replacedRaw := replacedScalar.«Unknown.Fields»[101]?
    | throw (IO.userError "singular extension setter lost its storage")
  assert (replacedRaw.any (·.isI32))
    "singular extension setter discarded wrong-wire unknown data with the same tag"

  let wrongOnly : ExtensionHost := {
    «Unknown.Fields» :=
      ({} : Std.HashMap Nat (Array ProtoVal)).insert 101 #[
        .I32 (7 : UInt32).toBitVec
      ]
  }
  assert ((← ofProtoExcept (ExtensionHost.get_scalar? wrongOnly)).isNone)
    "wrong-wire-only extension produced a value"
  assert (!ExtensionHost.has_scalar wrongOnly)
    "wrong-wire-only extension incorrectly reported presence"

  let mixedRepeated : ExtensionHost := {
    «Unknown.Fields» :=
      ({} : Std.HashMap Nat (Array ProtoVal)).insert 102 #[
        .VARINT 1,
        .I32 (7 : UInt32).toBitVec,
        .VARINT 2
      ]
  }
  assert ((← ofProtoExcept (ExtensionHost.get_numbers? mixedRepeated)) ==
      #[(1 : Int32), 2])
    "repeated extension getter did not filter wrong-wire records"

  let cleared ← ofProtoExcept (ExtensionHost.set_values set #[])
  assert (cleared.«Unknown.Fields»[100]?.isNone)
    "setting an empty packed extension should remove its wire record"
  assert (!ExtensionHost.has_values cleared)
    "an empty packed extension incorrectly reported presence"

  assert ((← ofProtoExcept (ExtensionHost.get_with_default? default)).isNone)
    "extension value default manufactured presence"
  assert ((← ofProtoExcept (ExtensionHost.get_with_default default)) == (17 : Int32))
    "extension value getter did not apply its explicit schema default"
  assert (!ExtensionHost.has_with_default default)
    "extension value default incorrectly reported presence"
