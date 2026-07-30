module

import Protobuf

open Protobuf
open scoped Protobuf.Notation

-- More fields than a generated encoder/decoder chunk.  The two final field
-- names deliberately resemble generated helper names: helpers live below the
-- already-reserved `toMessage`/`fromMessage` namespaces and cannot collide
-- with these ordinary one-segment projections.
message WideCodegen {
  int32 f01 = 1;
  int32 f02 = 2;
  int32 f03 = 3;
  int32 f04 = 4;
  int32 f05 = 5;
  int32 f06 = 6;
  int32 f07 = 7;
  int32 f08 = 8;
  int32 f09 = 9;
  int32 f10 = 10;
  int32 f11 = 11;
  int32 f12 = 12;
  int32 f13 = 13;
  int32 f14 = 14;
  int32 f15 = 15;
  int32 f16 = 16;
  int32 toMessage_chunk_0 = 17;
  int32 fromMessage_chunk_0 = 18;
}

#check WideCodegen.«protobuf.internal».toMessage._chunk_0
#check WideCodegen.«protobuf.internal».toMessage._chunk_1
#check WideCodegen.«protobuf.internal».fromMessage._chunk_0
#check WideCodegen.«protobuf.internal».fromMessage._chunk_1
#synth SizeOf WideCodegen

#eval! (do
  let expected : WideCodegen := {
    f01 := -1
    f16 := 16
    toMessage_chunk_0 := 17
    fromMessage_chunk_0 := 18
  }
  let wire ← IO.ofExcept (Protobuf.encode expected)
  let actual ← IO.ofExcept (Protobuf.decodeThe WideCodegen wire)
  unless actual.f01 == -1 &&
      actual.f16 == 16 &&
      actual.toMessage_chunk_0 == 17 &&
      actual.fromMessage_chunk_0 == 18 do
    throw (IO.userError "wide generated helper roundtrip failed")

  let hasUnknownLen
      (fields : Std.HashMap Nat (Array Encoding.ProtoVal))
      (fieldNum : Nat) : Bool :=
    match fields[fieldNum]? with
    | some values => values.any (·.isLEN)
    | none => false
  let decodeRecords (records : Array Encoding.Record) :=
    IO.ofExcept <|
      WideCodegen.«protobuf.internal».fromMessage { records }

  let lowWrongFirst ← decodeRecords #[
    { fieldNum := 1, value := .LEN ByteArray.empty },
    { fieldNum := 1, value := .VARINT 7 }
  ]
  let lowWrongLast ← decodeRecords #[
    { fieldNum := 1, value := .VARINT 7 },
    { fieldNum := 1, value := .LEN ByteArray.empty }
  ]
  unless lowWrongFirst.f01 == 7 && lowWrongLast.f01 == 7 &&
      hasUnknownLen lowWrongFirst.«Unknown.Fields» 1 &&
      hasUnknownLen lowWrongLast.«Unknown.Fields» 1 do
    throw (IO.userError
      "small generated dispatch did not preserve wrong-wire scalar data")

  let highWrongFirst ← decodeRecords #[
    { fieldNum := 18, value := .LEN ByteArray.empty },
    { fieldNum := 18, value := .VARINT 9 }
  ]
  let highWrongLast ← decodeRecords #[
    { fieldNum := 18, value := .VARINT 9 },
    { fieldNum := 18, value := .LEN ByteArray.empty }
  ]
  unless highWrongFirst.fromMessage_chunk_0 == 9 &&
      highWrongLast.fromMessage_chunk_0 == 9 &&
      hasUnknownLen highWrongFirst.«Unknown.Fields» 18 &&
      hasUnknownLen highWrongLast.«Unknown.Fields» 18 do
    throw (IO.userError
      "chunked generated dispatch did not preserve wrong-wire scalar data")
  : IO Unit)
