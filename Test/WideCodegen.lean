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
  : IO Unit)
