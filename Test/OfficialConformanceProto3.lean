module

import Protobuf

open Protobuf
open scoped Protobuf.Notation

-- This is the schema used by the upstream protobuf conformance and fuzz
-- suites.  Loading it here is deliberately a compile-time test: protoc
-- descriptors must be converted into ordinary Lean declarations, including
-- all imported well-known types, without a runtime descriptor interpreter.
#load_proto_file "Test/official/google/protobuf/test_messages_proto3.proto" in "Test/official"

#check _root_.protobuf_test_messages.proto3.TestAllTypesProto3
#check _root_.google.protobuf.Any
#check _root_.google.protobuf.Struct

#check _root_.protobuf_test_messages.proto3.TestAllTypesProto3.encode
#check _root_.protobuf_test_messages.proto3.TestAllTypesProto3.decode
#check _root_.protobuf_test_messages.proto3.TestAllTypesProto3.«protobuf.internal».toMessage._chunk_0
#check _root_.protobuf_test_messages.proto3.TestAllTypesProto3.«protobuf.internal».fromMessage._chunk_0

#eval! (do
  -- Native-compiling a value of TestAllTypesProto3 itself would require Lean
  -- to lower a 141-argument structure constructor.  Exercise generated code
  -- from the same official schema with a compact message instead; the wide
  -- helpers above are typechecked here and run with non-default data in
  -- Test/WideCodegen.lean.
  let expected :
      _root_.protobuf_test_messages.proto3.ForeignMessage := { c := 123 }
  let wire ← IO.ofExcept <|
    _root_.protobuf_test_messages.proto3.ForeignMessage.encode expected
  let decoded ← IO.ofExcept <|
    _root_.protobuf_test_messages.proto3.ForeignMessage.decode wire
  unless decoded.c == 123 do
    throw (IO.userError "official conformance message roundtrip failed")
  pure ()
  : IO Unit)
