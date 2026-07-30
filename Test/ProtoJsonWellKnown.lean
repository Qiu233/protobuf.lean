module

import Protobuf

open Lean
open Protobuf
open Protobuf.Reflection
open Protobuf.Json
open scoped Protobuf.Notation

#load_proto_file "Test/ProtoJsonWellKnown.proto"

private def assert (condition : Bool) (failure : String) : IO Unit := do
  unless condition do
    throw (IO.userError failure)

private def ofIOExcept [ToString ε] (result : IO (Except ε α)) : IO α := do
  IO.ofExcept (← result)

private def descriptor : MessageDescriptor :=
  messageDescriptor test.protojson.WellKnownHost

private def parse (text : String) : IO DynamicMessage :=
  ofIOExcept <| dynamicOfJsonString descriptor text
    ParseOptions.withGeneratedPool

private def normalize (text : String) : IO String := do
  let value ← parse text
  ofIOExcept <| dynamicToJsonString value PrintOptions.withGeneratedPool

private def expectParseFailure (text failure : String) : IO Unit := do
  match ← dynamicOfJsonString descriptor text ParseOptions.withGeneratedPool with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError failure)

private def testTimestampAndDuration : IO Unit := do
  assert
    ((← normalize
      "{\"optionalTimestamp\":\"1969-12-31T16:00:00-08:00\"}") ==
      "{\"optionalTimestamp\":\"1970-01-01T00:00:00Z\"}")
    "Timestamp was not normalized to UTC"
  assert
    ((← normalize
      "{\"optionalTimestamp\":\"1970-01-01T00:00:00.010000000Z\"}") ==
      "{\"optionalTimestamp\":\"1970-01-01T00:00:00.010Z\"}")
    "Timestamp fractional digits were not normalized"
  expectParseFailure
    "{\"optionalTimestamp\":\"0001-01-01t00:00:00Z\"}"
    "lowercase Timestamp separator was accepted"
  assert
    ((← normalize
      "{\"optionalDuration\":\"-315576000000.999999999s\"}") ==
      "{\"optionalDuration\":\"-315576000000.999999999s\"}")
    "minimum Duration did not round trip"
  expectParseFailure
    "{\"optionalDuration\":\"315576000001s\"}"
    "out-of-range Duration was accepted"

private def testStructuredWellKnownTypes : IO Unit := do
  assert
    ((← normalize "{\"optionalFieldMask\":\"foo,barBaz\"}") ==
      "{\"optionalFieldMask\":\"foo,barBaz\"}")
    "FieldMask did not round trip"
  expectParseFailure
    "{\"optionalFieldMask\":\"foo_bar\"}"
    "FieldMask JSON with an underscore was accepted"
  let structured ← normalize
    "{\"optionalStruct\":{\"nil\":null,\"n\":1,\"xs\":[true,\"x\"]}}"
  assert
    (structured ==
      "{\"optionalStruct\":{\"n\":1,\"nil\":null,\"xs\":[true,\"x\"]}}")
    s!"Struct/Value/ListValue mapping is wrong: {structured}"
  assert
    ((← normalize "{\"optionalInt32Wrapper\":0}") ==
      "{\"optionalInt32Wrapper\":0}")
    "wrapper default value lost presence"

private def testAny : IO Unit := do
  assert
    ((← normalize
      "{\"optionalAny\":{\"@type\":\"type.googleapis.com/test.protojson.Payload\",\"optionalInt32\":123}}") ==
      "{\"optionalAny\":{\"@type\":\"type.googleapis.com/test.protojson.Payload\",\"optionalInt32\":123}}")
    "ordinary Any payload did not round trip"
  assert
    ((← normalize
      "{\"optionalAny\":{\"@type\":\"type.googleapis.com/google.protobuf.Duration\",\"value\":\"1.500s\"}}") ==
      "{\"optionalAny\":{\"@type\":\"type.googleapis.com/google.protobuf.Duration\",\"value\":\"1.500s\"}}")
    "well-known Any payload did not round trip"
  assert ((← normalize "{\"optionalAny\":{}}") == "{\"optionalAny\":{}}")
    "empty Any did not round trip"
  expectParseFailure
    "{\"optionalAny\":{\"@type\":\"not_a_url\",\"value\":\"\"}}"
    "non-URL Any type was accepted"

private def testNullAndNumericEdges : IO Unit := do
  assert
    ((← normalize "{\"oneofNullValue\":\"NULL_VALUE\"}") ==
      "{\"oneofNullValue\":null}")
    "google.protobuf.NullValue was not emitted as JSON null"
  assert
    ((← normalize
      "{\"oneofUint32\":null,\"oneofString\":\"test\"}") ==
      "{\"oneofString\":\"test\"}")
    "null incorrectly selected a oneof case"
  expectParseFailure
    "{\"mapInt32Int32\":{\"0\":null}}"
    "null map scalar value was accepted"
  expectParseFailure
    "{\"optionalFloat\":3.502823e+38}"
    "out-of-range float was accepted"
  expectParseFailure
    "{\"optionalInt32Wrapper\":1,\"optionalInt32Wrapper\":2}"
    "duplicate JSON object key was accepted"
  expectParseFailure
    "{\"optionalStringWrapper\":\"\\uD800\"}"
    "unpaired high surrogate was accepted"
  expectParseFailure
    "{\"optionalStringWrapper\":\"\\uDC00\"}"
    "unpaired low surrogate was accepted"
  expectParseFailure
    "{\"optionalStringWrapper\":\"\\uDE01\\uD83D\"}"
    "reversed surrogate pair was accepted"

public def main : IO Unit := do
  testTimestampAndDuration
  testStructuredWellKnownTypes
  testAny
  testNullAndNumericEdges
