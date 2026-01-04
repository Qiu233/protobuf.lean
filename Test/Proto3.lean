module

import Protobuf.Encoding
meta import Protobuf.Notation
meta import Protobuf.Elab

open Protobuf Encoding
open scoped Protobuf.Notation

set_option protobuf.trace.notation true

#load_proto_file "Test/Proto3.proto"

def ofExcept {α} (e : Except ProtoError α) : IO α := do
  match e with
  | .ok v => pure v
  | .error err => throw (IO.userError err.toString)

def assert (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def assertEq [BEq α] (a b : α) (msg : String) : IO Unit := do
  assert (a == b) msg

def testDefaults : IO Unit := do
  let val : _root_.test.proto3.All := default
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  assert msg.records.isEmpty "proto3 defaults should not serialize"
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage Message.empty)
  assertEq decoded.int32_field (0 : Int32) "default int32_field mismatch"
  assertEq decoded.string_field "" "default string_field mismatch"
  assertEq decoded.bool_field false "default bool_field mismatch"
  assertEq decoded.bytes_field ByteArray.empty "default bytes_field mismatch"
  assertEq decoded.float_field (0 : Float32) "default float_field mismatch"
  assertEq decoded.double_field (0 : Float) "default double_field mismatch"
  assertEq decoded.uint32_field (0 : UInt32) "default uint32_field mismatch"
  assertEq decoded.uint64_field (0 : UInt64) "default uint64_field mismatch"
  assertEq decoded.sint32_field (0 : Int32) "default sint32_field mismatch"
  assertEq decoded.sint64_field (0 : Int64) "default sint64_field mismatch"
  assertEq decoded.fixed32_field (0 : UInt32) "default fixed32_field mismatch"
  assertEq decoded.fixed64_field (0 : UInt64) "default fixed64_field mismatch"
  assertEq decoded.sfixed32_field (0 : Int32) "default sfixed32_field mismatch"
  assertEq decoded.sfixed64_field (0 : Int64) "default sfixed64_field mismatch"
  assertEq decoded.color _root_.test.proto3.Color.COLOR_UNSPECIFIED "default enum mismatch"
  assert decoded.sub.isNone "default sub mismatch"
  assertEq decoded.opt_int32 none "default opt_int32 mismatch"
  assertEq decoded.rep_int32 #[] "default rep_int32 mismatch"
  assertEq decoded.rep_int32_unpacked #[] "default rep_int32_unpacked mismatch"
  assertEq decoded.rep_color #[] "default rep_color mismatch"
  assert (decoded.map_str_int32.size == 0) "default map mismatch"
  assert decoded.choice.isNone "default choice mismatch"
  assert decoded.rep_sub.isEmpty "default rep_sub mismatch"

def testOptionalPresence : IO Unit := do
  let base : _root_.test.proto3.All := default
  let val : _root_.test.proto3.All := { base with opt_int32 := some 0 }
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  assert ((Message.getRecordsOf msg 17).size == 1) "optional field should serialize when set"
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.opt_int32 (some (0 : Int32)) "optional presence mismatch"

def testSubPresence : IO Unit := do
  let sub : _root_.test.proto3.Sub := { id := 0 }
  let base : _root_.test.proto3.All := default
  let val : _root_.test.proto3.All := { base with sub := some sub }
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  assert ((Message.getRecordsOf msg 16).size == 1) "message field should serialize when present"
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  match decoded.sub with
  | some v => assertEq v.id (0 : Int32) "message field presence mismatch"
  | none => throw (IO.userError "message field presence mismatch")

def testOneof : IO Unit := do
  let choice : _root_.test.proto3.All.choice_Type := _root_.test.proto3.All.choice_Type.oneof_int32 7
  let base : _root_.test.proto3.All := default
  let val : _root_.test.proto3.All := { base with choice := some choice }
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  assert ((Message.getRecordsOf msg 22).size == 1) "oneof field did not serialize"
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  match decoded.choice with
  | some (.oneof_int32 v) => assertEq v (7 : Int32) "oneof int32 value mismatch"
  | _ => throw (IO.userError "oneof decode mismatch")

def testPackedAndUnpacked : IO Unit := do
  let base : _root_.test.proto3.All := default
  let val : _root_.test.proto3.All := {
    base with
    rep_int32 := #[(1 : Int32), 2],
    rep_int32_unpacked := #[(3 : Int32), 4]
  }
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  let repPacked := Message.getRecordsOf msg 18
  assert (repPacked.size == 1) "packed repeated field should be a single record"
  match repPacked[0]!.value with
  | .LEN _ => pure ()
  | _ => throw (IO.userError "packed repeated field should use LEN wire type")
  let repUnpacked := Message.getRecordsOf msg 19
  assert (repUnpacked.size == 2) "unpacked repeated field should be multiple records"
  for r in repUnpacked do
    match r.value with
    | .VARINT _ => pure ()
    | _ => throw (IO.userError "unpacked repeated field should use VARINT wire type")
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.rep_int32 #[(1 : Int32), 2] "packed repeated decode mismatch"
  assertEq decoded.rep_int32_unpacked #[(3 : Int32), 4] "unpacked repeated decode mismatch"

def testPackedAcceptsUnpacked : IO Unit := do
  let msg := Message.set Message.empty 18 (.VARINT 1)
  let msg := Message.set msg 18 (.VARINT 2)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.rep_int32 #[(1 : Int32), 2] "packed field should accept unpacked encoding"

def testMapRoundtrip : IO Unit := do
  let map := Std.HashMap.ofList [("a", (1 : Int32)), ("b", (2 : Int32))]
  let base : _root_.test.proto3.All := default
  let val : _root_.test.proto3.All := { base with map_str_int32 := map }
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq (decoded.map_str_int32.get? "a") (some (1 : Int32)) "map value mismatch for key a"
  assertEq (decoded.map_str_int32.get? "b") (some (2 : Int32)) "map value mismatch for key b"

def testUnknownEnum : IO Unit := do
  let msg := Message.set Message.empty 15 (.VARINT 9)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  match decoded.color with
  | _root_.test.proto3.Color.«Unknown.Value» raw =>
      assertEq raw (9 : Int32) "unknown enum raw value mismatch"
  | _ => throw (IO.userError "unknown enum value should be preserved")

def testUnknownFields : IO Unit := do
  let msg := Message.set Message.empty 99 (.VARINT 123)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  match decoded.«Unknown.Fields».get? 99 with
  | some vals => assert (vals.size == 1) "unknown field should be preserved"
  | none => throw (IO.userError "unknown field missing")
  let roundtrip ← ofExcept (_root_.test.proto3.All.toMessage decoded)
  assert ((Message.getRecordsOf roundtrip 99).size == 1) "unknown field should round-trip"

def runTest (name : String) (t : IO Unit) (errs : IO.Ref (Array String)) : IO Unit := do
  try
    t
  catch e =>
    errs.modify (·.push s!"{name}: {e.toString}")

def testProto3 : IO Unit := do
  let errs ← IO.mkRef #[]
  runTest "testDefaults" testDefaults errs
  runTest "testOptionalPresence" testOptionalPresence errs
  runTest "testSubPresence" testSubPresence errs
  runTest "testOneof" testOneof errs
  runTest "testPackedAndUnpacked" testPackedAndUnpacked errs
  runTest "testPackedAcceptsUnpacked" testPackedAcceptsUnpacked errs
  runTest "testMapRoundtrip" testMapRoundtrip errs
  runTest "testUnknownEnum" testUnknownEnum errs
  runTest "testUnknownFields" testUnknownFields errs
  let failures ← errs.get
  unless failures.isEmpty do
    let msg := String.intercalate "\n" failures.toList
    throw (IO.userError msg)

#eval! testProto3
