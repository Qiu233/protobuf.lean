module

import Protobuf
import Protobuf.Json

open Lean
open Protobuf
open Protobuf.Reflection
open Protobuf.Json
open scoped Protobuf.Notation

#load_proto_file "Test/Fixtures/Schemas/Proto3.proto"
#load_proto_file "Test/Fixtures/Schemas/ClosedEnumProto2.proto"
#load_proto_file "Test/Fixtures/Schemas/RequiredMergeProto2.proto"

private def assert (condition : Bool) (failure : String) : IO Unit := do
  unless condition do
    throw (IO.userError failure)

private def ofExcept [ToString ε] (result : Except ε α) : IO α :=
  IO.ofExcept result

private def ofIOExcept [ToString ε] (result : IO (Except ε α)) : IO α :=
  result >>= ofExcept

private def requiredField
    (descriptor : MessageDescriptor) (number : Int32) :
    IO FieldDescriptor := do
  let some field ← descriptor.findFieldByNumber number
    | throw (IO.userError s!"missing field {number}")
  return field

private def parsedUint64
    (descriptor : MessageDescriptor) (field : FieldDescriptor)
    (text : String) : IO UInt64 := do
  let parsed ← ofIOExcept (dynamicOfJsonString descriptor text)
  let values ← ofIOExcept (parsed.presentValues field)
  match values with
  | #[.uint64 value] => return value
  | _ => throw (IO.userError s!"uint64 value was not parsed from `{text}`")

private def expectJsonFailure
    (descriptor : MessageDescriptor) (text failure : String) : IO Unit := do
  match ← dynamicOfJsonString descriptor text with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError failure)

private def testRegularRoundtrip : IO Unit := do
  let descriptor := messageDescriptor test.proto3.All
  let int32Field ← requiredField descriptor 1
  let uint64Field ← requiredField descriptor 8
  let repeatedField ← requiredField descriptor 18
  let mapField ← requiredField descriptor 21

  let mut dynamicMessage : DynamicMessage := { descriptor }
  dynamicMessage ← ofIOExcept
    (dynamicMessage.setSingular int32Field (.int32 (-17)))
  dynamicMessage ← ofIOExcept
    (dynamicMessage.setSingular uint64Field (.uint64 18446744073709551615))
  dynamicMessage ← ofIOExcept
    (dynamicMessage.setValues repeatedField #[.int32 1, .int32 2])

  let some entryDescriptor ← mapField.messageType
    | throw (IO.userError "map entry descriptor is absent")
  let keyField ← requiredField entryDescriptor 1
  let valueField ← requiredField entryDescriptor 2
  let mut entry : DynamicMessage := { descriptor := entryDescriptor }
  entry ← ofIOExcept (entry.setSingular keyField (.string "answer"))
  entry ← ofIOExcept (entry.setSingular valueField (.int32 42))
  dynamicMessage ← ofIOExcept
    (dynamicMessage.setValues mapField #[.message entryDescriptor entry.wire])

  let json ← ofIOExcept (dynamicToJson dynamicMessage)
  let .obj object := json
    | throw (IO.userError "message did not encode as an object")
  assert
    (object.get? "int32Field" ==
      some (.num (JsonNumber.fromInt (-17))))
    "int32 field JSON mapping is wrong"
  assert (object.get? "uint64Field" == some (.str "18446744073709551615"))
    "uint64 field was not emitted as a decimal string"
  assert (object.get? "repInt32" == some (.arr #[1, 2]))
    "repeated field JSON mapping is wrong"
  let some (.obj mapObject) := object.get? "mapStrInt32"
    | throw (IO.userError "map field did not encode as an object")
  assert (mapObject.get? "answer" == some 42)
    "map entry JSON mapping is wrong"

  let decoded ← ofIOExcept (dynamicOfJson descriptor json)
  let int32Values ← ofIOExcept (decoded.presentValues int32Field)
  let uint64Values ← ofIOExcept (decoded.presentValues uint64Field)
  match int32Values with
  | #[.int32 value] =>
      assert (value == (-17)) "int32 field did not round trip"
  | _ => throw (IO.userError "int32 field did not round trip")
  match uint64Values with
  | #[.uint64 value] =>
      assert (value == 18446744073709551615)
        "uint64 field did not round trip"
  | _ => throw (IO.userError "uint64 field did not round trip")

private def testExtensionAndClosedEnum : IO Unit := do
  let descriptor := messageDescriptor test.closed.proto2.ClosedMessage
  let some extension ←
      generatedPool.findExtensionByName "test.closed.proto2.singular_ext"
    | throw (IO.userError "extension descriptor is absent")
  let some enumDescriptor ←
      generatedPool.findEnumByName "test.closed.proto2.ClosedEnum"
    | throw (IO.userError "enum descriptor is absent")
  let dynamicMessage : DynamicMessage := { descriptor }
  let dynamicMessage ← ofIOExcept
    (dynamicMessage.setSingular extension (.enum enumDescriptor 1))
  let options := PrintOptions.withGeneratedPool
  let .obj object ← ofIOExcept (dynamicToJson dynamicMessage options)
    | throw (IO.userError "extension host did not encode as an object")
  assert
    (object.get? "[test.closed.proto2.singular_ext]" ==
      some (.str "CLOSED_ENUM_ONE"))
    "extension was not emitted with its fully-qualified bracketed name"

  let parsed ← ofIOExcept <|
    dynamicOfJson descriptor (.obj object) ParseOptions.withGeneratedPool
  let values ← ofIOExcept (parsed.presentValues extension)
  assert (values.size == 1)
    "extension did not parse through the generated resolver"

  match ← dynamicOfJson descriptor
      (Lean.Json.mkObj [("singular", 123)]) with
  | .error (.invalidValue _ _) => pure ()
  | _ => throw (IO.userError "unknown closed enum number was accepted")

private def testPresenceAndRequired : IO Unit := do
  let descriptor := messageDescriptor test.proto3.All
  let .obj defaults ← ofIOExcept <|
      dynamicToJson ({ descriptor } : DynamicMessage)
        { emitFieldsWithoutPresence := true }
    | throw (IO.userError "default-emitting JSON was not an object")
  assert (defaults.get? "int32Field" == some 0)
    "absent implicit scalar was not emitted with its default"
  assert (defaults.get? "repInt32" == some (.arr #[]))
    "empty repeated field was not emitted"
  assert (defaults.get? "mapStrInt32" == some (.obj {}))
    "empty map field was not emitted"

  let requiredDescriptor :=
    messageDescriptor test.required_merge.proto2.Child
  match ← dynamicOfJson requiredDescriptor (.obj {}) with
  | .error (.missingRequiredField _ _) => pure ()
  | _ => throw (IO.userError "missing required field was accepted")
  let _ ← ofIOExcept <|
    dynamicOfJson requiredDescriptor (.obj {}) { allowPartial := true }
  match ← dynamicToJson ({ descriptor := requiredDescriptor } : DynamicMessage) with
  | .error (.missingRequiredField _ _) => pure ()
  | _ => throw (IO.userError "uninitialized message was serialized")

private def testIntegralNumericStrings : IO Unit := do
  let descriptor := messageDescriptor test.proto3.All
  let uint64Field ← requiredField descriptor 8
  let cases := #[
    ("{\"uint64Field\":1e3}", 1000),
    ("{\"uint64Field\":\"1e3\"}", 1000),
    ("{\"uint64Field\":\"1000e-3\"}", 1),
    ("{\"uint64Field\":\"1.20e1\"}", 12),
    ("{\"uint64Field\":\"184467440737095516150e-1\"}",
      18446744073709551615),
    ("{\"uint64Field\":\"0e536870000\"}", 0)
  ]
  for (text, expected) in cases do
    let actual ← parsedUint64 descriptor uint64Field text
    assert (actual == expected)
      s!"expected {expected}, got {actual} from `{text}`"
  for text in #[
      "{\"uint64Field\":\"1e536870000\"}",
      "{\"uint64Field\":\"1e-536870000\"}",
      "{\"uint64Field\":\"1e-1\"}",
      "{\"uint64Field\":\"18446744073709551616\"}",
      "{\"uint64Field\":\"01\"}",
      "{\"uint64Field\":\"+1\"}",
      "{\"uint64Field\":1e536870000}",
      "{\"floatField\":\"1e536870000\"}"
    ] do
    expectJsonFailure descriptor text
      s!"invalid uint64 numeric string was accepted: `{text}`"

public def main : IO Unit := do
  testRegularRoundtrip
  testExtensionAndClosedEnum
  testPresenceAndRequired
  testIntegralNumericStrings
