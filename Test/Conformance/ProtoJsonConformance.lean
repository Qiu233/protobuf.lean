module

import Protobuf
import Protobuf.Json

open Protobuf
open Protobuf.Reflection
open Protobuf.Json
open scoped Protobuf.Notation

#load_proto_descriptors "Test/Fixtures/Conformance/ProtoJsonConformance.proto"
#load_proto_descriptors "Test/Fixtures/Official/google/protobuf/test_messages_proto3.proto" in "Test/Fixtures/Official"
-- The upstream testee links Empty separately from test_messages_proto3.proto.
#load_proto_descriptors "Test/Fixtures/Conformance/ProtoJsonConformanceEmpty.proto"

private def ofReflection
    (result : IO (Except ReflectionError α)) : IO (Except String α) := do
  return (← result).mapError toString

private def requiredField
    (descriptor : MessageDescriptor) (number : Int32) :
    IO (Except String FieldDescriptor) := do
  let some field ← descriptor.findFieldByNumber number
    | return .error s!"missing field {number} in `{descriptor.fullName}`"
  return .ok field

private def lastValue
    (value : DynamicMessage) (number : Int32) :
    IO (Except String (Option Value)) := do
  let .ok field ← requiredField value.descriptor number
    | return .error s!"missing request field {number}"
  return (← ofReflection (value.presentValues field)).map (·.back?)

private def requestString
    (request : DynamicMessage) (number : Int32) :
    IO (Except String String) := do
  let .ok value? ← lastValue request number
    | return .error s!"cannot read request field {number}"
  match value? with
  | none => return .ok ""
  | some (.string value) =>
      let some text := value.toString?
        | return .error s!"request field {number} is not UTF-8"
      return .ok text
  | _ => return .error s!"request field {number} is not a string"

private def requestEnumNumber
    (request : DynamicMessage) (number : Int32) :
    IO (Except String Int32) := do
  let .ok value? ← lastValue request number
    | return .error s!"cannot read request field {number}"
  match value? with
  | none => return .ok 0
  | some (.enum _ value) => return .ok value
  | _ => return .error s!"request field {number} is not an enum"

private def response
    (number : Int32) (value : Value) : IO (Except String ByteArray) := do
  let some descriptor ←
      generatedPool.findMessageByName "conformance.ConformanceResponse"
    | return .error "ConformanceResponse descriptor is not registered"
  let .ok field ← requiredField descriptor number
    | return .error s!"missing response field {number}"
  let initial : DynamicMessage := { descriptor }
  let .ok result ← ofReflection (initial.setSingular field value)
    | return .error s!"cannot set response field {number}"
  return (DynamicMessage.encode result).mapError toString

private def textResponse (number : Int32) (detail : String) :
    IO (Except String ByteArray) :=
  response number (.string detail)

private def processTestRequest
    (request : DynamicMessage) : IO (Except String ByteArray) := do
  let .ok typeName ← requestString request 4
    | return ← textResponse 2 "invalid message_type"
  if typeName == "conformance.FailureSet" then
    return ← response 3 (.bytes .empty)
  unless typeName ==
      "protobuf_test_messages.proto3.TestAllTypesProto3" do
    return ← textResponse 5 s!"unsupported message type `{typeName}`"
  let some target ← generatedPool.findMessageByName typeName
    | return ← textResponse 2 s!"message type `{typeName}` is not registered"
  let .ok category ← requestEnumNumber request 5
    | return ← textResponse 2 "invalid test_category"
  if category == 4 || category == 5 then
    return ← textResponse 5 "JSPB and TextFormat are not implemented"
  let input? ← lastValue request 1
  let parsed : Except String DynamicMessage ←
    match input? with
    | .error detail => pure (.error detail)
    | .ok (some (.bytes bytes)) =>
        match DynamicMessage.decode target bytes with
        | .error error => pure (.error (toString error))
        | .ok value =>
            match ← value.validateKnownFields with
            | .error error => pure (.error (toString error))
            | .ok () => pure (.ok value)
    | .ok _ =>
        match ← lastValue request 2 with
        | .error detail => pure (.error detail)
        | .ok (some (.string raw)) =>
            let some text := raw.toString?
              | pure (.error "JSON payload is not UTF-8")
            let options : ParseOptions :=
              { ParseOptions.withGeneratedPool with
                discardUnknownFields := category == 3 }
            pure <| (← dynamicOfJsonString target text options).mapError toString
        | .ok _ => pure (.error "unsupported or absent input payload")
  let .error detail := parsed
    | let .ok outputFormat ← requestEnumNumber request 3
        | return ← textResponse 2 "invalid requested_output_format"
      let .ok value := parsed
        | return ← textResponse 2 "internal parse state error"
      match outputFormat with
      | 1 =>
          match DynamicMessage.encode value with
          | .ok bytes => response 3 (.bytes bytes)
          | .error error => textResponse 6 (toString error)
      | 2 =>
          match ← dynamicToJsonString value PrintOptions.withGeneratedPool with
          | .ok text => response 4 (.string text)
          | .error error => textResponse 6 (toString error)
      | _ => textResponse 5 s!"unsupported output format {outputFormat}"
  textResponse 1 detail

private def processFrame (bytes : ByteArray) : IO ByteArray := do
  let some descriptor ←
      generatedPool.findMessageByName "conformance.ConformanceRequest"
    | throw (IO.userError "ConformanceRequest descriptor is not registered")
  match DynamicMessage.decode descriptor bytes with
  | .error error =>
      IO.ofExcept (← textResponse 2 s!"invalid ConformanceRequest: {error}")
  | .ok request =>
      IO.ofExcept (← processTestRequest request)

private partial def readExactly
    (input : IO.FS.Stream) (count : Nat) (acc : ByteArray := .empty) :
    IO (Option ByteArray) := do
  if acc.size == count then
    return some acc
  let chunk ← input.read (USize.ofNat (count - acc.size))
  if chunk.isEmpty then
    if acc.isEmpty then return none
    else throw (IO.userError "truncated conformance frame")
  readExactly input count (acc ++ chunk)

private def littleEndianLength (header : ByteArray) : Nat :=
  header[0]!.toNat +
    (header[1]!.toNat <<< 8) +
    (header[2]!.toNat <<< 16) +
    (header[3]!.toNat <<< 24)

private def lengthHeader (length : Nat) : ByteArray :=
  .mk #[
    UInt8.ofNat length,
    UInt8.ofNat (length >>> 8),
    UInt8.ofNat (length >>> 16),
    UInt8.ofNat (length >>> 24)
  ]

private partial def runLoop
    (input output : IO.FS.Stream) : IO Unit := do
  let some header ← readExactly input 4 | return
  let length := littleEndianLength header
  if length > 0x7fffffff then
    throw (IO.userError "oversized conformance frame")
  let some request ← readExactly input length
    | throw (IO.userError "truncated conformance request")
  let result ← processFrame request
  output.write (lengthHeader result.size)
  output.write result
  output.flush
  runLoop input output

public def main : IO Unit := do
  runLoop (← IO.getStdin) (← IO.getStdout)
