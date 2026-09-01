module

import Protobuf.Json

open Protobuf.Json Protobuf.Reflection

/--
The descriptor pool is populated by `initialize` blocks below `Protobuf.Json`,
so a round trip through it fails unless the whole import is linked into the
client, not merely elaborated.
-/
public def main : IO Unit := do
  let some descriptor ←
    generatedPool.findMessageByName "google.protobuf.FieldDescriptorProto"
    | throw (IO.userError "descriptor.proto is missing from the generated pool")
  match ← dynamicOfJsonString descriptor "{\"name\":\"payload\",\"number\":3}" with
  | .error err => throw (IO.userError (toString err))
  | .ok message =>
    match ← dynamicToJsonString message with
    | .error err => throw (IO.userError (toString err))
    | .ok rendered => IO.println rendered
