module

import Protobuf

open Protobuf Encoding Notation

#load_proto_file "Test/official/google/protobuf/struct.proto" in "Test/official"

#check google.protobuf.Struct
#check google.protobuf.Value
#check google.protobuf.ListValue
#check google.protobuf.Value.kind_Type.string_value
#check google.protobuf.Value.kind_Type.struct_value
#check google.protobuf.Value.kind_Type.list_value
#check google.protobuf.Struct.fields

private def isLeaf (value : google.protobuf.Value) : Bool :=
  match value.kind with
  | some (.string_value text) => text == "leaf"
  | _ => false

private def hasRecursivePayload (value : google.protobuf.Value) : Bool :=
  match value.kind with
  | some (.struct_value object) =>
      match object.fields.get? "leaf" with
      | some leaf => isLeaf leaf
      | none => false
  | _ => false

private def hasListPayload (value : google.protobuf.Value) : Bool :=
  match value.kind with
  | some (.list_value list) =>
      list.values.size == 1 && isLeaf list.values[0]!
  | _ => false

private def officialStructRoundtrip : Bool :=
  let leaf : google.protobuf.Value := {
    kind := some (.string_value "leaf")
  }
  let child : google.protobuf.Struct := {
    fields := Std.HashMap.Raw.ofList [("leaf", leaf)]
  }
  let list : google.protobuf.ListValue := {
    values := #[leaf]
  }
  let root : google.protobuf.Struct := {
    fields := Std.HashMap.Raw.ofList [
      ("object", { kind := some (.struct_value child) }),
      ("list", { kind := some (.list_value list) })
    ]
  }
  match root.encode with
  | .error _ => false
  | .ok bytes =>
      match google.protobuf.Struct.decode bytes with
      | .error _ => false
      | .ok decoded =>
          match decoded.fields.get? "object", decoded.fields.get? "list" with
          | some object, some list => hasRecursivePayload object && hasListPayload list
          | _, _ => false

/-- info: true -/
#guard_msgs (info) in
#eval officialStructRoundtrip
