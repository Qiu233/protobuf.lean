module

import Protobuf

open Protobuf Encoding Notation

#load_proto_file "Test/Fixtures/Schemas/GroupProto2.proto"
#load_proto_file "Test/Fixtures/Schemas/GroupEditions.proto"

#check group_support.proto2.LegacyGroups
#check group_support.proto2.LegacyGroups.OptionalGroup
#check group_support.editions.DelimitedFields
#check group_support.editions.DelimitedFields.choice_Type.grouped_choice
#check group_support.proto2.ExtensionGroup

private def bytes (values : Array UInt8) : ByteArray := ⟨values⟩

private def proto2Required (value : Int32) :
    group_support.proto2.LegacyGroups.RequiredGroup := {
  value := some value
}

private def proto2Sample : group_support.proto2.LegacyGroups := {
  optionalgroup := some {
    a := some 3
    b := some (Protobuf.UnvalidatedString.ofString "q")
  }
  repeatedgroup := #[
    { value := some 4 },
    { value := some 5 }
  ]
  requiredgroup := some (proto2Required 9)
}

private def proto2Expected : ByteArray := bytes #[
  0x2b, 0x08, 0x03, 0x12, 0x01, 0x71, 0x2c,
  0x33, 0x08, 0x04, 0x34,
  0x33, 0x08, 0x05, 0x34,
  0x3b, 0x08, 0x09, 0x3c
]

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.encode proto2Sample with
  | .ok wire => wire == proto2Expected
  | .error _ => false

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.proto2.LegacyGroups proto2Expected with
  | .ok value =>
      match value.optionalgroup, value.requiredgroup with
      | some optionalGroup, some requiredGroup =>
          optionalGroup.a == some 3 &&
          optionalGroup.b.bind (·.toString?) == some "q" &&
          value.repeatedgroup.map
            (fun (group :
              group_support.proto2.LegacyGroups.RepeatedGroup) =>
                group.value) == #[some 4, some 5] &&
          requiredGroup.value == some 9
      | _, _ => false
  | .error _ => false

private def proto2MergeWire : ByteArray := bytes #[
  0x2b, 0x08, 0x01, 0x2c,
  0x2b, 0x12, 0x01, 0x78, 0x2c,
  0x3b, 0x08, 0x09, 0x3c
]

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.proto2.LegacyGroups proto2MergeWire with
  | .ok value =>
      match value.optionalgroup with
      | some group =>
          group.a == some 1 &&
          group.b.bind (·.toString?) == some "x"
      | none => false
  | .error _ => false

private def proto2RequiredMergeWire : ByteArray := bytes #[
  0x0b, 0x08, 0x01, 0x0c,
  0x0b, 0x10, 0x02, 0x0c
]

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.proto2.RequiredGroupMerge
      proto2RequiredMergeWire with
  | .ok value =>
      match value.value with
      | some group =>
          group.a == some 1 && group.b == some 2
      | none => false
  | .error _ => false

private def recursiveProto2Sample :
    group_support.proto2.RecursiveLegacy := {
  child := some {
    parent := some {}
  }
}

/-- info: true -/
#guard_msgs (info) in
#eval
  let expected := bytes #[0x0b, 0x0a, 0x00, 0x0c]
  match Protobuf.encode recursiveProto2Sample with
  | .error _ => false
  | .ok wire =>
      wire == expected &&
      match Protobuf.decodeThe group_support.proto2.RecursiveLegacy wire with
      | .ok value =>
          match value.child with
          | some child => child.parent.isSome
          | none => false
      | .error _ => false

private def proto2WrongWire : ByteArray := bytes #[
  0x2a, 0x02, 0x08, 0x01,
  0x3b, 0x08, 0x09, 0x3c
]

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.proto2.LegacyGroups proto2WrongWire with
  | .ok value =>
      value.optionalgroup.isNone &&
      (match value.«Unknown.Fields»[5]? with
      | some (values : Array ProtoVal) =>
          match values[0]? with
          | some (ProtoVal.LEN data) =>
              values.size == 1 && data == bytes #[0x08, 0x01]
          | _ => false
      | none => false) &&
      (match Protobuf.encode value with
      | .ok wire => wire == bytes #[
          0x3b, 0x08, 0x09, 0x3c,
          0x2a, 0x02, 0x08, 0x01
        ]
      | .error _ => false)
  | .error _ => false

private def editionsSample : group_support.editions.DelimitedFields := {
  singular := some { a := some 3, b := some "q" }
  repeated := #[
    { a := some 4 },
    { a := some 5 }
  ]
  choice := some (.grouped_choice { a := some 6 })
}

private def inheritedEditionsSample :
    group_support.editions.InheritedDelimited := {
  scalar := some 7
  payload := some { a := some 8 }
}

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.encode inheritedEditionsSample with
  | .ok wire =>
      wire == bytes #[0x08, 0x07, 0x13, 0x08, 0x08, 0x14]
  | .error _ => false

private def inheritedMapSample :
    group_support.editions.InheritedMap := {
  items := Std.HashMap.ofList [
    ("k", { a := some 3 })
  ]
}

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.encode inheritedMapSample with
  | .ok wire =>
      -- Map entries and their message values remain length-delimited even
      -- under an inherited file-level DELIMITED feature.
      wire == bytes #[
        0x0a, 0x07,
        0x0a, 0x01, 0x6b,
        0x12, 0x02, 0x08, 0x03
      ]
  | .error _ => false

private def editionsExpected : ByteArray := bytes #[
  0x0b, 0x08, 0x03, 0x12, 0x01, 0x71, 0x0c,
  0x13, 0x08, 0x04, 0x14,
  0x13, 0x08, 0x05, 0x14,
  0x1b, 0x08, 0x06, 0x1c
]

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.encode editionsSample with
  | .ok wire => wire == editionsExpected
  | .error _ => false

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.editions.DelimitedFields editionsExpected with
  | .ok value =>
      (match value.singular with
      | some payload =>
          payload.a == some 3 && payload.b == some "q"
      | none => false) &&
      value.repeated.map
        (fun (payload : group_support.editions.Payload) =>
          payload.a) == #[some 4, some 5] &&
      (match value.choice with
      | some (.grouped_choice payload) =>
          payload.a == some 6 && payload.b.isNone
      | _ => false)
  | .error _ => false

private def editionsOneofMergeWire : ByteArray := bytes #[
  0x1b, 0x08, 0x01, 0x1c,
  0x1b, 0x12, 0x01, 0x78, 0x1c
]

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.editions.DelimitedFields editionsOneofMergeWire with
  | .ok value =>
      match value.choice with
      | some (.grouped_choice payload) =>
          payload.a == some 1 && payload.b == some "x"
      | _ => false
  | .error _ => false

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.editions.DelimitedFields
      (bytes #[0x1b, 0x08, 0x01, 0x1c, 0x20, 0x09]) with
  | .ok value =>
      match value.choice with
      | some (.scalar_choice 9) => true
      | _ => false
  | .error _ => false

private def proto2ExtensionRoundtrip : Bool :=
  let host : group_support.proto2.ExtensionHost := {}
  match host.set_extensiongroup { value := some 17 } with
  | .error _ => false
  | .ok host =>
      match Protobuf.encode host with
      | .error _ => false
      | .ok wire =>
          wire == bytes #[0xa3, 0x06, 0x08, 0x11, 0xa4, 0x06] &&
          match Protobuf.decodeThe group_support.proto2.ExtensionHost wire with
          | .error _ => false
          | .ok decoded =>
              match decoded.get_extensiongroup? with
              | .ok (some group) => group.value == some 17
              | _ => false

/-- info: true -/
#guard_msgs (info) in
#eval proto2ExtensionRoundtrip

private def editionsExtensionRoundtrip : Bool :=
  let host : group_support.editions.ExtensionHost := {}
  match host.set_delimited_extension { a := some 18 } with
  | .error _ => false
  | .ok host =>
      match Protobuf.encode host with
      | .error _ => false
      | .ok wire =>
          wire == bytes #[0xa3, 0x06, 0x08, 0x12, 0xa4, 0x06] &&
          match Protobuf.decodeThe group_support.editions.ExtensionHost wire with
          | .error _ => false
          | .ok decoded =>
              match decoded.get_delimited_extension? with
              | .ok (some payload) =>
                  payload.a == some 18 && payload.b.isNone
              | _ => false

/-- info: true -/
#guard_msgs (info) in
#eval editionsExtensionRoundtrip

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.editions.DelimitedFields
      (bytes #[0x20, 0x09, 0x1b, 0x08, 0x01, 0x1c]) with
  | .ok value =>
      match value.choice with
      | some (.grouped_choice payload) =>
          payload.a == some 1 && payload.b.isNone
      | _ => false
  | .error _ => false

private def groupChain (depth : Nat) : ByteArray :=
  (List.range depth).foldl (fun payload _ =>
    bytes #[0x0b] ++ payload ++ bytes #[0x0c])
    (bytes #[0x10, 0x01])

private partial def varint (value : Nat) : ByteArray :=
  let byte := UInt8.ofNat (value &&& 0x7f)
  let rest := value >>> 7
  if rest == 0 then
    bytes #[byte]
  else
    bytes #[byte ||| 0x80] ++ varint rest

private def mixedChain (depth : Nat) : ByteArray :=
  (List.range depth).foldl (fun payload i =>
    if i % 2 == 0 then
      bytes #[0x0b] ++ payload ++ bytes #[0x0c]
    else
      bytes #[0x12] ++ varint payload.size ++ payload)
    ByteArray.empty

/-- info: true -/
#guard_msgs (info) in
#eval
  (Protobuf.decodeThe group_support.editions.RecursiveNode (groupChain 100)).isOk

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.editions.RecursiveNode (groupChain 101) with
  | .error _ => true
  | .ok _ => false

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.editions.MixedNode (mixedChain 100) with
  | .ok _ => true
  | .error _ => false

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.editions.MixedNode (mixedChain 101) with
  | .error _ => true
  | .ok _ => false

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.decodeThe group_support.editions.DelimitedFields
      (bytes #[0x0a, 0x02, 0x08, 0x01]) with
  | .ok value =>
      value.singular.isNone &&
      match value.«Unknown.Fields»[1]? with
      | some (values : Array ProtoVal) =>
          match values[0]? with
          | some (ProtoVal.LEN data) =>
              values.size == 1 && data == bytes #[0x08, 0x01]
          | _ => false
      | none => false
  | .error _ => false
