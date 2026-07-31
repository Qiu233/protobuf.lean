module

import Protobuf

open Lean
open Protobuf Encoding Notation
open scoped Protobuf.Notation

run_meta do
  unless
      Protobuf.Versions.leanGeneratedTypeMemberNames ==
        Protobuf.Notation.leanGeneratedMemberNames do
    throwError
      "descriptor and direct-notation collision lists have diverged"
  let syntheticName :=
    mkIdent
      ((Name.mkStr1 "ParserCollision").str
        "choice_Type.protobuf.oneof")
  let safeAlternative := mkIdent (Name.mkStr1 "rec.protobuf")
  let command ← `(command| oneof $syntheticName:ident {
    int32 $safeAlternative:ident = 1;
  })
  let rendered ←
    match
        Protobuf.Notation.PrettyPrinter.command.pprintSafe command with
    | .ok rendered => pure rendered
    | .error err =>
        throwError
          "collision-proof oneof syntax could not be rendered: {err}"
  unless rendered.contains "choice_Type.protobuf.oneof" &&
      rendered.contains "rec.protobuf" do
    throwError
      "collision-proof name components were lost while rendering: {rendered}"
  match Parser.runParserCategory (← getEnv) `command rendered with
  | .ok _ => pure ()
  | .error err =>
      throwError
        "rendered collision-proof oneof command did not parse again: {err}"

#load_proto_file "Test/Fixtures/Schemas/NamingCollisionsProto3.proto"
#load_proto_file "Test/Fixtures/Schemas/NamingCollisionsProto2.proto"
#load_proto_file "Test/Fixtures/Schemas/NamingCollisionsEditions.proto"

#check naming_collisions.proto3.HelperOwner.builder
#check naming_collisions.proto3.HelperOwner.encode
#check naming_collisions.proto3.HelperOwner.«protobuf.internal».encode
#check naming_collisions.proto3.OneofOwner.choice_Type
#check naming_collisions.proto3.OneofOwner.«choice_Type.protobuf.oneof»
#check naming_collisions.proto3.OneofOwner.«choice_Type.protobuf.oneof».«rec.protobuf»
#check naming_collisions.proto3.AutomaticOwner.«rec.protobuf»
#check naming_collisions.proto3.AutomaticOwner.«mk.protobuf»
#check naming_collisions.proto3.AutomaticOwner.«noConfusion.protobuf»
#check naming_collisions.proto3.AutomaticOwner.«ctorIdx.protobuf»
#check naming_collisions.proto3.AutomaticOwner.«_sizeOf_1.protobuf»
#check naming_collisions.proto3.AutomaticOwner.«_sizeOf_inst.protobuf»
#check naming_collisions.proto3.AutomaticOwner.«casesOn.protobuf»
#check naming_collisions.proto3.AutomaticEnum.«rec.protobuf»
#check naming_collisions.proto3.AutomaticEnum.«casesOn.protobuf»
#check naming_collisions.proto3.OneofProjectionOwner.«rec.protobuf»
#check naming_collisions.proto3.OneofProjectionOwner.«rec.protobuf_Type»
#check naming_collisions.proto3.OneofProjectionOwner.encode
#check naming_collisions.proto3.OneofProjectionOwner.encode_Type

private def proto3Sample : naming_collisions.proto3.HelperOwner := {
  builder_value := some { value := 11 }
  encode_value := some { value := 12 }
  decode_value := some { value := 13 }
  to_message_value := some { value := 14 }
  from_message_value := some { value := 15 }
  merge_value := some { value := 16 }
  decoder_value := some { value := 17 }
}

/-- info: true -/
#guard_msgs (info) in
#eval
  match
      Protobuf.encode proto3Sample with
  | .error _ => false
  | .ok wire =>
      match
          Protobuf.decodeThe naming_collisions.proto3.HelperOwner wire with
      | .error _ => false
      | .ok decoded =>
          decoded.builder_value.any fun
              (value : naming_collisions.proto3.HelperOwner.builder) =>
            value.value == 11 &&
              decoded.encode_value.any fun
                  (value : naming_collisions.proto3.HelperOwner.encode) =>
                value.value == 12 &&
                  decoded.decoder_value.any fun
                      (value :
                        naming_collisions.proto3.HelperOwner.decoder_rep) =>
                    value.value == 17

private def proto3Oneof :
    naming_collisions.proto3.OneofOwner := {
  choice := some
    (.«rec.protobuf» 23)
  nested_value := some { marker := 24 }
}

/-- info: true -/
#guard_msgs (info) in
#eval
  match
      Protobuf.encode proto3Oneof with
  | .error _ => false
  | .ok wire =>
      match
          Protobuf.decodeThe naming_collisions.proto3.OneofOwner wire with
      | .error _ => false
      | .ok decoded =>
          match decoded.choice with
          | some
              (.«rec.protobuf» value) =>
              value == 23 &&
                decoded.nested_value.any fun
                    (nested :
                      naming_collisions.proto3.OneofOwner.choice_Type) =>
                  nested.marker == 24
          | _ => false

private def proto3OneofProjection :
  naming_collisions.proto3.OneofProjectionOwner := {
  «rec.protobuf» := some (.value 25)
  encode := some (.text "projection")
}

/-- info: true -/
#guard_msgs (info) in
#eval
  match Protobuf.encode proto3OneofProjection with
  | .error _ => false
  | .ok wire =>
      match
          Protobuf.decodeThe
            naming_collisions.proto3.OneofProjectionOwner wire with
      | .error _ => false
      | .ok decoded =>
          (match decoded.«rec.protobuf» with
          | some (.value value) => value == 25
          | _ => false) &&
          (match decoded.encode with
          | some (.text value) => value == "projection"
          | _ => false)

#check naming_collisions.proto2.ExplicitDefaults.get_foo
#check naming_collisions.proto2.ExplicitDefaults.has_foo
#check naming_collisions.proto2.ExplicitDefaults.«protobuf.internal».encode
#check naming_collisions.proto2.ExplicitDefaults.«Explicit.Default.Accessors».foo.get
#check naming_collisions.proto2.OneofOwner.«selected_Type.protobuf.oneof»
#check naming_collisions.proto2.AutomaticEnum.«ctorElim.protobuf»
#check naming_collisions.proto2.OneofProjectionOwner.«rec.protobuf»
#check naming_collisions.proto2.OneofProjectionOwner.«rec.protobuf_Type»
#check naming_collisions.proto2.OneofProjectionOwner.encode
#check naming_collisions.proto2.OneofProjectionOwner.encode_Type

/-- info: true -/
#guard_msgs (info) in
#eval
  let value : naming_collisions.proto2.ExplicitDefaults := {}
  naming_collisions.proto2.ExplicitDefaults.«Explicit.Default.Accessors».foo.get
      value == 7 &&
    !naming_collisions.proto2.ExplicitDefaults.«Explicit.Default.Accessors».foo.has
      value &&
    match
        naming_collisions.proto2.ExplicitDefaults.«protobuf.internal».encode
          value with
    | .error _ => false
    | .ok wire =>
        match
            naming_collisions.proto2.ExplicitDefaults.«protobuf.internal».decode
              wire with
        | .ok decoded =>
            naming_collisions.proto2.ExplicitDefaults.«Explicit.Default.Accessors».foo.get
                decoded == 7
        | .error _ => false

#check naming_collisions.editions.HelperOwner.builder
#check naming_collisions.editions.HelperOwner.encode
#check naming_collisions.editions.HelperOwner.«protobuf.internal».encode
#check naming_collisions.editions.AutomaticOwner.«rec.protobuf»
#check naming_collisions.editions.AutomaticOwner.«mk.protobuf»
#check naming_collisions.editions.OneofOwner.«choice_Type.protobuf.oneof»
#check naming_collisions.editions.OneofProjectionOwner.«rec.protobuf»
#check naming_collisions.editions.OneofProjectionOwner.«rec.protobuf_Type»
#check naming_collisions.editions.OneofProjectionOwner.encode
#check naming_collisions.editions.OneofProjectionOwner.encode_Type

/-- info: true -/
#guard_msgs (info) in
#eval
  let value : naming_collisions.editions.AutomaticOwner := {
    «mk.protobuf» := some 31
    nested_rec := some { «mk.protobuf» := some 32 }
  }
  match
      naming_collisions.editions.AutomaticOwner.«protobuf.internal».encode
        value with
  | .error _ => false
  | .ok wire =>
      match
          naming_collisions.editions.AutomaticOwner.«protobuf.internal».decode
            wire with
      | .ok decoded =>
          decoded.«mk.protobuf» == some 31 &&
            decoded.nested_rec.bind (·.«mk.protobuf») == some 32
      | .error _ => false

enum DirectAutomaticEnum {
  rec = 0;
  casesOn = 1;
  ctorElim = 2;
}

oneof DirectAutomaticOneof {
  int32 rec = 1;
  string casesOn = 2;
}

message DirectAutomaticMessage {
  int32 mk = 3;
  int32 recOn = 4;
  int32 noConfusion = 5;
  int32 ctorIdx = 6;
  int32 _sizeOf_1 = 7;
  int32 _sizeOf_inst = 8;
  DirectAutomaticOneof selected = 0;
}

enum DirectFormerHelperEnum {
  toInt32 = 0;
  fromInt32 = 1;
  builder = 2;
}

oneof DirectFormerHelperOneof {
  int32 toMessage = 1;
  int32 merge = 2;
  int32 fromMessage = 3;
}

message DirectFormerHelperMessage {
  int32 encode = 1;
  int32 decode = 2;
  int32 toMessage = 3;
  int32 fromMessage = 4;
  int32 merge = 5;
  DirectFormerHelperEnum enum_value = 6;
}

#check DirectAutomaticEnum.«rec.protobuf»
#check DirectAutomaticEnum.«casesOn.protobuf»
#check DirectAutomaticOneof.«rec.protobuf»
#check DirectAutomaticMessage.«mk.protobuf»
#check DirectAutomaticMessage.«recOn.protobuf»
#check DirectAutomaticMessage.«noConfusion.protobuf»
#check DirectAutomaticMessage.«ctorIdx.protobuf»
#check DirectAutomaticMessage.«_sizeOf_1.protobuf»
#check DirectAutomaticMessage.«_sizeOf_inst.protobuf»
#check DirectFormerHelperEnum.toInt32
#check DirectFormerHelperEnum.fromInt32
#check DirectFormerHelperEnum.builder
#check DirectFormerHelperOneof.toMessage
#check DirectFormerHelperOneof.merge
#check DirectFormerHelperOneof.fromMessage
#check DirectFormerHelperMessage.encode
#check DirectFormerHelperMessage.decode
#check DirectFormerHelperMessage.toMessage
#check DirectFormerHelperMessage.fromMessage
#check DirectFormerHelperMessage.merge

/-- info: true -/
#guard_msgs (info) in
#eval
  let value : DirectFormerHelperMessage := {
    encode := 71
    decode := 72
    toMessage := 73
    fromMessage := 74
    merge := 75
    enum_value := .builder
  }
  match Protobuf.encode value with
  | .error _ => false
  | .ok wire =>
      match Protobuf.decodeThe DirectFormerHelperMessage wire with
      | .error _ => false
      | .ok decoded =>
          decoded.encode == 71 &&
            decoded.decode == 72 &&
            decoded.toMessage == 73 &&
            decoded.fromMessage == 74 &&
            decoded.merge == 75 &&
            decoded.enum_value == DirectFormerHelperEnum.builder

proto_mutual {
  message DirectQualifiedOwner {
    DirectQualifiedOwner.builder nested = 1;
    DirectQualifiedOwner.rec auto_nested = 2;
  }
  message DirectQualifiedOwner.builder {
    int32 value = 1;
  }
  message DirectQualifiedOwner.rec {
    int32 value = 1;
  }
}

#check DirectQualifiedOwner.builder
#check DirectQualifiedOwner.«rec.protobuf»
#check DirectQualifiedOwner.«protobuf.internal».builder
#check DirectQualifiedOwner.«protobuf.internal».encode

message DirectSingleOneofChild {
  int32 value = 1;
}

oneof DirectSingleMessageOneof {
  DirectSingleOneofChild child = 1;
}

#check DirectSingleMessageOneof.«protobuf.internal».merge

/-- info: true -/
#guard_msgs (info) in
#eval
  let old : DirectSingleMessageOneof := .child { value := 61 }
  let new : DirectSingleMessageOneof := .child { value := 62 }
  match DirectSingleMessageOneof.«protobuf.internal».merge old new with
  | .child value => value.value == 62

/-- info: true -/
#guard_msgs (info) in
#eval
  let value : DirectQualifiedOwner := {
    nested := some { value := 51 }
    auto_nested := some { value := 52 }
  }
  match DirectQualifiedOwner.«protobuf.internal».encode value with
  | .error _ => false
  | .ok wire =>
      match DirectQualifiedOwner.«protobuf.internal».decode wire with
      | .error _ => false
      | .ok decoded =>
          decoded.nested.any fun
              (nested : DirectQualifiedOwner.builder) =>
            nested.value == 51 &&
              decoded.auto_nested.any fun
                  (nested : DirectQualifiedOwner.«rec.protobuf») =>
                nested.value == 52

/-- info: true -/
#guard_msgs (info) in
#eval
  let value : DirectAutomaticMessage := {
    «mk.protobuf» := 41
    «recOn.protobuf» := 42
    «noConfusion.protobuf» := 44
    «ctorIdx.protobuf» := 45
    «_sizeOf_1.protobuf» := 46
    «_sizeOf_inst.protobuf» := 47
    selected := some (.«rec.protobuf» 43)
  }
  match Protobuf.encode value with
  | .error _ => false
  | .ok wire =>
      match Protobuf.decodeThe DirectAutomaticMessage wire with
      | .error _ => false
      | .ok decoded =>
          decoded.«mk.protobuf» == 41 &&
            decoded.«recOn.protobuf» == 42 &&
            decoded.«noConfusion.protobuf» == 44 &&
            decoded.«ctorIdx.protobuf» == 45 &&
            decoded.«_sizeOf_1.protobuf» == 46 &&
            decoded.«_sizeOf_inst.protobuf» == 47 &&
            match decoded.selected with
            | some (.«rec.protobuf» selected) => selected == 43
            | _ => false
