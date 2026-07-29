module

public import Protobuf.Internal.Desc.Core
public import Protobuf.Internal.Desc.Features
public import Protobuf.Internal.Desc.Options.Support
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

message MessageOptions {
  optional bool message_set_wire_format = 1 [default = false];

  optional bool no_standard_descriptor_accessor = 2 [default = false];

  optional bool deprecated = 3 [default = false];

  optional bool map_entry = 7;

  optional bool deprecated_legacy_json_field_conflicts = 11 [deprecated = true];

  optional FeatureSet features = 12;

  repeated UninterpretedOption uninterpreted_option = 999;
}

message OneofOptions {
  optional FeatureSet features = 1;

  repeated UninterpretedOption uninterpreted_option = 999;
}

message EnumOptions {
  optional bool allow_alias = 2;

  optional bool deprecated = 3 [default = false];

  optional bool deprecated_legacy_json_field_conflicts = 6 [deprecated = true];

  optional FeatureSet features = 7;

  repeated UninterpretedOption uninterpreted_option = 999;
}

message EnumValueOptions {
  optional bool deprecated = 1 [default = false];

  optional FeatureSet features = 2;

  optional bool debug_redact = 3 [default = false];

  optional FieldOptions.FeatureSupport feature_support = 4;

  repeated UninterpretedOption uninterpreted_option = 999;
}

message ServiceOptions {
  optional FeatureSet features = 34;

  optional bool deprecated = 33 [default = false];

  repeated UninterpretedOption uninterpreted_option = 999;
}

enum MethodOptions.IdempotencyLevel [closed = true] {
  IDEMPOTENCY_UNKNOWN = 0;
  NO_SIDE_EFFECTS = 1; IDEMPOTENT = 2; }

message MethodOptions {
  optional bool deprecated = 33 [default = false];

  optional MethodOptions.IdempotencyLevel idempotency_level = 34
      [default = IDEMPOTENCY_UNKNOWN];

  optional FeatureSet features = 35;

  repeated UninterpretedOption uninterpreted_option = 999;
}

local instance descOptionsDeclarationReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for MessageOptions
deriving instance Repr for OneofOptions
deriving instance Repr for EnumOptions
deriving instance Repr for EnumValueOptions
deriving instance Repr for ServiceOptions
deriving instance Repr for MethodOptions.IdempotencyLevel
deriving instance Repr for MethodOptions
