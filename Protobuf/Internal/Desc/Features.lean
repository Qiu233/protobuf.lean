module

public import Protobuf.Encoding
public import Protobuf.ProtoMessage
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

enum FeatureSet.FieldPresence [closed = true] {
  FIELD_PRESENCE_UNKNOWN = 0;
  EXPLICIT = 1;
  IMPLICIT = 2;
  LEGACY_REQUIRED = 3;
}

enum FeatureSet.EnumType [closed = true] {
  ENUM_TYPE_UNKNOWN = 0;
  OPEN = 1;
  CLOSED = 2;
}

enum FeatureSet.RepeatedFieldEncoding [closed = true] {
  REPEATED_FIELD_ENCODING_UNKNOWN = 0;
  PACKED = 1;
  EXPANDED = 2;
}

enum FeatureSet.Utf8Validation [closed = true] {
  UTF8_VALIDATION_UNKNOWN = 0;
  VERIFY = 2;
  NONE = 3;
}

enum FeatureSet.MessageEncoding [closed = true] {
  MESSAGE_ENCODING_UNKNOWN = 0;
  LENGTH_PREFIXED = 1;
  DELIMITED = 2;
}

enum FeatureSet.JsonFormat [closed = true] {
  JSON_FORMAT_UNKNOWN = 0;
  ALLOW = 1;
  LEGACY_BEST_EFFORT = 2;
}

enum FeatureSet.EnforceNamingStyle [closed = true] {
  ENFORCE_NAMING_STYLE_UNKNOWN = 0;
  STYLE2024 = 1;
  STYLE_LEGACY = 2;
  STYLE2026 = 3;
}

enum FeatureSet.VisibilityFeature.DefaultSymbolVisibility [closed = true] {
  DEFAULT_SYMBOL_VISIBILITY_UNKNOWN = 0;
  EXPORT_ALL = 1;
  EXPORT_TOP_LEVEL = 2;
  LOCAL_ALL = 3;
  STRICT = 4;
}

enum FeatureSet.ProtoLimitsFeature.EnforceProtoLimits [closed = true] {
  PROTO_LIMITS_UNKNOWN = 0;
  LEGACY_NO_EXPLICIT_LIMITS = 1;
  PROTO_LIMITS2026 = 2;
}

message FeatureSet {
  optional FeatureSet.FieldPresence field_presence = 1 [
    retention = RETENTION_RUNTIME,
    targets = TARGET_TYPE_FIELD,
    targets = TARGET_TYPE_FILE
  ];

  optional FeatureSet.EnumType enum_type = 2 [
    retention = RETENTION_RUNTIME,
    targets = TARGET_TYPE_ENUM,
    targets = TARGET_TYPE_FILE
  ];

  optional FeatureSet.RepeatedFieldEncoding repeated_field_encoding = 3 [
    retention = RETENTION_RUNTIME,
    targets = TARGET_TYPE_FIELD,
    targets = TARGET_TYPE_FILE
  ];

  optional FeatureSet.Utf8Validation utf8_validation = 4 [
    retention = RETENTION_RUNTIME,
    targets = TARGET_TYPE_FIELD,
    targets = TARGET_TYPE_FILE
  ];

  optional FeatureSet.MessageEncoding message_encoding = 5 [
    retention = RETENTION_RUNTIME,
    targets = TARGET_TYPE_FIELD,
    targets = TARGET_TYPE_FILE
  ];

  optional FeatureSet.JsonFormat json_format = 6 [
    retention = RETENTION_RUNTIME,
    targets = TARGET_TYPE_MESSAGE,
    targets = TARGET_TYPE_ENUM,
    targets = TARGET_TYPE_FILE
  ];

  optional FeatureSet.EnforceNamingStyle enforce_naming_style = 7 [
    retention = RETENTION_SOURCE,
    targets = TARGET_TYPE_FILE,
    targets = TARGET_TYPE_EXTENSION_RANGE,
    targets = TARGET_TYPE_MESSAGE,
    targets = TARGET_TYPE_FIELD,
    targets = TARGET_TYPE_ONEOF,
    targets = TARGET_TYPE_ENUM,
    targets = TARGET_TYPE_ENUM_ENTRY,
    targets = TARGET_TYPE_SERVICE,
    targets = TARGET_TYPE_METHOD
  ];

  optional FeatureSet.VisibilityFeature.DefaultSymbolVisibility
      default_symbol_visibility = 8 [
    retention = RETENTION_SOURCE,
    targets = TARGET_TYPE_FILE
  ];

  optional FeatureSet.ProtoLimitsFeature.EnforceProtoLimits enforce_proto_limits = 9 [
    retention = RETENTION_SOURCE,
    targets = TARGET_TYPE_ENUM,
    targets = TARGET_TYPE_MESSAGE,
    targets = TARGET_TYPE_FIELD,
    targets = TARGET_TYPE_ONEOF
  ];
}

local instance descFeaturesReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for FeatureSet.FieldPresence
deriving instance Repr for FeatureSet.EnumType
deriving instance Repr for FeatureSet.RepeatedFieldEncoding
deriving instance Repr for FeatureSet.Utf8Validation
deriving instance Repr for FeatureSet.MessageEncoding
deriving instance Repr for FeatureSet.JsonFormat
deriving instance Repr for FeatureSet.EnforceNamingStyle
deriving instance Repr for FeatureSet.VisibilityFeature.DefaultSymbolVisibility
deriving instance Repr for FeatureSet.ProtoLimitsFeature.EnforceProtoLimits
deriving instance Repr for FeatureSet
