module

public import Protobuf.Internal.Desc.Base
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

enum FieldOptions.CType [closed = true] {
  STRING = 0;

  CORD = 1;

  STRING_PIECE = 2;
}

enum FieldOptions.JSType [closed = true] {
  JS_NORMAL = 0;

  JS_STRING = 1;

  JS_NUMBER = 2;
}

enum FieldOptions.OptionRetention [closed = true] {
  RETENTION_UNKNOWN = 0;
  RETENTION_RUNTIME = 1;
  RETENTION_SOURCE = 2;
}

enum FieldOptions.OptionTargetType [closed = true] {
  TARGET_TYPE_UNKNOWN = 0;
  TARGET_TYPE_FILE = 1;
  TARGET_TYPE_EXTENSION_RANGE = 2;
  TARGET_TYPE_MESSAGE = 3;
  TARGET_TYPE_FIELD = 4;
  TARGET_TYPE_ONEOF = 5;
  TARGET_TYPE_ENUM = 6;
  TARGET_TYPE_ENUM_ENTRY = 7;
  TARGET_TYPE_SERVICE = 8;
  TARGET_TYPE_METHOD = 9;
}

message FieldOptions.EditionDefault {
  optional Edition edition = 3;
  optional string value = 2;
}

message FieldOptions.FeatureSupport {
  optional Edition edition_introduced = 1;

  optional Edition edition_deprecated = 2;

  optional string deprecation_warning = 3;

  optional Edition edition_removed = 4;
}

local instance descOptionsSupportReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for FieldOptions.CType
deriving instance Repr for FieldOptions.JSType
deriving instance Repr for FieldOptions.OptionRetention
deriving instance Repr for FieldOptions.OptionTargetType
deriving instance Repr for FieldOptions.EditionDefault
deriving instance Repr for FieldOptions.FeatureSupport
