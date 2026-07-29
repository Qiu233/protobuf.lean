module

public import Protobuf.Internal.Desc.Options.Field
public import Protobuf.Internal.Desc.Options.Declaration
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

enum FieldDescriptorProto.Type [closed = true] {
  TYPE_DOUBLE = 1;
  TYPE_FLOAT = 2;
  TYPE_INT64 = 3;
  TYPE_UINT64 = 4;
  TYPE_INT32 = 5;
  TYPE_FIXED64 = 6;
  TYPE_FIXED32 = 7;
  TYPE_BOOL = 8;
  TYPE_STRING = 9;
  TYPE_GROUP = 10;
  TYPE_MESSAGE = 11;
  TYPE_BYTES = 12;
  TYPE_UINT32 = 13;
  TYPE_ENUM = 14;
  TYPE_SFIXED32 = 15;
  TYPE_SFIXED64 = 16;
  TYPE_SINT32 = 17; TYPE_SINT64 = 18; }

enum FieldDescriptorProto.Label [closed = true] {
  LABEL_OPTIONAL = 1;
  LABEL_REPEATED = 3;
  LABEL_REQUIRED = 2;
}

message FieldDescriptorProto {
  optional string name = 1;
  optional int32 number = 3;
  optional FieldDescriptorProto.Label label = 4;

  optional FieldDescriptorProto.Type type = 5;

  optional string type_name = 6;

  optional string extendee = 2;

  -- Descriptor defaults for `string` may contain arbitrary bytes when UTF-8
  -- validation is disabled, so this bootstrap field must not validate UTF-8.
  optional raw_string default_value = 7;

  optional int32 oneof_index = 9;

  optional string json_name = 10;

  optional FieldOptions options = 8;

  optional bool proto3_optional = 17;
}

message OneofDescriptorProto {
  optional string name = 1;
  optional OneofOptions options = 2;
}

local instance descSchemaFieldReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for FieldDescriptorProto.Type
deriving instance Repr for FieldDescriptorProto.Label
deriving instance Repr for FieldDescriptorProto
deriving instance Repr for OneofDescriptorProto
