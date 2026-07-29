module

public import Protobuf.Internal.Desc.Options.Declaration
public import Protobuf.Internal.Desc.Schema.Field
public import Protobuf.Internal.Desc.Schema.Enum
public import Protobuf.Internal.Desc.Schema.Extension
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

message DescriptorProto.ExtensionRange {
  optional int32 start = 1; optional int32 «end» = 2;
  optional ExtensionRangeOptions options = 3;
}

message DescriptorProto.ReservedRange {
  optional int32 start = 1; optional int32 «end» = 2; }

message DescriptorProto {
  optional string name = 1;

  repeated FieldDescriptorProto field = 2;
  repeated FieldDescriptorProto extension = 6;

  repeated DescriptorProto nested_type = 3;
  repeated EnumDescriptorProto enum_type = 4;

  repeated DescriptorProto.ExtensionRange extension_range = 5;

  repeated OneofDescriptorProto oneof_decl = 8;

  optional MessageOptions options = 7;

  repeated DescriptorProto.ReservedRange reserved_range = 9;
  repeated string reserved_name = 10;

  optional SymbolVisibility visibility = 11;
}

local instance descSchemaMessageReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for DescriptorProto.ExtensionRange
deriving instance Repr for DescriptorProto.ReservedRange
deriving instance Repr for DescriptorProto
