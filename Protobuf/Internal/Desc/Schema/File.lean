module

public import Protobuf.Internal.Desc.Core
public import Protobuf.Internal.Desc.Options.File
public import Protobuf.Internal.Desc.Schema.Field
public import Protobuf.Internal.Desc.Schema.Enum
public import Protobuf.Internal.Desc.Schema.Service
public import Protobuf.Internal.Desc.Schema.Message
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

message FileDescriptorProto {
  optional string name = 1;
  optional string package = 2;
  repeated string dependency = 3;
  repeated int32 public_dependency = 10;
  repeated int32 weak_dependency = 11;
  repeated string option_dependency = 15;

  repeated DescriptorProto message_type = 4;
  repeated EnumDescriptorProto enum_type = 5;
  repeated ServiceDescriptorProto service = 6;
  repeated FieldDescriptorProto extension = 7;

  optional FileOptions options = 8;

  optional SourceCodeInfo source_code_info = 9;

  optional string «syntax» = 12;

  optional Edition edition = 14;
}

message FileDescriptorSet {
  repeated FileDescriptorProto file = 1;
}

local instance descSchemaFileReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for FileDescriptorProto
deriving instance Repr for FileDescriptorSet
