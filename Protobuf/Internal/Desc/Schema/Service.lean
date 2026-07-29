module

public import Protobuf.Internal.Desc.Options.Declaration
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

message MethodDescriptorProto {
  optional string name = 1;

  optional string input_type = 2;
  optional string output_type = 3;

  optional MethodOptions options = 4;

  optional bool client_streaming = 5 [default = false];
  optional bool server_streaming = 6 [default = false];
}

message ServiceDescriptorProto {
  optional string name = 1;
  repeated MethodDescriptorProto method = 2;

  optional ServiceOptions options = 3;
}

local instance descSchemaServiceReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for MethodDescriptorProto
deriving instance Repr for ServiceDescriptorProto
