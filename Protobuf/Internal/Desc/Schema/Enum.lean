module

public import Protobuf.Internal.Desc.Core
public import Protobuf.Internal.Desc.Options.Declaration
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

message EnumValueDescriptorProto {
  optional string name = 1;
  optional int32 number = 2;

  optional EnumValueOptions options = 3;
}

message EnumDescriptorProto.EnumReservedRange {
  optional int32 start = 1; optional int32 «end» = 2; }

message EnumDescriptorProto {
  optional string name = 1;

  repeated EnumValueDescriptorProto value = 2;

  optional EnumOptions options = 3;

  repeated EnumDescriptorProto.EnumReservedRange reserved_range = 4;

  repeated string reserved_name = 5;

  optional SymbolVisibility visibility = 6;
}

local instance descSchemaEnumReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for EnumValueDescriptorProto
deriving instance Repr for EnumDescriptorProto.EnumReservedRange
deriving instance Repr for EnumDescriptorProto
