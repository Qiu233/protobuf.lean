module

public import Protobuf.Internal.Desc.Base
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

message UninterpretedOption.NamePart {
  required string name_part = 1;
  required bool is_extension = 2;
}

message UninterpretedOption {
  repeated UninterpretedOption.NamePart name = 2;

  optional string identifier_value = 3;
  optional uint64 positive_int_value = 4;
  optional int64 negative_int_value = 5;
  optional double double_value = 6;
  optional bytes string_value = 7;
  optional string aggregate_value = 8;
}

message SourceCodeInfo.Location {
  repeated int32 path = 1 [packed = true];

  repeated int32 span = 2 [packed = true];

  optional string leading_comments = 3;
  optional string trailing_comments = 4;
  repeated string leading_detached_comments = 6;
}

message SourceCodeInfo {
  repeated SourceCodeInfo.Location location = 1;
}

enum GeneratedCodeInfo.Annotation.Semantic [closed = true] {
  NONE = 0;
  SET = 1;
  ALIAS = 2;
}

message GeneratedCodeInfo.Annotation {
  repeated int32 path = 1 [packed = true];

  optional string source_file = 2;

  optional int32 begin = 3;

  optional int32 «end» = 4;

  optional GeneratedCodeInfo.Annotation.Semantic semantic = 5;
}

message GeneratedCodeInfo {
  repeated GeneratedCodeInfo.Annotation annotation = 1;
}

local instance descCoreReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for UninterpretedOption.NamePart, UninterpretedOption
deriving instance Repr for SourceCodeInfo.Location, SourceCodeInfo
deriving instance Repr for GeneratedCodeInfo.Annotation.Semantic, GeneratedCodeInfo.Annotation, GeneratedCodeInfo
