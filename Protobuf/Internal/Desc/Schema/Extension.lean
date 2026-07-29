module

public import Protobuf.Internal.Desc.Core
public import Protobuf.Internal.Desc.Features
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

enum ExtensionRangeOptions.VerificationState [closed = true] {
  DECLARATION = 0;
  UNVERIFIED = 1;
}

message ExtensionRangeOptions.Declaration {
  optional int32 number = 1;

  optional string full_name = 2;

  optional string type = 3;

  optional bool reserved = 5;

  optional bool «repeated» = 6;
}

message ExtensionRangeOptions {
  repeated UninterpretedOption uninterpreted_option = 999;

  repeated ExtensionRangeOptions.Declaration declaration = 2 [retention = RETENTION_SOURCE];

  optional FeatureSet features = 50;

  optional ExtensionRangeOptions.VerificationState verification = 3
      [default = UNVERIFIED, retention = RETENTION_SOURCE];
}

local instance descSchemaExtensionReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for ExtensionRangeOptions.VerificationState
deriving instance Repr for ExtensionRangeOptions.Declaration
deriving instance Repr for ExtensionRangeOptions
