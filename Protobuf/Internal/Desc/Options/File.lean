module

public import Protobuf.Internal.Desc.Core
public import Protobuf.Internal.Desc.Features
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

enum FileOptions.OptimizeMode [closed = true] {
  SPEED = 1; CODE_SIZE = 2; LITE_RUNTIME = 3; }

message FileOptions {
  optional string java_package = 1;

  optional string java_outer_classname = 8;

  optional bool java_multiple_files = 10 [default = false];

  optional bool java_generate_equals_and_hash = 20 [deprecated = true];

  optional bool java_string_check_utf8 = 27 [default = false];

  optional FileOptions.OptimizeMode optimize_for = 9 [default = SPEED];

  optional string go_package = 11;

  optional bool cc_generic_services = 16 [default = false];
  optional bool java_generic_services = 17 [default = false];
  optional bool py_generic_services = 18 [default = false];

  optional bool deprecated = 23 [default = false];

  optional bool cc_enable_arenas = 31 [default = true];

  optional string objc_class_prefix = 36;

  optional string csharp_namespace = 37;

  optional string swift_prefix = 39;

  optional string php_class_prefix = 40;

  optional string php_namespace = 41;

  optional string php_metadata_namespace = 44;

  optional string ruby_package = 45;

  optional FeatureSet features = 50;

  repeated UninterpretedOption uninterpreted_option = 999;
}

local instance descOptionsFileReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for FileOptions.OptimizeMode
deriving instance Repr for FileOptions
