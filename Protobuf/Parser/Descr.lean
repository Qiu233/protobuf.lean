import Protobuf.Parser.Grammar
import Lake
open Lean Parser Elab Command

namespace Protobuf.Parser

/-!
// Describes a complete .proto file.
message FileDescriptorProto {
  optional string name = 1;     // file name, relative to root of source tree
  optional string package = 2;  // e.g. "foo", "foo.bar", etc.

  // Names of files imported by this file.
  repeated string dependency = 3;
  // Indexes of the public imported files in the dependency list above.
  repeated int32 public_dependency = 10;
  // Indexes of the weak imported files in the dependency list.
  // For Google-internal migration only. Do not use.
  repeated int32 weak_dependency = 11;

  // All top-level definitions in this file.
  repeated DescriptorProto message_type = 4;
  repeated EnumDescriptorProto enum_type = 5;
  repeated ServiceDescriptorProto service = 6;
  repeated FieldDescriptorProto extension = 7;

  optional FileOptions options = 8;

  // This field contains optional information about the original source code.
  // You may safely remove this entire field without harming runtime
  // functionality of the descriptors -- the information is needed only by
  // development tools.
  optional SourceCodeInfo source_code_info = 9;

  // The syntax of the proto file.
  // The supported values are "proto2", "proto3", and "editions".
  //
  // If `edition` is present, this value must be "editions".
  optional string syntax = 12;

  // The edition of the proto file.
  optional Edition edition = 14;
}
-/
