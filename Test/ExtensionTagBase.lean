module

public import Protobuf

open Protobuf Protobuf.Notation
open scoped Protobuf.Notation

public section

message ImportedExtensionTagHost {
}

extend ImportedExtensionTagHost {
  optional int32 imported_value = 300;
}
