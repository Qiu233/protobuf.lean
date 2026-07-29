module

public import Protobuf

open Lean Protobuf Protobuf.Notation
open scoped Protobuf.Notation

public section

-- A standalone oneof used by `OneofParentCollisions` to verify that its static
-- alternative metadata survives an `.olean` boundary.
oneof OneofParentImportedChoice {
  int32 imported_value = 7;
  string imported_label = 8;
}
