module

public import Protobuf

open Protobuf Protobuf.Notation
open scoped Protobuf.Notation

public section

/-
A message and an embedded oneof defined in a separate module.  The importing
test verifies that their compile-time field-tag metadata survives the `.olean`
boundary.
-/
oneof ImportedExtensionKnownChoice {
  int32 imported_selected = 8;
  string imported_label = 9;
}

message ImportedExtensionKnownHost {
  int32 imported_ordinary = 7;
  ImportedExtensionKnownChoice imported_choice = 0;
}
