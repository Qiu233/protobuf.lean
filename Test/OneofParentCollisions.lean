module

import Protobuf
import Test.OneofParentCollisionBase

open Lean Protobuf Protobuf.Notation
open scoped Protobuf.Notation

#check OneofParentImportedChoice.«protobuf.internal».toMessage
#check OneofParentImportedChoice.«protobuf.internal».merge
#check OneofParentImportedChoice.«protobuf.internal».acceptsRecord
#check OneofParentImportedChoice.«protobuf.internal».fromMessage?

message OneofParentImportedValid {
  int32 ordinary = 1;
  OneofParentImportedChoice choice = 0;
}

/-- error: protobuf field number 7 from embedded oneof `OneofParentImportedChoice` is declared more than once -/
#guard_msgs in
message OneofParentImportedTagConflict {
  int32 ordinary = 7;
  OneofParentImportedChoice choice = 0;
}

/-- error: protobuf field name `imported_value` from embedded oneof `OneofParentImportedChoice` is declared more than once -/
#guard_msgs in
message OneofParentImportedNameConflict {
  int32 imported_value = 1;
  OneofParentImportedChoice choice = 0;
}

-- The message deliberately precedes its oneof. The mutual elaborator must
-- pre-scan alternatives rather than querying a declaration that does not exist
-- yet.
/-- error: protobuf field number 11 from embedded oneof `OneofParentMutualTagChoice` is declared more than once -/
#guard_msgs in
proto_mutual {
  message OneofParentMutualOrdinaryTagConflict {
    int32 ordinary = 11;
    OneofParentMutualTagChoice choice = 0;
  }
  oneof OneofParentMutualTagChoice {
    string selected = 11;
  }
}

/-- error: protobuf field name `selected` from embedded oneof `OneofParentMutualNameChoice` is declared more than once -/
#guard_msgs in
proto_mutual {
  message OneofParentMutualOrdinaryNameConflict {
    int32 selected = 12;
    OneofParentMutualNameChoice choice = 0;
  }
  oneof OneofParentMutualNameChoice {
    string selected = 13;
  }
}

/-- error: protobuf field number 21 from embedded oneof `OneofParentMutualTagChoiceB` is declared more than once -/
#guard_msgs in
proto_mutual {
  message OneofParentMutualOneofTagConflict {
    OneofParentMutualTagChoiceA first_choice = 0;
    OneofParentMutualTagChoiceB second_choice = 0;
  }
  oneof OneofParentMutualTagChoiceA {
    int32 first_value = 21;
  }
  oneof OneofParentMutualTagChoiceB {
    string second_value = 21;
  }
}

/-- error: protobuf field name `duplicate_name` from embedded oneof `OneofParentMutualNameChoiceB` is declared more than once -/
#guard_msgs in
proto_mutual {
  message OneofParentMutualOneofNameConflict {
    OneofParentMutualNameChoiceA first_choice = 0;
    OneofParentMutualNameChoiceB second_choice = 0;
  }
  oneof OneofParentMutualNameChoiceA {
    int32 duplicate_name = 31;
  }
  oneof OneofParentMutualNameChoiceB {
    string duplicate_name = 32;
  }
}

-- A non-conflicting mutual block still elaborates and generates the normal
-- schema-specialized API.
proto_mutual {
  message OneofParentMutualValid {
    int32 ordinary = 40;
    OneofParentMutualValidChoice choice = 0;
  }
  oneof OneofParentMutualValidChoice {
    int32 selected = 41;
    string label = 42;
  }
}

message OneofParentAfterMutualValid {
  int32 ordinary = 50;
  OneofParentMutualValidChoice choice = 0;
}

#synth Protobuf.ProtoMessage OneofParentImportedValid
#synth Protobuf.ProtoMessage OneofParentMutualValid
#synth Protobuf.ProtoMessage OneofParentAfterMutualValid
