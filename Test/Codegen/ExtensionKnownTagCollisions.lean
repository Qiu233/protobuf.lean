module

import Protobuf
import Test.Codegen.ExtensionKnownTagCollisionsBase

open Protobuf Protobuf.Notation
open scoped Protobuf.Notation

message StandaloneExtensionKnownHost {
  int32 ordinary = 1;
}

/-- error: protobuf extension field number 1 for `StandaloneExtensionKnownHost` conflicts with declared field `ordinary` -/
#guard_msgs in
extend StandaloneExtensionKnownHost {
  optional string duplicate_ordinary = 1;
}

oneof StandaloneExtensionKnownChoice {
  int32 selected = 2;
  string label = 3;
}

message StandaloneExtensionKnownOneofHost {
  StandaloneExtensionKnownChoice choice = 0;
}

/-- error: protobuf extension field number 2 for `StandaloneExtensionKnownOneofHost` conflicts with declared field `selected` -/
#guard_msgs in
extend StandaloneExtensionKnownOneofHost {
  optional bytes duplicate_selected = 2;
}

-- The message deliberately precedes its oneof.  Both ordinary and alternative
-- tags must be collected from the successfully elaborated mutual block.
proto_mutual {
  message MutualExtensionKnownHost {
    int32 mutual_ordinary = 20;
    MutualExtensionKnownChoice mutual_choice = 0;
  }
  oneof MutualExtensionKnownChoice {
    int32 mutual_selected = 21;
    string mutual_label = 22;
  }
}

/-- error: protobuf extension field number 20 for `MutualExtensionKnownHost` conflicts with declared field `mutual_ordinary` -/
#guard_msgs in
extend MutualExtensionKnownHost {
  optional string duplicate_mutual_ordinary = 20;
}

/-- error: protobuf extension field number 21 for `MutualExtensionKnownHost` conflicts with declared field `mutual_selected` -/
#guard_msgs in
extend MutualExtensionKnownHost {
  optional string duplicate_mutual_selected = 21;
}

/-- error: protobuf extension field number 7 for `ImportedExtensionKnownHost` conflicts with declared field `imported_ordinary` -/
#guard_msgs in
extend ImportedExtensionKnownHost {
  optional string duplicate_imported_ordinary = 7;
}

/-- error: protobuf extension field number 8 for `ImportedExtensionKnownHost` conflicts with declared field `imported_selected` -/
#guard_msgs in
extend ImportedExtensionKnownHost {
  optional string duplicate_imported_selected = 8;
}

-- A genuinely unoccupied tag still generates the normal static extension API.
extend StandaloneExtensionKnownHost {
  optional int32 legal_extension = 100;
}

extend MutualExtensionKnownHost {
  repeated fixed32 legal_mutual_extension = 101 [packed = true];
}

extend ImportedExtensionKnownHost {
  optional string legal_imported_extension = 102;
}

#check StandaloneExtensionKnownHost.get_legal_extension?
#check StandaloneExtensionKnownHost.set_legal_extension
#check MutualExtensionKnownHost.get_legal_mutual_extension?
#check ImportedExtensionKnownHost.set_legal_imported_extension
