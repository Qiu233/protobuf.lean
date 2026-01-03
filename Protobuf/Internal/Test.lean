import Protobuf.Notation

namespace Protobuf.Internal

open Encoding Notation


enum Edition {
    EDITION_UNKNOWN = 0;

    EDITION_LEGACY = 900;

    EDITION_PROTO2 = 998;
    EDITION_PROTO3 = 999;

    EDITION_2023 = 1000;
    EDITION_2024 = 1001;

    EDITION_1_TEST_ONLY     = 1;
    EDITION_2_TEST_ONLY     = 2;
    EDITION_99997_TEST_ONLY = 99997;
    EDITION_99998_TEST_ONLY = 99998;
    EDITION_99999_TEST_ONLY = 99999;

    EDITION_MAX = 0x7FFFFFFF;
}

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

oneof A {
  int32 a = 1;
  Edition edition = 2;
  UninterpretedOption o = 3;
}

message T {
  A v = 0;
}

proto_mutual {
  message B {
    C c = 1;
  }

  oneof C.T {
    C t = 1;
  }

  message C {
    B b = 1;
    C.T f = 0;
  }
}
