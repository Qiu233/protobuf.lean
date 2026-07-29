module

public import Protobuf.Encoding
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

enum Edition [closed = true] {
    EDITION_UNKNOWN = 0;

    EDITION_LEGACY = 900;

    EDITION_PROTO2 = 998;
    EDITION_PROTO3 = 999;

    EDITION_2023 = 1000;
    EDITION_2024 = 1001;
    EDITION_2026 = 1002;

    EDITION_UNSTABLE = 9999;

    EDITION_1_TEST_ONLY     = 1;
    EDITION_2_TEST_ONLY     = 2;
    EDITION_99997_TEST_ONLY = 99997;
    EDITION_99998_TEST_ONLY = 99998;
    EDITION_99999_TEST_ONLY = 99999;

    EDITION_MAX = 0x7FFFFFFF;
}

enum SymbolVisibility [closed = true] {
  VISIBILITY_UNSET = 0;
  VISIBILITY_LOCAL = 1;
  VISIBILITY_EXPORT = 2;
}

local instance descBaseReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for Edition
deriving instance Repr for SymbolVisibility
