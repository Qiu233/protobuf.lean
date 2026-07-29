module

public import Protobuf.Internal.Desc.Core
public import Protobuf.Internal.Desc.Features
public import Protobuf.Internal.Desc.Options.Support
meta import Protobuf.Notation

public section

namespace google.protobuf

open Protobuf Encoding Notation

message FieldOptions {
  optional FieldOptions.CType ctype = 1 [default = STRING];

  optional bool packed = 2;

  optional FieldOptions.JSType jstype = 6 [default = JS_NORMAL];

  optional bool lazy = 5 [default = false];

  optional bool unverified_lazy = 15 [default = false];

  optional bool deprecated = 3 [default = false];

  optional bool weak = 10 [default = false];

  optional bool debug_redact = 16 [default = false];

  optional FieldOptions.OptionRetention retention = 17;

  repeated FieldOptions.OptionTargetType targets = 19;

  repeated FieldOptions.EditionDefault edition_defaults = 20;

  optional FeatureSet features = 21;

  optional FieldOptions.FeatureSupport feature_support = 22;

  repeated UninterpretedOption uninterpreted_option = 999;
}

message FeatureSetDefaults.FeatureSetEditionDefault {
  optional Edition edition = 3;

  optional FeatureSet overridable_features = 4;

  optional FeatureSet fixed_features = 5;
}

message FeatureSetDefaults {
  repeated FeatureSetDefaults.FeatureSetEditionDefault defaults = 1;

  optional Edition minimum_edition = 4;

  optional Edition maximum_edition = 5;
}

local instance descOptionsFieldReprByteArray : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

deriving instance Repr for FieldOptions
deriving instance Repr for FeatureSetDefaults.FeatureSetEditionDefault
deriving instance Repr for FeatureSetDefaults
