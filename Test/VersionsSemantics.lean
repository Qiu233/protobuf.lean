module

import Protobuf

open Protobuf Encoding
open Protobuf.Versions google.protobuf
open scoped Protobuf.Notation

#load_proto_file "Test/VersionsSemanticsProto2.proto"
#load_proto_file "Test/VersionsSemanticsEditions.proto"
#load_proto_file "Test/VersionsSemanticsProto3.proto"

/-
Exercise the programmatic descriptor boundary, not the `.proto` source parser.
Each generated command is rendered through the same safe printer used by the
standalone plugin, parsed again as real Lean source, and only then elaborated.
-/
run_cmd do
  let field
      (name : String) (number : Int32)
      (fieldType : FieldDescriptorProto.Type) (defaultValue : String) :
      FieldDescriptorProto := {
    name := some name
    number := some number
    label := some .LABEL_OPTIONAL
    type := some fieldType
    default_value := some defaultValue
  }
  let descriptor : FileDescriptorSet := {
    file := #[{
      name := some "handcrafted-numeric-defaults.proto"
      package := some "descriptor_numeric"
      «syntax» := some "proto2"
      message_type := #[{
        name := some "HandcraftedFloatDefaults"
        field := #[
          field "leading_zero_integer" 1 .TYPE_DOUBLE "077",
          field "invalid_source_octal" 2 .TYPE_DOUBLE "08",
          field "leading_zero_decimal" 3 .TYPE_DOUBLE "01.0",
          field "hexadecimal_float" 4 .TYPE_DOUBLE "0x1.8p1",
          field "long_infinity" 5 .TYPE_DOUBLE "infinity",
          field "negative_nan" 6 .TYPE_DOUBLE "-nan",
          field "negative_zero" 7 .TYPE_DOUBLE "-0",
          field "overflow" 8 .TYPE_DOUBLE "1e400",
          field "negative_underflow" 9 .TYPE_DOUBLE "-1e-4000",
          field "float_leading_zero" 10 .TYPE_FLOAT "077",
          field "float_hexadecimal" 11 .TYPE_FLOAT "0x1.8p-1",
          field "float_nan_payload" 12 .TYPE_FLOAT "NaN(payload)",
          field "float_negative_zero" 13 .TYPE_FLOAT "-0",
          field "float_double_rounding" 14 .TYPE_FLOAT "1.0000000596046448",
          field "float_max_rounded" 15 .TYPE_FLOAT "3.4028235e38",
          field "float_overflow" 16 .TYPE_FLOAT "3.4028236e38",
          field "float_min_subnormal" 17 .TYPE_FLOAT "1e-45",
          field "float_underflow" 18 .TYPE_FLOAT "1e-46",
          field "float_negative_underflow" 19 .TYPE_FLOAT "-1e-100",
          field "float_min_normal" 20 .TYPE_FLOAT "1.17549435e-38",
          field "double_exact_rounding" 21 .TYPE_DOUBLE "6952064596942408e65",
          field "float_safe_max_endpoint" 22 .TYPE_FLOAT "3.4028235677973366e38",
          field "float_safe_min_endpoint" 23 .TYPE_FLOAT "-3.4028235677973366e38",
          field "double_hex_subnormal_rounding" 24 .TYPE_DOUBLE "0x188ece39880d216fp-1083"
        ]
      }]
    }]
  }
  let commands ←
    match (compile_proto descriptor).run with
    | .ok commands => pure commands
    | .error err =>
        throwError
          "handcrafted numeric descriptor compilation failed: {err}"
  for command in commands do
    let rendered ←
      match Protobuf.Notation.PrettyPrinter.command.pprintSafe command with
      | .ok rendered => pure rendered
      | .error err =>
          throwError
            "safe descriptor command rendering failed: {err}"
    let reparsed ←
      match Lean.Parser.runParserCategory (← Lean.getEnv) `command rendered with
      | .ok reparsed => pure reparsed
      | .error err =>
          throwError
            "safe descriptor command did not parse again: {err}"
    Lean.Elab.Command.elabCommand reparsed

private def assert (cond : Bool) (msg : String) : IO Unit := do
  unless cond do
    throw (IO.userError msg)

private def assertEq [BEq α] (actual expected : α) (msg : String) : IO Unit :=
  assert (actual == expected) msg

private def assertMissingRequired
    (result : Except ProtoError α) (msg : String) : IO Unit := do
  match result with
  | .error (.missingRequiredField _) => pure ()
  | .error err =>
      throw (IO.userError s!"{msg}: expected missingRequiredField, got {err}")
  | .ok _ =>
      throw (IO.userError s!"{msg}: operation unexpectedly succeeded")

private def expectedBytes : ByteArray :=
  ⟨#[0, 1, 127, 128, 255, 92, 34, 39]⟩

private def positiveInfinity : Float :=
  Float.ofBits 0x7ff0000000000000

private def negativeInfinity : Float :=
  Float.ofBits 0xfff0000000000000

private def notANumber : Float :=
  Float.ofBits 0x7ff8000000000000

private def positiveInfinityFloat : Float32 :=
  Float32.ofBits 0x7f800000

private def negativeInfinityFloat : Float32 :=
  Float32.ofBits 0xff800000

private def notANumberFloat : Float32 :=
  Float32.ofBits 0x7fc00000

private def testHandcraftedDescriptorNumericDefaults : IO Unit := do
  let value : _root_.descriptor_numeric.HandcraftedFloatDefaults := default
  assertEq
    (Float.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».leading_zero_integer.get
        value))
    (Float.toBits (77 : Float))
    "descriptor double default 077 was interpreted as source-level octal"
  assertEq
    (Float.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».invalid_source_octal.get
        value))
    (Float.toBits (8 : Float))
    "descriptor double default 08 was rejected or changed"
  assertEq
    (Float.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».leading_zero_decimal.get
        value))
    (Float.toBits (1 : Float))
    "descriptor leading-zero decimal default changed"
  assertEq
    (Float.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».hexadecimal_float.get
        value))
    (Float.toBits (3 : Float))
    "descriptor hexadecimal floating default changed"
  assert
    (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».long_infinity.get
      value).isInf
    "descriptor infinity spelling did not normalize to infinity"
  assert
    (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».negative_nan.get
      value).isNaN
    "descriptor negative NaN spelling did not normalize to NaN"
  assertEq
    (Float.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».negative_zero.get
        value))
    0x8000000000000000
    "descriptor double negative zero lost its sign"
  assert
    (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».overflow.get
      value).isInf
    "descriptor double overflow did not become infinity"
  assertEq
    (Float.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».negative_underflow.get
        value))
    0x8000000000000000
    "descriptor double negative underflow did not become negative zero"
  assertEq
    (Float32.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_leading_zero.get
        value))
    (Float32.toBits (77 : Float32))
    "descriptor float default 077 was interpreted as source-level octal"
  assertEq
    (Float32.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_hexadecimal.get
        value))
    (Float32.toBits (0.75 : Float32))
    "descriptor hexadecimal float32 default changed"
  assert
    (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_nan_payload.get
      value).isNaN
    "descriptor float NaN payload did not normalize to NaN"
  assertEq
    (Float32.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_negative_zero.get
        value))
    0x80000000
    "descriptor float negative zero lost its sign"
  assertEq
    (Float32.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_double_rounding.get
        value))
    0x3f800000
    "descriptor float default bypassed the C++ double-to-float rounding step"
  assertEq
    (Float32.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_max_rounded.get
        value))
    0x7f7fffff
    "descriptor float max-finite rounded spelling became infinity"
  assert
    (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_overflow.get
      value).isInf
    "descriptor float overflow did not become infinity"
  assertEq
    (Float32.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_min_subnormal.get
        value))
    0x00000001
    "descriptor float minimum subnormal rounded incorrectly"
  assertEq
    (Float32.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_underflow.get
        value))
    0x00000000
    "descriptor float positive underflow did not become positive zero"
  assertEq
    (Float32.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_negative_underflow.get
        value))
    0x80000000
    "descriptor float negative underflow lost its sign"
  assertEq
    (Float32.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_min_normal.get
        value))
    0x00800000
    "descriptor float minimum normal rounded incorrectly"
  assertEq
    (Float.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».double_exact_rounding.get
        value))
    0x50b773eb90084b0d
    "descriptor double default did not use correctly rounded from_chars semantics"
  assertEq
    (Float32.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_safe_max_endpoint.get
        value))
    0x7f7fffff
    "descriptor float SafeDoubleToFloat positive endpoint became infinity"
  assertEq
    (Float32.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».float_safe_min_endpoint.get
        value))
    0xff7fffff
    "descriptor float SafeDoubleToFloat negative endpoint became infinity"
  assertEq
    (Float.toBits
      (_root_.descriptor_numeric.HandcraftedFloatDefaults.«Explicit.Default.Accessors».double_hex_subnormal_rounding.get
        value))
    0x000c47671cc40691
    "descriptor hexadecimal double subnormal rounded incorrectly"

private def testProto2Defaults : IO Unit := do
  assertEq
    _root_.test.versions.proto2.DefaultEnum.DEFAULT_ENUM_NEGATIVE.toInt32
    (-1 : Int32)
    "proto2 negative enum value changed"
  assert
    (_root_.test.versions.proto2.HelperNameAlias.«toInt32.protobuf» ==
      _root_.test.versions.proto2.HelperNameAlias.toInt32_)
    "reserved enum helper name collided with its underscore-suffixed alias"
  let value : _root_.test.versions.proto2.Defaults := default
  assert value.spaced.isNone "absent proto2 string default gained presence"
  assertEq (_root_.test.versions.proto2.Defaults.get_spaced value) "  padded \t"
    "proto2 explicit default value accessor did not return the schema default"
  assert (!_root_.test.versions.proto2.Defaults.has_spaced value)
    "proto2 explicit default accessor manufactured field presence"
  assert value.escaped.isNone "absent proto2 bytes default gained presence"
  assert value.enum_reserved_name.isNone "absent proto2 enum default gained presence"
  assertEq
    (_root_.test.versions.proto2.Defaults.get_enum_reserved_name value)
    _root_.test.versions.proto2.DefaultEnum.«builder.protobuf»
    "proto2 enum value accessor did not return its sanitized schema default"
  assert value.positive_infinity.isNone "absent proto2 +inf default gained presence"
  assert value.negative_infinity.isNone "absent proto2 -inf default gained presence"
  assert value.not_a_number.isNone "absent proto2 nan default gained presence"
  assert value.positive_infinity_float.isNone "absent proto2 float +inf gained presence"
  assert value.negative_infinity_float.isNone "absent proto2 float -inf gained presence"
  assert value.not_a_number_float.isNone "absent proto2 float nan gained presence"
  assertEq
    (_root_.test.versions.proto2.Defaults.get_octal_default value)
    (63 : Int32)
    "proto2 octal integer default was not interpreted by protoc semantics"
  assertEq
    (_root_.test.versions.proto2.Defaults.get_hex_default value)
    (4294967295 : UInt32)
    "proto2 hexadecimal integer default changed"
  let explicit : _root_.test.versions.proto2.Defaults := {
    spaced := some "  padded \t"
    escaped := some expectedBytes
    enum_reserved_name :=
      some _root_.test.versions.proto2.DefaultEnum.«builder.protobuf»
    positive_infinity := some positiveInfinity
    negative_infinity := some negativeInfinity
    not_a_number := some notANumber
    positive_infinity_float := some positiveInfinityFloat
    negative_infinity_float := some negativeInfinityFloat
    not_a_number_float := some notANumberFloat
  }
  let encoded ← match _root_.test.versions.proto2.Defaults.toMessage explicit with
    | .ok msg => pure msg
    | .error err => throw (IO.userError err.toString)
  let decoded ← match _root_.test.versions.proto2.Defaults.fromMessage encoded with
    | .ok result => pure result
    | .error err => throw (IO.userError err.toString)
  assertEq decoded.spaced explicit.spaced "proto2 spaced string default roundtrip changed"
  assertEq decoded.escaped explicit.escaped "proto2 escaped bytes default roundtrip changed"
  assertEq decoded.enum_reserved_name explicit.enum_reserved_name
    "proto2 sanitized enum default roundtrip changed"
  assert decoded.positive_infinity.get!.isInf "proto2 +inf default changed"
  assert (decoded.negative_infinity.get! == negativeInfinity)
    "proto2 -inf default changed"
  assert decoded.not_a_number.get!.isNaN "proto2 nan default changed"
  assert decoded.positive_infinity_float.get!.isInf "proto2 float +inf default changed"
  assert (decoded.negative_infinity_float.get! == negativeInfinityFloat)
    "proto2 float -inf default changed"
  assert decoded.not_a_number_float.get!.isNaN "proto2 float nan default changed"

private def testProto2FirstEnumDefault : IO Unit := do
  let first :=
    _root_.test.versions.proto2.NonZeroFirstEnum.NON_ZERO_FIRST
  assertEq
    _root_.test.versions.proto2.NonZeroFirstEnum.«Default.Value»
    first
    "proto2 implicit enum default did not use the first declaration"

  let empty : _root_.test.versions.proto2.NonZeroEnumDefaults := default
  assert
    (!_root_.test.versions.proto2.NonZeroEnumDefaults.has_nonzero_first_ext empty)
    "absent enum extension gained presence"
  let extensionDefault ← match
      _root_.test.versions.proto2.NonZeroEnumDefaults.get_nonzero_first_ext empty with
    | .ok result => pure result
    | .error err => throw (IO.userError err.toString)
  assertEq extensionDefault first
    "absent proto2 enum extension did not expose the first declaration"

private def testProto2RequiredPresence : IO Unit := do
  let absent : _root_.test.versions.proto2.RequiredFields := default
  assert absent.scalar.isNone "default proto2 required scalar gained presence"
  assert absent.enum_value.isNone "default proto2 required enum gained presence"
  assertEq (_root_.test.versions.proto2.RequiredFields.get_scalar absent) (0 : Int32)
    "required scalar value accessor did not expose its explicit default"
  assert (!_root_.test.versions.proto2.RequiredFields.has_scalar absent)
    "required scalar default manufactured presence"
  assertMissingRequired
    (_root_.test.versions.proto2.RequiredFields.toMessage absent)
    "encoding absent proto2 required fields"
  assertMissingRequired
    (_root_.test.versions.proto2.RequiredFields.fromMessage Message.empty)
    "decoding absent proto2 required fields"

  let present : _root_.test.versions.proto2.RequiredFields := {
    scalar := some 0
    enum_value := some _root_.test.versions.proto2.DefaultEnum.DEFAULT_ENUM_ZERO
  }
  let wire ← match _root_.test.versions.proto2.RequiredFields.toMessage present with
    | .ok msg => pure msg
    | .error err => throw (IO.userError err.toString)
  assertEq (wire.getRecordsOf 1).size 1
    "present proto2 required scalar default was omitted"
  assertEq (wire.getRecordsOf 2).size 1
    "present proto2 required enum default was omitted"
  let decoded ← match _root_.test.versions.proto2.RequiredFields.fromMessage wire with
    | .ok result => pure result
    | .error err => throw (IO.userError err.toString)
  assertEq decoded.scalar present.scalar
    "proto2 required scalar default did not roundtrip with presence"
  assertEq decoded.enum_value present.enum_value
    "proto2 required enum default did not roundtrip with presence"

  let older : _root_.test.versions.proto2.RequiredFields := {
    scalar := some 1
    enum_value := some _root_.test.versions.proto2.DefaultEnum.DEFAULT_ENUM_ZERO
  }
  let newer : _root_.test.versions.proto2.RequiredFields := {
    scalar := some 0
    enum_value :=
      some _root_.test.versions.proto2.DefaultEnum.«builder.protobuf»
  }
  let merged := _root_.test.versions.proto2.RequiredFields.merge older newer
  assertEq merged.scalar newer.scalar
    "proto2 required scalar merge did not prefer later presence"
  assertEq merged.enum_value newer.enum_value
    "proto2 required enum merge did not prefer later presence"
  let keepOlder :=
    _root_.test.versions.proto2.RequiredFields.merge older default
  assertEq keepOlder.scalar older.scalar
    "proto2 required scalar merge discarded earlier presence"
  assertEq keepOlder.enum_value older.enum_value
    "proto2 required enum merge discarded earlier presence"

private def testEditionsDefaults : IO Unit := do
  assertEq
    _root_.test.versions.editions.DefaultEnum.DEFAULT_ENUM_NEGATIVE.toInt32
    (-1 : Int32)
    "Editions negative enum value changed"
  let value : _root_.test.versions.editions.Semantics := default
  assert value.spaced.isNone "absent Editions string default gained presence"
  assert value.escaped.isNone "absent Editions bytes default gained presence"
  assert value.enum_reserved_name.isNone "absent Editions enum default gained presence"
  assert value.positive_infinity.isNone "absent Editions +inf default gained presence"
  assert value.negative_infinity.isNone "absent Editions -inf default gained presence"
  assert value.not_a_number.isNone "absent Editions nan default gained presence"
  assert value.positive_infinity_float.isNone "absent Editions float +inf gained presence"
  assert value.negative_infinity_float.isNone "absent Editions float -inf gained presence"
  assert value.not_a_number_float.isNone "absent Editions float nan gained presence"
  assert value.required.isNone "default Editions required scalar gained presence"
  assert value.required_enum.isNone "default Editions required enum gained presence"
  assertMissingRequired
    (_root_.test.versions.editions.Semantics.toMessage value)
    "encoding absent Editions required fields"
  assertMissingRequired
    (_root_.test.versions.editions.Semantics.fromMessage Message.empty)
    "decoding absent Editions required fields"

  let encoded ← match _root_.test.versions.editions.Semantics.toMessage {
      value with
      spaced := some "  padded \t"
      escaped := some expectedBytes
      enum_reserved_name :=
        some _root_.test.versions.editions.DefaultEnum.«builder.protobuf»
      positive_infinity := some positiveInfinity
      negative_infinity := some negativeInfinity
      not_a_number := some notANumber
      positive_infinity_float := some positiveInfinityFloat
      negative_infinity_float := some negativeInfinityFloat
      not_a_number_float := some notANumberFloat
      implicit := 0
      explicit := some 0
      required := some 0
      packed := #[1, 2]
      expanded := #[3, 4]
      required_enum := some _root_.test.versions.editions.DefaultEnum.DEFAULT_ENUM_ZERO
    } with
    | .ok msg => pure msg
    | .error err => throw (IO.userError err.toString)
  assert (encoded.getRecordsOf 10).isEmpty
    "Editions IMPLICIT scalar default should not be encoded"
  assertEq (encoded.getRecordsOf 11).size 1
    "Editions EXPLICIT scalar default should be encoded when present"
  assertEq (encoded.getRecordsOf 12).size 1
    "Editions required scalar default should be encoded when present"
  assertEq (encoded.getRecordsOf 13).size 1
    "Editions PACKED repeated field should use one record"
  assertEq (encoded.getRecordsOf 14).size 2
    "Editions EXPANDED repeated field should use one record per value"
  assertEq (encoded.getRecordsOf 15).size 1
    "Editions required enum default should be encoded when present"
  let decoded ← match _root_.test.versions.editions.Semantics.fromMessage encoded with
    | .ok result => pure result
    | .error err => throw (IO.userError err.toString)
  assertEq decoded.required (some 0)
    "Editions required scalar default did not roundtrip with presence"
  assertEq decoded.required_enum
    (some _root_.test.versions.editions.DefaultEnum.DEFAULT_ENUM_ZERO)
    "Editions required enum default did not roundtrip with presence"

private def testProto3Mapping : IO Unit := do
  assertEq
    _root_.test.versions.proto3.SignedEnum.SIGNED_ENUM_NEGATIVE.toInt32
    (-1 : Int32)
    "proto3 negative enum value changed"
  let value : _root_.test.versions.proto3.Semantics := {
    implicit := 0
    explicit := some 0
    packed := #[1, 2]
    expanded := #[3, 4]
    aliased_enum :=
      _root_.test.versions.proto3.AliasedEnum.ALIASED_ENUM_ZERO_ALIAS
  }
  let encoded ← match _root_.test.versions.proto3.Semantics.toMessage value with
    | .ok msg => pure msg
    | .error err => throw (IO.userError err.toString)
  assert (encoded.getRecordsOf 1).isEmpty
    "proto3 implicit scalar default should not be encoded"
  assertEq (encoded.getRecordsOf 2).size 1
    "proto3 optional scalar default should be encoded when present"
  assertEq (encoded.getRecordsOf 3).size 1
    "proto3 repeated primitive should default to packed"
  assertEq (encoded.getRecordsOf 4).size 2
    "proto3 packed=false should use expanded encoding"
  assert
    (_root_.test.versions.proto3.AliasedEnum.ALIASED_ENUM_ZERO ==
      _root_.test.versions.proto3.AliasedEnum.ALIASED_ENUM_ZERO_ALIAS)
    "protobuf enum aliases were not equal by numeric value"
  assert (encoded.getRecordsOf 6).isEmpty
    "zero-valued enum alias was encoded as a non-default field"
  let decoded ← match
      _root_.test.versions.proto3.Semantics.fromMessage encoded with
    | .ok result => pure result
    | .error err => throw (IO.userError err.toString)
  assert
    (decoded.aliased_enum ==
      _root_.test.versions.proto3.AliasedEnum.ALIASED_ENUM_ZERO_ALIAS)
    "enum alias did not roundtrip by numeric value"

public def main : IO Unit := do
  testHandcraftedDescriptorNumericDefaults
  testProto2Defaults
  testProto2FirstEnumDefault
  testProto2RequiredPresence
  testEditionsDefaults
  testProto3Mapping
