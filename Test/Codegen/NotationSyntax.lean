module

import Protobuf
import Test.Codegen.ExtensionTagBase

open Lean
open Protobuf
open Protobuf.Notation
open scoped Protobuf.Notation

run_meta do
  let value ← `(enum_value| -1)
  unless Protobuf.Notation.PrettyPrinter.enum_value.pprint value == "-1" do
    throwError "signed enum value did not survive quotation/pretty-printing"
  match Protobuf.Notation.PrettyPrinter.enum_value.pprintSafe value with
  | .ok "-1" => pure ()
  | .ok rendered =>
      throwError
        "safe enum pretty-printer produced unexpected output {rendered.quote}"
  | .error err =>
      throwError "safe enum pretty-printer rejected valid syntax: {err}"
  let env ← getEnv
  let expectCategory
      (category : Name) (input : String) (shouldParse : Bool) :
      MetaM Unit := do
    match Parser.runParserCategory env category input, shouldParse with
    | .ok _, true | .error _, false => pure ()
    | .ok parsed, false =>
        throwError
          "parser category {category} unexpectedly accepted {input.quote}: {repr parsed}"
    | .error err, true =>
        throwError
          "parser category {category} unexpectedly rejected {input.quote}: {err}"
  for text in #["0", "077", "0x10", "0X10", "-077", "- 011"] do
    expectCategory `enum_value text true
  for text in #["+1", "0o77", "0b11", "08", "09", "1_0"] do
    expectCategory `enum_value text false
  for text in
      #["077", "-077", ".5", "- .5", "1.", "1.e+2", "0e2",
        "-inf", "-nan"] do
    expectCategory `options_value text true
  for text in
      #["+077", "+.5", "+inf", "+nan", "00.5", "01e2", "0o77",
        "0b11", "08", "1_0", "1f", "1F", "1.0f", ".5F", "1e2f"] do
    expectCategory `options_value text false
  for text in
      #["message NumericProbe { int32 value = 077; }",
        "message NumericProbe { int32 value = 0x10; }"] do
    expectCategory `command text true
  for text in
      #["message NumericProbe { int32 value = -1; }",
        "message NumericProbe { int32 value = +1; }",
        "message NumericProbe { int32 value = 0o1; }",
        "message NumericProbe { int32 value = 08; }"] do
    expectCategory `command text false

  let octalNum : TSyntax `num := ⟨Syntax.mkNumLit "077"⟩
  let quotedOctal ← `(enum_value| $octalNum:num)
  let octalRendered ←
    match PrettyPrinter.enum_value.pprintSafe quotedOctal with
    | .ok rendered => pure rendered
    | .error err =>
        throwError "safe enum printer rejected injected protobuf octal: {err}"
  unless octalRendered == "63" do
    throwError
      "safe enum printer did not canonicalize protobuf octal: {octalRendered}"
  match Parser.runParserCategory env `enum_value octalRendered with
  | .ok _ => pure ()
  | .error err =>
      throwError "canonical enum octal did not reparse: {err}"

  let optionOctal ← `(options_value| $octalNum:num)
  let optionRendered ←
    match PrettyPrinter.options_value.pprintSafe optionOctal with
    | .ok rendered => pure rendered
    | .error err =>
        throwError "safe option printer rejected injected protobuf octal: {err}"
  unless optionRendered == "63" do
    throwError
      "safe option printer did not canonicalize protobuf octal: {optionRendered}"
  match Parser.runParserCategory env `options_value optionRendered with
  | .ok _ => pure ()
  | .error err =>
      throwError "canonical option octal did not reparse: {err}"

  let fieldOctal ←
    `(message_entry| int32 octal_field = $octalNum:num;)
  let fieldRendered ←
    match PrettyPrinter.message_entry.pprintSafe fieldOctal with
    | .ok rendered => pure rendered
    | .error err =>
        throwError "safe field printer rejected injected protobuf octal: {err}"
  unless fieldRendered.contains "= 63;" do
    throwError
      "safe field printer did not canonicalize protobuf octal: {fieldRendered}"
  let fieldCommand :=
    s!"message SafeFieldProbe \{{fieldRendered}}"
  match Parser.runParserCategory env `command fieldCommand with
  | .ok _ => pure ()
  | .error err =>
      throwError "canonical field octal did not reparse: {err}"

  let invalidNum : TSyntax `num := ⟨Syntax.mkNumLit "0o77"⟩
  let invalidEnum ← `(enum_value| $invalidNum:num)
  let invalidOption ← `(options_value| $invalidNum:num)
  let invalidField ←
    `(message_entry| int32 invalid_field = $invalidNum:num;)
  for rendered in
      #[PrettyPrinter.enum_value.pprintSafe invalidEnum,
        PrettyPrinter.options_value.pprintSafe invalidOption,
        PrettyPrinter.message_entry.pprintSafe invalidField] do
    match rendered with
    | .error _ => pure ()
    | .ok output =>
        throwError
          "safe protobuf printer accepted injected Lean-only numeral as {output}"

  let plusMagnitude : TSyntax `num := ⟨Syntax.mkNumLit "1"⟩
  let injectedPlus ← `(options_value| +$plusMagnitude:num)
  match PrettyPrinter.options_value.pprintSafe injectedPlus with
  | .error _ => pure ()
  | .ok output =>
      throwError
        "safe option printer accepted quotation-only leading plus as {output}"

  let invalidFloat : TSyntax `scientific :=
    ⟨Syntax.mkScientificLit "00.5"⟩
  let injectedInvalidFloat ←
    `(options_value| $invalidFloat:scientific)
  match PrettyPrinter.options_value.pprintSafe injectedInvalidFloat with
  | .error _ => pure ()
  | .ok output =>
      throwError
        "safe option printer accepted invalid leading-zero float as {output}"

  let leadingDot ← `(options_value| .5)
  let leadingDotRendered ←
    match PrettyPrinter.options_value.pprintSafe leadingDot with
    | .ok rendered => pure rendered
    | .error err =>
        throwError "safe option printer rejected leading-dot float: {err}"
  unless leadingDotRendered == "0.5" do
    throwError
      "leading-dot float did not normalize for Lean elaboration: {leadingDotRendered}"
  match Parser.runParserCategory env `options_value leadingDotRendered with
  | .ok _ => pure ()
  | .error err =>
      throwError "normalized leading-dot float did not reparse: {err}"
  let mapType ← `(message_field_type| map<string, int32>)
  match mapType with
  | `(message_field_type| $inner:message_field_type_map) =>
      match inner with
      | `(message_field_type_map| map<$key:ident, $value:ident>) =>
          unless key.getId.eraseMacroScopes == `string &&
              value.getId.eraseMacroScopes == `int32 do
            throwErrorAt inner
              "map field type quotation changed its key or value"
      | _ =>
          throwErrorAt inner
            "map field type did not survive parser-category quotation"
  | _ =>
      throwErrorAt mapType
        "map field type was not classified as message_field_type_map"
  let normalType ← `(message_field_type| string)
  match normalType with
  | `(message_field_type| $x:ident) =>
      unless x.getId.eraseMacroScopes == `string do
        throwErrorAt x "ordinary field type quotation changed its identifier"
  | _ =>
      throwErrorAt normalType
        "ordinary field type was not classified as an identifier"
  let decl ← `(command| enum QuotedSigned { NEGATIVE = -1; ZERO = 0; })
  let rendered := Protobuf.Notation.PrettyPrinter.enumDec.pprint ⟨decl.raw⟩
  unless rendered.contains " = -1;" do
    throwError "signed enum declaration did not survive quotation/pretty-printing"
  let keywordDecl ← `(command| message «match» {
    string «structure» = 1;
  })
  let keywordRendered :=
    Protobuf.Notation.PrettyPrinter.messageDec.pprint ⟨keywordDecl.raw⟩
  if keywordRendered.contains "_@" || keywordRendered.contains "_hyg" then
    throwError "pretty-printed protobuf syntax leaked Lean macro scopes"
  unless keywordRendered.contains "«match»" &&
      keywordRendered.contains "«structure»" do
    throwError "Lean keyword identifiers were not escaped by the protobuf pretty-printer"
  match Parser.runParserCategory (← getEnv) `command keywordRendered with
  | .ok _ => pure ()
  | .error err =>
      throwError "pretty-printed protobuf command did not parse again: {err}"
  let malformed : TSyntax ``messageDec := ⟨Syntax.missing⟩
  match Protobuf.Notation.PrettyPrinter.messageDec.pprintSafe malformed with
  | .error _ => pure ()
  | .ok rendered =>
      throwError
        "safe protobuf pretty-printer accepted malformed syntax as {rendered.quote}"
  let malformedCommand : TSyntax `command := ⟨Syntax.missing⟩
  match
      Protobuf.Notation.PrettyPrinter.command.pprintSafe
        malformedCommand with
  | .error _ => pure ()
  | .ok rendered =>
      throwError
        "safe command pretty-printer accepted missing syntax as {rendered.quote}"
  let badId : TSyntax `ident :=
    ⟨Lean.mkIdent (Name.mkStr1 "bad»")⟩
  let badDecl ← `(command| message $badId:ident { })
  match
      Protobuf.Notation.PrettyPrinter.command.pprintSafe
        (TSyntax.mk badDecl.raw) with
  | .error err =>
      unless err.contains "bad»" do
        throwError
          "unrepresentable identifier produced an unrelated error: {err}"
  | .ok rendered =>
      throwError
        "safe protobuf pretty-printer accepted an unrepresentable identifier as {rendered.quote}"
  let genericKeywordId : TSyntax `ident :=
    ⟨Lean.mkIdent (Name.mkStr1 "match")⟩
  let genericKeywordCommand ←
    `(command| def $genericKeywordId:ident := 1)
  let genericKeywordRendered ←
    match
        Protobuf.Notation.PrettyPrinter.command.pprintSafe
          genericKeywordCommand with
    | .ok rendered => pure rendered
    | .error err =>
        throwError
          "safe generic command printer rejected a representable keyword identifier: {err}"
  unless genericKeywordRendered.contains "«match»" do
    throwError
      "safe generic command printer did not escape a keyword identifier: {genericKeywordRendered}"
  match
      Parser.runParserCategory
        (← getEnv) `command genericKeywordRendered with
  | .ok _ => pure ()
  | .error err =>
      throwError
        "safe generic command output did not parse again: {err}"
  let parenthesizedCommand ←
    `(command|
      def parenthesizedGeneratedTerm :=
        ((String.append "a" (String.append "b" "c"))))
  let parenthesizedRendered ←
    match
        Protobuf.Notation.PrettyPrinter.command.pprintSafe
          parenthesizedCommand with
    | .ok rendered => pure rendered
    | .error err =>
        throwError
          "safe generic command printer rejected a parenthesized generated term: {err}"
  match
      Parser.runParserCategory
        (← getEnv) `command parenthesizedRendered with
  | .ok _ => pure ()
  | .error err =>
      throwError
        "safe parenthesized command output did not parse again: {err}"
  let genericBadCommand ← `(command| def $badId:ident := 1)
  match
      Protobuf.Notation.PrettyPrinter.command.pprintSafe
        genericBadCommand with
  | .error err =>
      unless err.contains "bad»" do
        throwError
          "unrepresentable generic identifier produced an unrelated error: {err}"
  | .ok rendered =>
      throwError
        "safe generic command printer accepted an unrepresentable identifier as {rendered.quote}"
  let anonymousId : TSyntax `ident :=
    ⟨Lean.mkIdent Name.anonymous⟩
  let anonymousCommand ← `(command| def $anonymousId:ident := 1)
  match
      Protobuf.Notation.PrettyPrinter.command.pprintSafe
        anonymousCommand with
  | .error _ => pure ()
  | .ok rendered =>
      throwError
        "safe generic command printer accepted an anonymous identifier as {rendered.quote}"
  let numericId : TSyntax `ident :=
    ⟨Lean.mkIdent (.num (Name.mkStr1 "generated") 1)⟩
  let numericCommand ← `(command| def $numericId:ident := 1)
  match
      Protobuf.Notation.PrettyPrinter.command.pprintSafe
        numericCommand with
  | .error _ => pure ()
  | .ok rendered =>
      throwError
        "safe generic command printer accepted an unrenderable numeric name component as {rendered.quote}"

enum ElaboratedSigned {
  ZERO = 0;
  NEGATIVE = -1;
}

message ExtensionTarget {
}

/-- error: extension fields cannot be required -/
#guard_msgs in
extend ExtensionTarget {
  required int32 value = 100;
}

message DeprecatedExtensionTarget {
}

extend DeprecatedExtensionTarget {
  optional int32 old_value = 100 [deprecated = true];
  repeated int32 old_values = 101 [packed = true, deprecated = true];
  optional int32 current_value = 102;
}

run_meta do
  let env ← getEnv
  let actualNamesByUser :=
    env.constants.toList.foldl
      (init := ({} : NameMap Name))
      fun names (actualName, _) =>
        names.insert (privateToUserName actualName) actualName
  let resolveName (userName : Name) : Name :=
    if env.contains userName then
      userName
    else
      actualNamesByUser.find? userName |>.getD userName
  let target := `DeprecatedExtensionTarget
  let nested (field : String) (number : Nat) :=
    ((target.str "Extension.Accessors").str s!"{field}_{number}")
  let oldValue := nested "old_value" 100
  let oldValues := nested "old_values" 101
  let deprecatedAccessors :=
    #[oldValue.str "get?", oldValue.str "get", oldValue.str "set",
      oldValue.str "has", target.str "get_old_value?",
      target.str "get_old_value", target.str "set_old_value",
      target.str "has_old_value", oldValues.str "get?",
      oldValues.str "set", oldValues.str "has",
      target.str "get_old_values?", target.str "set_old_values",
      target.str "has_old_values"]
  for userName in deprecatedAccessors do
    let actualName := resolveName userName
    unless env.contains actualName do
      throwError "deprecated extension accessor `{userName}` was not generated"
    unless Lean.Linter.isDeprecated env actualName do
      throwError "extension accessor `{userName}` was not marked deprecated"
  let currentValue := nested "current_value" 102
  for userName in
      #[currentValue.str "get?", currentValue.str "get",
        currentValue.str "set", currentValue.str "has",
        target.str "get_current_value?", target.str "get_current_value",
        target.str "set_current_value", target.str "has_current_value"] do
    let actualName := resolveName userName
    unless env.contains actualName do
      throwError "non-deprecated extension accessor `{userName}` was not generated"
    if Lean.Linter.isDeprecated env actualName then
      throwError "non-deprecated extension accessor `{userName}` was marked deprecated"

message DeprecatedExtensionFlatCollision {
  optional int32 get_old = 1;
  optional int32 set_old = 2;
  optional bool has_old = 3;
}

extend DeprecatedExtensionFlatCollision {
  optional int32 old = 100 [deprecated = true];
}

run_meta do
  let env ← getEnv
  let actualNamesByUser :=
    env.constants.toList.foldl
      (init := ({} : NameMap Name))
      fun names (actualName, _) =>
        names.insert (privateToUserName actualName) actualName
  let resolveName (userName : Name) : Name :=
    if env.contains userName then
      userName
    else
      actualNamesByUser.find? userName |>.getD userName
  let target := `DeprecatedExtensionFlatCollision
  let nested := ((target.str "Extension.Accessors").str "old_100")
  for userName in
      #[nested.str "get?", nested.str "get", nested.str "set",
        nested.str "has", target.str "get_old?"] do
    unless Lean.Linter.isDeprecated env (resolveName userName) do
      throwError "extension accessor `{userName}` was not marked deprecated"
  for userName in
      #[target.str "get_old", target.str "set_old", target.str "has_old"] do
    let actualName := resolveName userName
    unless env.contains actualName do
      throwError "collision projection `{userName}` was not generated"
    if Lean.Linter.isDeprecated env actualName then
      throwError "unrelated collision projection `{userName}` was marked deprecated"

/-- info: true -/
#guard_msgs (info) in
#eval
  ElaboratedSigned.«protobuf.internal».fromInt32 (-1) ==
      ElaboratedSigned.NEGATIVE &&
    ElaboratedSigned.«protobuf.internal».toInt32
      ElaboratedSigned.NEGATIVE == (-1 : Int32)

enum ElaboratedRadix {
  ZERO = 0;
  OCTAL = 077;
  HEX = 0x40;
  NEGATIVE_OCTAL = -010;
}

message ElaboratedNumericLiterals {
  optional int32 octal_default = 010 [default = 077];
  optional float octal_float = 011 [default = 077];
  optional float hex_float = 012 [default = 0x10];
  optional float negative_zero_decimal = 013 [default = -0];
  optional float negative_zero_octal = 014 [default = -00];
  optional float negative_zero_hex = 015 [default = -0x0];
  optional double leading_dot = 016 [default = .5];
  optional double negative_inf = 017 [default = -inf];
  optional double negative_nan = 020 [default = -nan];
}

/-- info: true -/
#guard_msgs (info) in
#eval
  ElaboratedRadix.«protobuf.internal».toInt32 ElaboratedRadix.OCTAL ==
      (63 : Int32) &&
    ElaboratedRadix.«protobuf.internal».toInt32 ElaboratedRadix.HEX ==
      (64 : Int32) &&
    ElaboratedRadix.«protobuf.internal».toInt32
      ElaboratedRadix.NEGATIVE_OCTAL == (-8 : Int32)

/-- info: true -/
#guard_msgs (info) in
#eval
  let value : ElaboratedNumericLiterals := default
  ElaboratedNumericLiterals.«Explicit.Default.Accessors».octal_default.get
        value == (63 : Int32) &&
    ElaboratedNumericLiterals.«Explicit.Default.Accessors».octal_float.get
        value == (63 : Float32) &&
    ElaboratedNumericLiterals.«Explicit.Default.Accessors».hex_float.get
        value == (16 : Float32) &&
    Float32.toBits
        (ElaboratedNumericLiterals.«Explicit.Default.Accessors».negative_zero_decimal.get
          value) == 0x80000000 &&
    Float32.toBits
        (ElaboratedNumericLiterals.«Explicit.Default.Accessors».negative_zero_octal.get
          value) == 0x80000000 &&
    Float32.toBits
        (ElaboratedNumericLiterals.«Explicit.Default.Accessors».negative_zero_hex.get
          value) == 0x80000000 &&
    Float.toBits
        (ElaboratedNumericLiterals.«Explicit.Default.Accessors».leading_dot.get
          value) == 0x3fe0000000000000 &&
    Float.toBits
        (ElaboratedNumericLiterals.«Explicit.Default.Accessors».negative_inf.get
          value) == 0xfff0000000000000 &&
    Float.toBits
        (ElaboratedNumericLiterals.«Explicit.Default.Accessors».negative_nan.get
          value) == 0x7ff8000000000000

/-- info: true -/
#guard_msgs (info) in
#eval
  match
      ElaboratedNumericLiterals.«protobuf.internal».toMessage {
        octal_default := some 1
      } with
  | .ok wire =>
      (Encoding.Message.getRecordsOf wire 8).size == 1 &&
        (Encoding.Message.getRecordsOf wire 10).isEmpty
  | .error _ => false

enum EnumHelperNameCollision {
  isKnown = 0;
  isClosed = 1;
  Internal = 2;
}

enum NumericAlias [allow_alias = true] {
  NUMERIC_ALIAS_ZERO = 0;
  NUMERIC_ALIAS_ZERO_ALIAS = 0;
  NUMERIC_ALIAS_ONE = 1;
}

message NumericAliasHolder {
  NumericAlias value = 1;
}

/-- info: true -/
#guard_msgs (info) in
#eval
    NumericAlias.NUMERIC_ALIAS_ZERO ==
      NumericAlias.NUMERIC_ALIAS_ZERO_ALIAS &&
    NumericAlias.«protobuf.internal».isKnown
      NumericAlias.NUMERIC_ALIAS_ZERO_ALIAS &&
    match
        NumericAliasHolder.«protobuf.internal».toMessage {
          value := NumericAlias.NUMERIC_ALIAS_ZERO_ALIAS
        } with
    | .ok msg =>
        msg.records.isEmpty &&
          match NumericAliasHolder.«protobuf.internal».fromMessage msg with
          | .ok decoded =>
              decoded.value ==
                  NumericAlias.NUMERIC_ALIAS_ZERO_ALIAS &&
                decoded.value == NumericAlias.NUMERIC_ALIAS_ZERO
          | .error _ => false
    | .error _ => false

/-- info: true -/
#guard_msgs (info) in
#eval
  EnumHelperNameCollision.«protobuf.internal».isKnown
      EnumHelperNameCollision.isKnown &&
    EnumHelperNameCollision.«protobuf.internal».isKnown
      EnumHelperNameCollision.Internal &&
    !EnumHelperNameCollision.«protobuf.internal».isClosed

message ExplicitAccessorCollision {
  optional int32 foo = 1 [default = 7];
  optional int32 get_foo = 2;
  optional bool has_foo = 3;
}

/-- info: true -/
#guard_msgs (info) in
#eval
  let value : ExplicitAccessorCollision := default
  value.get_foo.isNone &&
    value.has_foo.isNone &&
    ExplicitAccessorCollision.«Explicit.Default.Accessors».foo.get value == 7 &&
    !ExplicitAccessorCollision.«Explicit.Default.Accessors».foo.has value

message ExtensionAccessorCollision {
  optional int32 get_x = 1;
  optional bool has_x = 2;
  optional int32 set_x = 3;
}

extend ExtensionAccessorCollision {
  optional int32 x = 100 [default = 7];
}

/-- error: protobuf extension field number 100 for `ExtensionAccessorCollision` is already declared by `x` -/
#guard_msgs in
extend ExtensionAccessorCollision {
  optional string duplicate_x = 100;
}

/-- error: protobuf extension field number 300 for `ImportedExtensionTagHost` is already declared by `imported_value` -/
#guard_msgs in
extend ImportedExtensionTagHost {
  optional string duplicate_imported = 300;
}

run_meta do
  let marker :=
    `ImportedExtensionTagHost.«Extension.Tags.protobuf».«300.protobuf»
  unless (← getEnv).contains marker do
    throwError "imported extension tag marker was not persisted"

/-- info: true -/
#guard_msgs (info) in
#eval
  let value : ExtensionAccessorCollision := default
  match
      ExtensionAccessorCollision.«Extension.Accessors».x_100.get value,
      ExtensionAccessorCollision.«Extension.Accessors».x_100.set value 9 with
  | .ok defaultValue, .ok updated =>
      match
          ExtensionAccessorCollision.«Extension.Accessors».x_100.get? updated with
      | .ok (some decoded) =>
          defaultValue == 7 &&
            !ExtensionAccessorCollision.«Extension.Accessors».x_100.has value &&
            ExtensionAccessorCollision.«Extension.Accessors».x_100.has updated &&
            decoded == 9
      | _ => false
  | _, _ => false

-- Schema invariants are checked by the notation elaborator, before any
-- runtime encoder/decoder is generated.
/-- error: protobuf field `value` has invalid number 0; field numbers must be in 1..536870911 -/
#guard_msgs in
message InvalidZeroTag {
  int32 value = 0;
}

/-- error: protobuf field number 19000 is in the reserved implementation range 19000..19999 -/
#guard_msgs in
message InvalidReservedTag {
  int32 value = 19000;
}

/-- error: protobuf field number 1 is declared more than once -/
#guard_msgs in
message InvalidDuplicateTag {
  int32 first = 1;
  int32 second = 1;
}

/-- error: protobuf field number 8 is declared more than once -/
#guard_msgs in
message InvalidOctalDuplicateTag {
  int32 first = 010;
  int32 second = 8;
}

/-- error: protobuf option `packed` is only valid for packable scalar or enum fields -/
#guard_msgs in
message InvalidPackedString {
  repeated string value = 1 [packed = true];
}

/-- error: unknown protobuf notation option `pakced` -/
#guard_msgs in
message InvalidUnknownOption {
  int32 value = 1 [pakced = true];
}

/-- error: the first value of an open protobuf enum must have numeric value 0 -/
#guard_msgs in
enum InvalidOpenEnum {
  NOT_ZERO = 1;
}

/-- error: oneof fields cannot declare a default value -/
#guard_msgs in
oneof InvalidOneofDefault {
  int32 value = 1 [default = 7];
}

/-- error: default value 4294967296 is outside the int32 range [-2147483648, 2147483647] -/
#guard_msgs in
message InvalidInt32DefaultOverflow {
  optional int32 value = 1 [default = 4294967296];
}

/-- error: default value -1 is outside the uint32 range [0, 4294967295] -/
#guard_msgs in
message InvalidUint32DefaultNegative {
  optional uint32 value = 1 [default = -1];
}

/-- error: default value for unsigned uint32 field `value` cannot have a negative sign -/
#guard_msgs in
message InvalidUint32DefaultNegativeZero {
  optional uint32 value = 1 [default = -0];
}

/-- error: default value 9223372036854775808 is outside the int64 range [-9223372036854775808, 9223372036854775807] -/
#guard_msgs in
message InvalidInt64DefaultOverflow {
  optional int64 value = 1 [default = 9223372036854775808];
}

/-- error: default value 18446744073709551616 is outside the uint64 range [0, 18446744073709551615] -/
#guard_msgs in
message InvalidUint64DefaultOverflow {
  optional uint64 value = 1 [default = 18446744073709551616];
}

/-- error: default option for integer field `value` expects an integer literal -/
#guard_msgs in
message InvalidScientificIntegerDefault {
  optional int32 value = 1 [default = 1.0];
}

/-- error: invalid base64 bytes default: base64: invalid character '%' -/
#guard_msgs in
message InvalidBytesDefaultEncoding {
  optional bytes value = 1 [default = "%%%"];
}

/-- error: invalid base64 or UTF-8 string default: invalid UTF-8 default string literal -/
#guard_msgs in
message InvalidStringDefaultUtf8 {
  optional string value = 1 [default = "/w=="];
}

message IntegerDefaultBoundaries {
  optional int32 i32_min = 1 [default = -2147483648];
  optional uint32 u32_max = 2 [default = 4294967295];
  optional int64 i64_min = 3 [default = -9223372036854775808];
  optional uint64 u64_max = 4 [default = 18446744073709551615];
}

/-- info: true -/
#guard_msgs (info) in
#eval
  let value : IntegerDefaultBoundaries := default
  IntegerDefaultBoundaries.«Explicit.Default.Accessors».i32_min.get value ==
      (-2147483648 : Int32) &&
    IntegerDefaultBoundaries.«Explicit.Default.Accessors».u32_max.get value ==
      (4294967295 : UInt32) &&
    IntegerDefaultBoundaries.«Explicit.Default.Accessors».i64_min.get value ==
      (-9223372036854775808 : Int64) &&
    IntegerDefaultBoundaries.«Explicit.Default.Accessors».u64_max.get value ==
      (18446744073709551615 : UInt64)

message StaticBinaryDefaults {
  optional bytes binary = 1 [default = "AP8="];
  optional string text = 2 [default = "aGk="];
  optional raw_string unchecked = 3 [default = "/w=="];
}

/-- info: true -/
#guard_msgs (info) in
#eval
  let value : StaticBinaryDefaults := default
  StaticBinaryDefaults.«Explicit.Default.Accessors».binary.get value ==
      (⟨#[0, 255]⟩ : ByteArray) &&
    StaticBinaryDefaults.«Explicit.Default.Accessors».text.get value == "hi" &&
    (StaticBinaryDefaults.«Explicit.Default.Accessors».unchecked.get value).bytes ==
      (⟨#[255]⟩ : ByteArray)
