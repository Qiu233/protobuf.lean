module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Base64
import Protobuf.Utils
public meta import Protobuf.Notation.Basic
public import Protobuf.Notation.Enum
public import Lean
public meta import Protobuf.Notation.Syntax

public meta section

namespace Protobuf.Notation

open Encoding Notation

open Lean Meta Elab Term Command

initialize protoOneOfAttr : TagAttribute ←
  registerTagAttribute `proto_oneof "mark inductive type to be a protobuf oneof sum type"

public def getProtoOneOfs [Monad m] [MonadEnv m] : m NameSet := do
  let env ← getEnv
  return protoOneOfAttr.ext.getState env

public def isProtoOneOf [Monad m] [MonadEnv m] (x : Name) : m Bool := do
  let env ← getEnv
  return protoOneOfAttr.hasTag env x

private def resolveInternalType [Monad m] [MonadQuotation m] : TSyntax `ident → m (TSyntax `ident) := fun stx =>
  match stx with
  | `(string) => ``(String)
  | `(raw_string) => ``(Protobuf.UnvalidatedString)
  | `(bytes) => ``(ByteArray)
  | `(bool) => ``(Bool)
  | `(int32) => ``(Int32)
  | `(uint32) => ``(UInt32)
  | `(int64) => ``(Int64)
  | `(uint64) => ``(UInt64)
  | `(sint32) => ``(Int32)
  | `(sint64) => ``(Int64)

  | `(double) => ``(Float)
  | `(float) => ``(Float32)
  | `(fixed64) => ``(UInt64)
  | `(sfixed64) => ``(Int64)
  | `(fixed32) => ``(UInt32)
  | `(sfixed32) => ``(Int32)
  | x => pure x

inductive Modifier where
  /-- singular scalar fields are encoded as plain scalar type with default value -/
  | default
  /-- all optional -/
  | optional
  | repeated
  | required
deriving Inhabited, BEq

instance : ToString Modifier where
  toString
    | .default => "default"
    | .optional => "optional"
    | .repeated => "repeated"
    | .required => "required"

inductive InternalType where
  | string
  | raw_string
  | bytes
  | bool
  | int32
  | uint32
  | int64
  | uint64
  | sint32
  | sint64

  | double
  | fixed64
  | sfixed64
  | float
  | fixed32
  | sfixed32
deriving Inhabited, BEq

private def InternalType.isMapKeyAllowed : InternalType → Bool
  | .string
  | .raw_string
  | .bool
  | .int32
  | .uint32
  | .int64
  | .uint64
  | .sint32
  | .sint64
  | .fixed32
  | .fixed64
  | .sfixed32
  | .sfixed64 => true
  | .bytes
  | .double
  | .float => false

private def getInternalType? : TSyntax `ident → Option InternalType
  | `(string) => some .string
  | `(raw_string) => some .raw_string
  | `(bool) => some .bool
  | `(bytes) => some .bytes
  | `(int32) => some .int32
  | `(uint32) => some .uint32
  | `(int64) => some .int64
  | `(uint64) => some .uint64
  | `(sint32) => some .sint32
  | `(sint64) => some .sint64

  | `(double) => some .double
  | `(float) => some .float
  | `(fixed64) => some .fixed64
  | `(sfixed64) => some .sfixed64
  | `(fixed32) => some .fixed32
  | `(sfixed32) => some .sfixed32
  | _ => none

/-- (is_scalar, internal_type?, enum_type?, oneof_type?) -/
@[specialize]
private def getProtoTypeMData [Monad m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mutEnums mutOneofs messages : NameSet) : TSyntax `ident → m (Bool × Option InternalType × Option Name × Option Name) := fun x => do
  let x := protectGeneratedTypeName x
  let internal_type? := getInternalType? x
  if let some x := internal_type? then
    if x != InternalType.string && x != InternalType.raw_string && x != InternalType.bytes then
      return (true, internal_type?, none, none)
    else
      return (false, internal_type?, none, none)
  if mutEnums.contains x.getId then
    return (true, none, some x.getId, none)
  if mutOneofs.contains x.getId then
    return (false, none, none, some x.getId)
  if messages.contains x.getId then
    return (false, none, none, none)
  let ns ← try resolveGlobalConst x
    catch _ => throwErrorAt x "Type {x} is not one of mutual declarations but cannot be resolved.\n  Note: if a mutual declaration has qualified name, then it must also be qualified when used in the same mutual block."
      -- return (false, internal_type?, none, none)
  if ns.length > 1 then
    throwErrorAt x "{x} is ambiguous"
  if ← isProtoEnum ns[0]! then
    return (true, internal_type?, some ns[0]!, none)
  else if ← isProtoOneOf ns[0]! then
    return (false, internal_type?, none, some ns[0]!)
  else
    return (false, internal_type?, none, none)

private def InternalType.builder [Monad m] [MonadQuotation m] : InternalType → m Ident
  | .string =>  ``(Encoding.ProtoVal.ofString)
  | .raw_string => ``(Encoding.ProtoVal.ofUnvalidatedString)
  | .bytes =>   ``(Encoding.ProtoVal.ofBytes)
  | .bool =>    ``(Encoding.ProtoVal.ofBool)
  | .int32 =>   ``(Encoding.ProtoVal.ofVarint_int32)
  | .uint32 =>  ``(Encoding.ProtoVal.ofVarint_uint32)
  | .int64 =>   ``(Encoding.ProtoVal.ofVarint_int64)
  | .uint64 =>  ``(Encoding.ProtoVal.ofVarint_uint64)
  | .sint32 =>  ``(Encoding.ProtoVal.ofVarint_sint32)
  | .sint64 =>  ``(Encoding.ProtoVal.ofVarint_sint64)

  | .double =>    ``(Encoding.ProtoVal.ofI64_double)
  | .fixed64 =>   ``(Encoding.ProtoVal.ofI64_fixed64)
  | .sfixed64 =>  ``(Encoding.ProtoVal.ofI64_sfixed64)
  | .float =>     ``(Encoding.ProtoVal.ofI32_float)
  | .fixed32 =>   ``(Encoding.ProtoVal.ofI32_fixed32)
  | .sfixed32 =>  ``(Encoding.ProtoVal.ofI32_sfixed32)

private def InternalType.decoder? [Monad m] [MonadQuotation m] : InternalType → m Ident
  | .string =>  ``(Encoding.Message.getString?)
  | .raw_string => ``(Encoding.Message.getUnvalidatedString?)
  | .bytes =>   ``(Encoding.Message.getBytes?)
  | .bool =>    ``(Encoding.Message.getBool?)
  | .int32 =>   ``(Encoding.Message.getVarint_int32?)
  | .uint32 =>  ``(Encoding.Message.getVarint_uint32?)
  | .int64 =>   ``(Encoding.Message.getVarint_int64?)
  | .uint64 =>  ``(Encoding.Message.getVarint_uint64?)
  | .sint32 =>  ``(Encoding.Message.getVarint_sint32?)
  | .sint64 =>  ``(Encoding.Message.getVarint_sint64?)

  | .double =>    ``(Encoding.Message.getI64_double?)
  | .fixed64 =>   ``(Encoding.Message.getI64_fixed64?)
  | .sfixed64 =>  ``(Encoding.Message.getI64_sfixed64?)
  | .float =>     ``(Encoding.Message.getI32_float?)
  | .fixed32 =>   ``(Encoding.Message.getI32_fixed32?)
  | .sfixed32 =>  ``(Encoding.Message.getI32_sfixed32?)

private def InternalType.decoder_rep_packed
    [Monad m] [MonadQuotation m] [MonadError m] [MonadRef m]
    [AddMessageContext m] : InternalType → m Ident
  | .string
  | .raw_string
  | .bytes =>
      throwError
        "{decl_name%}: internal error: a non-packable string or bytes type reached the packed decoder generator"
  | .bool =>    ``(Encoding.Message.getPackedBool)
  | .int32 =>   ``(Encoding.Message.getPackedVarint_int32)
  | .uint32 =>  ``(Encoding.Message.getPackedVarint_uint32)
  | .int64 =>   ``(Encoding.Message.getPackedVarint_int64)
  | .uint64 =>  ``(Encoding.Message.getPackedVarint_uint64)
  | .sint32 =>  ``(Encoding.Message.getPackedVarint_sint32)
  | .sint64 =>  ``(Encoding.Message.getPackedVarint_sint64)

  | .double =>    ``(Encoding.Message.getPackedI64_double)
  | .fixed64 =>   ``(Encoding.Message.getPackedI64_fixed64)
  | .sfixed64 =>  ``(Encoding.Message.getPackedI64_sfixed64)
  | .float =>     ``(Encoding.Message.getPackedI32_float)
  | .fixed32 =>   ``(Encoding.Message.getPackedI32_fixed32)
  | .sfixed32 =>  ``(Encoding.Message.getPackedI32_sfixed32)

private def InternalType.decoder_rep [Monad m] [MonadQuotation m] : InternalType → m Ident
  | .string =>  ``(Encoding.Message.getExpandedString)
  | .raw_string => ``(Encoding.Message.getExpandedUnvalidatedString)
  | .bytes =>   ``(Encoding.Message.getExpandedBytes)
  | .bool =>    ``(Encoding.Message.getRepeatedBool)
  | .int32 =>   ``(Encoding.Message.getRepeatedVarint_int32)
  | .uint32 =>  ``(Encoding.Message.getRepeatedVarint_uint32)
  | .int64 =>   ``(Encoding.Message.getRepeatedVarint_int64)
  | .uint64 =>  ``(Encoding.Message.getRepeatedVarint_uint64)
  | .sint32 =>  ``(Encoding.Message.getRepeatedVarint_sint32)
  | .sint64 =>  ``(Encoding.Message.getRepeatedVarint_sint64)

  | .double =>    ``(Encoding.Message.getRepeatedI64_double)
  | .fixed64 =>   ``(Encoding.Message.getRepeatedI64_fixed64)
  | .sfixed64 =>  ``(Encoding.Message.getRepeatedI64_sfixed64)
  | .float =>     ``(Encoding.Message.getRepeatedI32_float)
  | .fixed32 =>   ``(Encoding.Message.getRepeatedI32_fixed32)
  | .sfixed32 =>  ``(Encoding.Message.getRepeatedI32_sfixed32)

inductive LeanShape where
  | strict
  | option
  | array
  | map
deriving Inhabited, BEq

structure MapFieldMData where
  /--
  `Std.HashMap` bundles a dependent well-formedness proof and therefore cannot
  occur around a value type from the same recursive protobuf SCC.  Such map
  fields use `Std.HashMap.Raw`, whose representation is designed for nested
  inductive types.  Non-recursive maps keep the bundled public type.
  -/
  uses_raw_map : Bool
  key_proto_type : Ident
  value_proto_type : Ident
  key_lean_type : Ident
  value_lean_type : Ident
  key_builder : Ident
  value_builder : Ident
  key_decoder? : Ident
  value_decoder? : Ident
  key_default : Term
  value_default : Term
  value_enum_type? : Option Name
  /-- Whether decoding the map value enters another embedded message. -/
  value_is_message : Bool
deriving Inhabited

structure ProtoFieldMData where
  mod : Modifier
  proto_type : Ident
  lean_type_inner : Ident
  lean_type : Term
  field_name : Ident
  field_proj : Ident
  field_num : TSyntax `num
  options : Options
  lean_shape : LeanShape
  map_info? : Option MapFieldMData
  is_scalar : Bool
  internal_type? : Option InternalType
  /-- the `«Default.Value»` of the type -/
  default_lean_value : Term
  /-- the default value term in constructor so that use-site `{...}` won't need to initialize everything -/
  default_ctor_value : Term
  /--
  An explicit schema default for an explicit-presence scalar or enum field.

  Storage remains `Option` so presence is not manufactured.  Static accessors
  use this term to expose protobuf's value-without-presence semantics.
  -/
  explicit_default? : Option Term
  /-- Value returned by a schema-level getter when explicit presence is absent. -/
  accessor_default : Term
  /-- the code to test whether this fields should not be serialized to the wire -/
  test_unset : Term
  enum_type? : Option Name
  oneof_type? : Option Name
  builder? : Option Ident
  toMessage? : Option Ident
  fromMessage? : Option Ident
  fromMessage?? : Option Ident
  decoder?? : Option Ident
  decoder_rep? : Option Ident
  decoder_rep_packed? : Option Ident
deriving Inhabited

/--
The protobuf field namespace contributed by one alternative of a generated
oneof.

This is elaborator metadata, not a runtime descriptor.  It is persisted in the
environment alongside the oneof declaration so that a message in another
module can validate its ordinary fields against the alternatives of an
embedded oneof without reflection.
-/
structure OneofAlternativeMData where
  fieldName : Name
  fieldNumber : Nat
deriving Inhabited, Repr, BEq

/-- A concrete wire tag occupied by a generated protobuf message. -/
structure MessageFieldTagMData where
  fieldName : Name
  fieldNumber : Nat
deriving Inhabited, Repr, BEq

/--
Alternatives of oneofs declared in the same `proto_mutual` block.  Those
declarations do not exist in the environment while message metadata is being
computed, so the mutual elaborator supplies this pre-scanned map.
-/
abbrev LocalOneofAlternatives := NameMap (Array OneofAlternativeMData)

initialize oneofAlternativesExt :
    MapDeclarationExtension (Array OneofAlternativeMData) ←
  mkMapDeclarationExtension

/--
The statically known wire fields of a generated protobuf message.

Like `oneofAlternativesExt`, this is declaration metadata persisted through
`.olean` files.  It is consumed by the extension elaborator to reject an
extension whose tag is already occupied by an ordinary field or by an
alternative of an embedded oneof.  No runtime descriptor or reflection data is
generated.
-/
initialize messageFieldTagsExt :
    MapDeclarationExtension (Array MessageFieldTagMData) ←
  mkMapDeclarationExtension

/-- Extract the static alternative namespace from parsed oneof fields. -/
def oneofAlternativesOfFields
    (fieldNames : Array Ident) (fieldNumbers : Array (TSyntax `num)) :
    CommandElabM (Array OneofAlternativeMData) := do
  let mut alternatives := #[]
  for fieldName in fieldNames, fieldNumber in fieldNumbers do
    let some value := protobufIntLiteralValue? fieldNumber
      | throwErrorAt fieldNumber "invalid protobuf field number literal"
    let safeFieldName := protectGeneratedMemberName fieldName
    alternatives := alternatives.push {
      fieldName := safeFieldName.getId.eraseMacroScopes
      fieldNumber := value
    }
  return alternatives

/-- Extract a oneof name and alternatives before elaborating a mutual block. -/
def oneofAlternativesOfSyntax
    (stx : Syntax) : CommandElabM (Ident × Array OneofAlternativeMData) := do
  let `(oneofDec|
      oneof $rawName {
        $[$[$mod]? $t' $fieldNames = $fieldNumbers $[$optionsStx]? ;]*
      }) := stx
    | throwUnsupportedSyntax
  let name := protectGeneratedTypeName rawName
  let alternatives ← oneofAlternativesOfFields fieldNames fieldNumbers
  return (name, alternatives)

/--
Persist a successfully elaborated oneof's field namespace.  Registration is
performed only after its generated declaration block has elaborated, so a
failed schema cannot leave metadata in the environment.
-/
def registerOneofAlternatives
    (oneofName : Ident) (alternatives : Array OneofAlternativeMData) :
    CommandElabM Unit := do
  let names ← resolveGlobalConst oneofName
  unless names.length == 1 do
    throwErrorAt oneofName
      "cannot uniquely resolve elaborated protobuf oneof `{oneofName}`"
  let declName := names[0]!
  modifyEnv fun env =>
    oneofAlternativesExt.insert env declName alternatives

/--
Persist a successfully elaborated message's statically known wire fields.

Registration is deliberately separate from metadata computation: callers
invoke it only after the generated declaration block has elaborated, so a
failed schema cannot leave stale field tags in the environment.
-/
def registerMessageFieldTags
    (messageName : Ident) (fields : Array MessageFieldTagMData) :
    CommandElabM Unit := do
  let names ← resolveGlobalConst messageName
  unless names.length == 1 do
    throwErrorAt messageName
      "cannot uniquely resolve elaborated protobuf message `{messageName}`"
  let declName := names[0]!
  modifyEnv fun env =>
    messageFieldTagsExt.insert env declName fields

/--
Validate the single protobuf field namespace of a message.

The message's ordinary fields and every alternative of every embedded oneof
share names and tag numbers in the protobuf descriptor model.  The Lean
representation stores an embedded oneof as a dummy tag-0 structure field, so
this extra compile-time pass restores the schema invariant without generating
or consulting a runtime descriptor.
-/
def validateEmbeddedOneofAlternatives
    (localOneofs : LocalOneofAlternatives)
    (fields : Array ProtoFieldMData) :
    CommandElabM (Array MessageFieldTagMData) := do
  let mut fieldNames : Array Name :=
    fields.map fun field => field.field_name.getId.eraseMacroScopes
  let mut fieldTags : Array MessageFieldTagMData :=
    fields.filterMap fun field =>
      if field.oneof_type?.isSome then
        none
      else
        some {
          fieldName := field.field_name.getId.eraseMacroScopes
          fieldNumber := field.field_num.getNat
        }
  let mut fieldNumbers : Array Nat :=
    fieldTags.map (·.fieldNumber)
  for field in fields do
    let some oneofName := field.oneof_type? | continue
    let alternatives? ←
      match localOneofs.find? oneofName with
      | some alternatives => pure (some alternatives)
      | none => do
          let env ← getEnv
          pure (oneofAlternativesExt.find? env oneofName)
    let some alternatives := alternatives?
      | throwErrorAt field.proto_type
          "static field metadata is unavailable for protobuf oneof `{oneofName}`; rebuild the module that declares it"
    for alternative in alternatives do
      if fieldNames.contains alternative.fieldName then
        throwErrorAt field.field_name
          "protobuf field name `{alternative.fieldName}` from embedded oneof `{oneofName}` is declared more than once"
      fieldNames := fieldNames.push alternative.fieldName
      if fieldNumbers.contains alternative.fieldNumber then
        throwErrorAt field.field_name
          "protobuf field number {alternative.fieldNumber} from embedded oneof `{oneofName}` is declared more than once"
      fieldNumbers := fieldNumbers.push alternative.fieldNumber
      fieldTags := fieldTags.push {
        fieldName := alternative.fieldName
        fieldNumber := alternative.fieldNumber
      }
  return fieldTags

def validateFieldNumber
    [Monad m] [MonadError m] [MonadRef m] [AddMessageContext m]
    (fieldName : Ident) (fieldNum : TSyntax `num) : m Unit := do
  let some n := protobufIntLiteralValue? fieldNum
    | throwErrorAt fieldNum "invalid protobuf field number literal"
  if n == 0 || n > (1 <<< 29) - 1 then
    throwErrorAt fieldNum
      "protobuf field `{fieldName.getId.eraseMacroScopes}` has invalid number {n}; field numbers must be in 1..536870911"
  if 19000 ≤ n && n ≤ 19999 then
    throwErrorAt fieldNum
      "protobuf field number {n} is in the reserved implementation range 19000..19999"

private def optionsValueToNumericTerm [Monad m] [MonadQuotation m] [MonadError m] [MonadRef m] [AddMessageContext m]
    (field_name : Ident) (v : TSyntax `options_value) : m Term := do
  match v with
  | `(options_value| $x:scientific) =>
      let some canonical := canonicalProtobufFloatLiteral? x
        | throwErrorAt x "invalid protobuf floating-point literal"
      `($canonical:scientific)
  | `(options_value| -$x:scientific) =>
      let some canonical := canonicalProtobufFloatLiteral? x
        | throwErrorAt x "invalid protobuf floating-point literal"
      `(-$canonical:scientific)
  | `(options_value| +$_x:scientific) =>
      throwErrorAt v
        "protobuf numeric literals do not allow a leading plus sign"
  | `(options_value| $x:num) =>
      let some canonical := canonicalProtobufIntLiteral? x
        | throwErrorAt x "invalid protobuf integer literal"
      `($canonical:num)
  | `(options_value| -$x:num) =>
      let some canonical := canonicalProtobufIntLiteral? x
        | throwErrorAt x "invalid protobuf integer literal"
      `(-$canonical:num)
  | `(options_value| +$_x:num) =>
      throwErrorAt v
        "protobuf numeric literals do not allow a leading plus sign"
  | _ => throwErrorAt field_name "default option expects a numeric literal"

private def optionsValueToInteger
    [Monad m] [MonadError m] [MonadRef m] [AddMessageContext m]
    (fieldName : Ident) (v : TSyntax `options_value) : m (Int × Bool) := do
  match v with
  | `(options_value| $x:num) =>
      let some magnitude := protobufIntLiteralValue? x
        | throwErrorAt x "invalid protobuf integer literal"
      return (Int.ofNat magnitude, false)
  | `(options_value| -$x:num) =>
      let some magnitude := protobufIntLiteralValue? x
        | throwErrorAt x "invalid protobuf integer literal"
      return (-Int.ofNat magnitude, true)
  | `(options_value| +$_x:num) =>
      throwErrorAt v
        "protobuf numeric literals do not allow a leading plus sign"
  | _ =>
      throwErrorAt v
        "default option for integer field `{fieldName.getId.eraseMacroScopes}` expects an integer literal"

private def integerDefaultBounds
    (internalType : InternalType) : Option (Int × Int × String) :=
  let signed (bits : Nat) (name : String) :=
    let half := Int.ofNat (2 ^ (bits - 1))
    (-half, half - 1, name)
  let unsigned (bits : Nat) (name : String) :=
    (0, Int.ofNat (2 ^ bits) - 1, name)
  match internalType with
  | .int32 => some (signed 32 "int32")
  | .sint32 => some (signed 32 "sint32")
  | .sfixed32 => some (signed 32 "sfixed32")
  | .uint32 => some (unsigned 32 "uint32")
  | .fixed32 => some (unsigned 32 "fixed32")
  | .int64 => some (signed 64 "int64")
  | .sint64 => some (signed 64 "sint64")
  | .sfixed64 => some (signed 64 "sfixed64")
  | .uint64 => some (unsigned 64 "uint64")
  | .fixed64 => some (unsigned 64 "fixed64")
  | _ => none

private def optionsValueToBoundedIntegerTerm
    [Monad m] [MonadQuotation m] [MonadError m] [MonadRef m]
    [AddMessageContext m]
    (fieldName : Ident) (internalType : InternalType)
    (v : TSyntax `options_value) : m Term := do
  let (value, explicitlyNegative) ← optionsValueToInteger fieldName v
  let some (minValue, maxValue, typeName) :=
      integerDefaultBounds internalType
    | throwErrorAt fieldName
        "internal error: requested integer bounds for a non-integer field"
  if explicitlyNegative && value == 0 && minValue == 0 then
    throwErrorAt v
      "default value for unsigned {typeName} field `{fieldName.getId.eraseMacroScopes}` cannot have a negative sign"
  if value < minValue || value > maxValue then
    throwErrorAt v
      "default value {value} is outside the {typeName} range [{minValue}, {maxValue}]"
  optionsValueToNumericTerm fieldName v

private def byteArrayLiteral
    [Monad m] [MonadQuotation m] (bytes : ByteArray) : m Term := do
  let elements : Array Term :=
    bytes.data.map fun byte =>
      ⟨Syntax.mkNumLit byte.toNat.repr⟩
  `(ByteArray.mk #[$elements,*])

private def optionsValueToTerm [Monad m] [MonadQuotation m] [MonadError m] [MonadRef m] [AddMessageContext m]
    (field_name : Ident) (_ : LeanShape) (_ : Ident) (internal_type : InternalType) (v : TSyntax `options_value) : m Term := do
  match internal_type with
  | .bool =>
      match v with
      | `(options_value| true) => `(true)
      | `(options_value| false) => `(false)
      | _ => throwErrorAt field_name "default option expects a boolean literal"
  | .string =>
      match v with
      | `(options_value| $s:str) => do
          match Protobuf.Base64.decodeBase64String s.getString with
          | .ok value => pure (quote value)
          | .error error =>
              throwErrorAt s
                "invalid base64 or UTF-8 string default: {error}"
      | _ => throwErrorAt field_name "default option expects a string literal"
  | .raw_string =>
      match v with
      | `(options_value| $s:str) => do
          let bytes ←
            match Protobuf.Base64.decode s.getString with
            | .ok bytes => pure bytes
            | .error error =>
                throwErrorAt s "invalid base64 string default: {error}"
          let literal ← byteArrayLiteral bytes
          let ofBytes := mkIdent ``Protobuf.UnvalidatedString.ofBytes
          `($ofBytes:ident $literal)
      | _ => throwErrorAt field_name "default option expects a string literal"
  | .bytes =>
      match v with
      | `(options_value| $s:str) => do
          match Protobuf.Base64.decode s.getString with
          | .ok bytes => byteArrayLiteral bytes
          | .error error =>
              throwErrorAt s "invalid base64 bytes default: {error}"
      | _ => throwErrorAt field_name "default option expects a string literal"
  | .double | .float =>
      match v with
      | `(options_value| -inf) =>
          match internal_type with
          | .double => `(Float.ofBits 0xfff0000000000000)
          | .float => `(Float32.ofBits 0xff800000)
          | _ => unreachable!
      | `(options_value| -nan) =>
          match internal_type with
          | .double => `(Float.ofBits 0x7ff8000000000000)
          | .float => `(Float32.ofBits 0x7fc00000)
          | _ => unreachable!
      | `(options_value| $x:ident) =>
          let special := x.getId.eraseMacroScopes
          match internal_type, special with
          | .double, `protobuf_inf | .double, `inf =>
              `(Float.ofBits 0x7ff0000000000000)
          | .double, `protobuf_neg_inf =>
              `(Float.ofBits 0xfff0000000000000)
          | .double, `protobuf_nan | .double, `nan =>
              `(Float.ofBits 0x7ff8000000000000)
          | .float, `protobuf_inf | .float, `inf =>
              `(Float32.ofBits 0x7f800000)
          | .float, `protobuf_neg_inf =>
              `(Float32.ofBits 0xff800000)
          | .float, `protobuf_nan | .float, `nan =>
              `(Float32.ofBits 0x7fc00000)
          | _, _ =>
              throwErrorAt x "unsupported floating-point default value '{special}'"
      | _ => optionsValueToNumericTerm field_name v
  | .int32
  | .uint32
  | .int64
  | .uint64
  | .sint32
  | .sint64
  | .fixed64
  | .sfixed64
  | .fixed32
  | .sfixed32 =>
      optionsValueToBoundedIntegerTerm field_name internal_type v

private def defaultOverride? [Monad m] [MonadQuotation m] [MonadError m] [MonadRef m] [AddMessageContext m]
    (field_name : Ident) (lean_shape : LeanShape) (proto_type : Ident) (internal_type? : Option InternalType) (enum_type? : Option Name)
    (options : Options) : m (Option Term) := do
  let some v := options.default? | return none
  if let some internal_type := internal_type? then
    some <$> optionsValueToTerm field_name lean_shape proto_type internal_type v
  else if enum_type?.isSome then
    match v with
    | `(options_value| $x:ident) =>
        let term :=
          mkIdentFrom proto_type
            (proto_type.getId.append x.getId.eraseMacroScopes)
        return some term
    | _ => throwErrorAt field_name "default option expects an enum value identifier"
  else
    throwErrorAt field_name "default option is only supported for scalar or enum fields"

def computeMData.map [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mutEnums mutOneofs messages : NameSet) (_name : Ident)
    (key_proto_type : Ident) (value_proto_type : Ident) (mod? : Modifier)
    (_proto_type : TSyntax `Protobuf.Notation.message_field_type)
    (field_name : Ident)
    (field_proj : Ident)
    (field_num : TSyntax `num)
    (options : Options) : m ProtoFieldMData := do
  let key_proto_type := protectGeneratedTypeName key_proto_type
  let value_proto_type := protectGeneratedTypeName value_proto_type
  if !(mod? matches .default) then
    throwErrorAt field_name "map fields cannot have cardinality modifiers"
  let key_lean_type ← resolveInternalType key_proto_type
  let value_lean_type ← resolveInternalType value_proto_type
  let (_, key_internal_type?, _, key_oneof_type?) ← getProtoTypeMData mutEnums mutOneofs messages key_proto_type
  if key_oneof_type?.isSome then
    throwErrorAt key_proto_type "map key type cannot be a oneof"
  let some key_internal_type := key_internal_type?
    | throwErrorAt key_proto_type "map key type must be a scalar type"
  if !InternalType.isMapKeyAllowed key_internal_type then
    throwErrorAt key_proto_type "map key type must be an integral type, bool, or string"
  let (value_is_scalar, value_internal_type?, value_enum_type?, value_oneof_type?) ←
    getProtoTypeMData mutEnums mutOneofs messages value_proto_type
  if value_oneof_type?.isSome then
    throwErrorAt value_proto_type "map value type cannot be a oneof"
  let uses_raw_map := messages.contains value_proto_type.getId
  let hashMapIdent :=
    if uses_raw_map then mkIdent `Std.HashMap.Raw else mkIdent `Std.HashMap
  let key_builder ← InternalType.builder key_internal_type
  let key_decoder? ← InternalType.decoder? key_internal_type
  let value_builder ←
    if let some value_internal_type := value_internal_type? then
      InternalType.builder value_internal_type
    else
      pure (helperIdent value_proto_type "builder")
  let value_decoder? ←
    if let some value_internal_type := value_internal_type? then
      InternalType.decoder? value_internal_type
    else
      pure (helperIdent value_proto_type "decoder?")
  let key_default : Term ← match key_internal_type with
    | .bool => `(false)
    | .string => `("")
    | .raw_string => `(Protobuf.UnvalidatedString.empty)
    | .bytes => `({})
    | _ => `(0)
  let value_default : Term ← match value_internal_type? with
    | some itype =>
      match itype with
      | .bool => `(false)
      | .string => `("")
      | .raw_string => `(Protobuf.UnvalidatedString.empty)
      | .bytes => `({})
      | _ => `(0)
    | none =>
      if value_enum_type?.isSome || !value_is_scalar then
        pure (helperIdent value_proto_type "Default.Value")
      else
        throwErrorAt value_proto_type "map value type must be scalar, enum, or message"
  let map_info := {
    uses_raw_map,
    key_proto_type,
    value_proto_type,
    key_lean_type,
    value_lean_type,
    key_builder,
    value_builder,
    key_decoder?,
    value_decoder?,
    key_default,
    value_default,
    value_enum_type?,
    value_is_message :=
      value_internal_type?.isNone && value_enum_type?.isNone,
  }
  let lean_type ←
    if uses_raw_map then
      `(Std.HashMap.Raw $key_lean_type $value_lean_type)
    else
      `(Std.HashMap $key_lean_type $value_lean_type)
  let default_map := (← `({}))
  let map_is_empty ←
    if uses_raw_map then
      ``(Std.HashMap.Raw.isEmpty)
    else
      ``(Std.HashMap.isEmpty)
  return {
    mod := .default,
    proto_type := hashMapIdent,
    lean_type_inner := hashMapIdent,
    lean_type,
    field_name,
    field_proj,
    field_num,
    options,
    lean_shape := .map,
    map_info? := some map_info,
    is_scalar := false,
    internal_type? := none,
    default_lean_value := default_map,
    default_ctor_value := default_map,
    explicit_default? := none,
    accessor_default := default_map,
    test_unset := map_is_empty,
    enum_type? := none,
    oneof_type? := none,
    builder? := none,
    toMessage? := none,
    decoder?? := none,
    fromMessage? := none,
    fromMessage?? := none,
    decoder_rep_packed? := none,
    decoder_rep? := none,
    : ProtoFieldMData
  }

def computeMData.ordinary.computeShape [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mod? : Modifier) (internal_type? : Option InternalType) (enum_type? : Option Name) (lean_type_inner : Ident) : m (TSyntax `term × LeanShape) := do
  match mod? with
    | .default =>
      if internal_type?.isSome || enum_type?.isSome then
        pure (← `($lean_type_inner), LeanShape.strict)
      else
        pure (← `(Option $lean_type_inner), LeanShape.option)
    | .optional | .required =>
      pure (← `(Option $lean_type_inner), LeanShape.option)
    | .repeated => pure (← `(Array $lean_type_inner), LeanShape.array)

def computeMData.ordinary.computeCtorValue [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (name : Ident) (internal_type? : Option InternalType) (lean_shape : LeanShape) (enum_type? : Option Name) (proto_type : Ident) : m Term := do
  match lean_shape with
    | .strict =>
      if let some itype := internal_type? then
        match itype with
        | .bool => `(false)
        | .string => `("")
        | .raw_string => `(Protobuf.UnvalidatedString.empty)
        | .bytes => `({})
        | _ => `(0)
      else if enum_type?.isSome then
        pure (helperIdent proto_type "Default.Value")
      else throwErrorAt name "{decl_name%}: internal error: strict non-scalar type"
    | .option => `(Option.none) -- oneofs always go here
    | .array => `(#[])
    | .map => unreachable!

def computeMData.ordinary.computeTestUnset [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (name : Ident) (internal_type? : Option InternalType) (lean_shape : LeanShape) (enum_type? : Option Name) (proto_type : Ident) : m Term := do
  match lean_shape with
    | .strict =>
      if let some itype := internal_type? then
        match itype with
        | .bool => `((· == false))
        | .string => `(String.isEmpty)
        | .raw_string => `(Protobuf.UnvalidatedString.isEmpty)
        | .bytes => `(ByteArray.isEmpty)
        -- IEEE -0.0 compares numerically equal to +0.0, but protobuf preserves
        -- its sign bit and serializes it as a non-default value.
        | .double => `((fun x => Float.toBits x == 0))
        | .float => `((fun x => Float32.toBits x == 0))
        | _ => `((· == 0))
      else if enum_type?.isSome then
        let x := helperIdent proto_type "Default.Value"
        `((· == $x)) -- TODO: maybe make `Enum.«Default.Value»` a `@[match_pattern]`?
      else throwErrorAt name "{decl_name%}: internal error: strict non-scalar type"
    | .option => `(Option.isNone) -- oneofs always go here
    | .array => `(Array.isEmpty)
    | .map => unreachable!

def computeMData.ordinary [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mutEnums mutOneofs messages : NameSet) (name : Ident)
    (mod? : Modifier)
    (proto_type : Ident)
    (field_name : Ident)
    (field_proj : Ident)
    (field_num : TSyntax `num)
    (options : Options) : m ProtoFieldMData := do
  let proto_type := protectGeneratedTypeName proto_type
  let lean_type_inner ← resolveInternalType proto_type
  let (is_scalar, internal_type?, enum_type?, oneof_type?) ← getProtoTypeMData mutEnums mutOneofs messages proto_type
  if oneof_type?.isSome && !(mod? matches .default) then
    throwErrorAt name "oneof field cannot have cardinality modifier: {oneof_type?.get!}"
  let (lean_type, lean_shape) ← computeMData.ordinary.computeShape mod? internal_type? enum_type? lean_type_inner
  let builder? ← internal_type?.mapM InternalType.builder
  let builder? :=
    if oneof_type?.isNone then
      some (builder?.getD (helperIdent proto_type "builder"))
    else
      none
  let toMessage? :=
    if is_scalar then none else some (helperIdent proto_type "toMessage")
  let fromMessage? :=
    if is_scalar then none else some (helperIdent proto_type "fromMessage")
  let fromMessage?? :=
    if oneof_type?.isSome then
      some (helperIdent proto_type "fromMessage?")
    else
      none
  let decoder?? ← internal_type?.mapM InternalType.decoder?
  let decoder?? :=
    if oneof_type?.isNone then
      some (decoder??.getD (helperIdent proto_type "decoder?"))
    else
      none
  let decoder_rep_packed? ← match internal_type? with
    | some .string => pure none
    | some .raw_string => pure none
    | some .bytes => pure none
    | some itype => some <$> InternalType.decoder_rep_packed itype
    | none => pure none
  let decoder_rep_packed? :=
    if is_scalar then
      decoder_rep_packed? <|> some (helperIdent proto_type "decoder_rep_packed")
    else none
  let decoder_rep? ← internal_type?.mapM InternalType.decoder_rep
  let decoder_rep? :=
    if oneof_type?.isSome then
      none
    else
      some <| decoder_rep?.getD (helperIdent proto_type "decoder_rep")
  let default_override? ← defaultOverride? field_name lean_shape proto_type internal_type? enum_type? options
  if default_override?.isSome && mod? == Modifier.repeated then
    throwErrorAt field_name "default option is not allowed for repeated fields"
  let default_lean_value_base ← match lean_shape with
    | .strict =>
      if internal_type?.isSome then `(Inhabited.default)
      else pure (helperIdent proto_type "Default.Value")
    | .option => `(Option.none) -- oneofs always go here
    | .array => `(#[])
    | .map => unreachable!
  let default_ctor_value_base ← computeMData.ordinary.computeCtorValue name internal_type? lean_shape enum_type? proto_type
  let test_unset_base ← computeMData.ordinary.computeTestUnset name internal_type? lean_shape enum_type? proto_type
  let (default_lean_value, default_ctor_value, test_unset) ← do
    match default_override? with
    | some default_term =>
        match lean_shape with
        | .strict =>
          let test_unset_override ← `((· == $default_term))
          pure (default_term, default_term, test_unset_override)
        | .option =>
          -- Explicit-presence fields must start absent.  A protobuf default affects
          -- the value returned by a field accessor, not whether the field is present.
          -- Keep the storage-level `Option` empty; a generated accessor can apply
          -- `default_term` without manufacturing presence.
          pure (default_lean_value_base, default_ctor_value_base, test_unset_base)
        | _ =>
          pure (default_lean_value_base, default_ctor_value_base, test_unset_base)
    | none =>
        pure (default_lean_value_base, default_ctor_value_base, test_unset_base)
  let accessor_default ←
    default_override?.getDM `((Inhabited.default : $lean_type_inner))
  return {
    mod := mod?,
    proto_type,
    lean_type_inner,
    lean_type,
    field_name,
    field_proj,
    field_num,
    options,
    lean_shape,
    map_info? := none,
    default_lean_value,
    default_ctor_value,
    explicit_default? := default_override?,
    accessor_default,
    test_unset,
    is_scalar,
    internal_type?,
    enum_type?,
    oneof_type?,
    builder?,
    toMessage?,
    decoder??,
    fromMessage?,
    fromMessage??,
    decoder_rep_packed?,
    decoder_rep?,
    : ProtoFieldMData
  }

def computeMData [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mutEnums mutOneofs messages : NameSet) (name : Ident)
    (mod : Array (Option (TSyntax `Protobuf.Notation.message_entry_modifier)))
    (t' : Array (TSyntax `Protobuf.Notation.message_field_type)) (n : Array Ident) (fidx : Array (TSyntax `num)) (optionsStx : Array (Option (TSyntax `Protobuf.Notation.options))) : m (Array ProtoFieldMData) := do
  let ms ← mod.mapM fun mod? => do
    let some mod := mod? | return Modifier.default
    match mod with
    | `(message_entry_modifier| optional) => return Modifier.optional
    | `(message_entry_modifier| repeated) => return Modifier.repeated
    | `(message_entry_modifier| required) => return Modifier.required
    | _ => unreachable!
  let dots ← n.mapM fun (x : Ident) => return mkIdentFrom x (name.getId.append x.getId)
  let options := optionsStx.map Options.parseD
  for option in options do
    option.validate
      #[`packed, `deprecated, `wired_as_group, `default, `retention, `targets]
  let mut out := #[]
  for mod? in ms, proto_type in t', field_name in n, field_proj in dots, field_num in fidx, options in options do
    let some field_num := canonicalProtobufIntLiteral? field_num
      | throwErrorAt field_num "invalid protobuf field number literal"
    match proto_type with
    | `(message_field_type| $s:message_field_type_map) => do
      let `(message_field_type_map| map<$key_proto_type:ident, $value_proto_type:ident>) := s | throwUnsupportedSyntax
      let r ← computeMData.map mutEnums mutOneofs messages name key_proto_type value_proto_type mod? proto_type field_name field_proj field_num options
      out := out.push r
    | `(message_field_type| $proto_type:ident) => do
      let r ← computeMData.ordinary mutEnums mutOneofs messages name mod? proto_type field_name field_proj field_num options
      out := out.push r
    | _ => throwUnsupportedSyntax
  let mut fieldNames : Array Name := #[]
  let mut fieldNumbers : Array Nat := #[]
  for field in out do
    let fieldName := field.field_name.getId.eraseMacroScopes
    if fieldNames.contains fieldName then
      throwErrorAt field.field_name "protobuf field name `{fieldName}` is declared more than once"
    fieldNames := fieldNames.push fieldName
    if field.oneof_type?.isSome then
      if field.field_num.getNat != 0 then
        throwErrorAt field.field_num
          "embedded oneof fields use dummy field number 0, got {field.field_num.getNat}"
    else
      validateFieldNumber field.field_name field.field_num
      let fieldNumber := field.field_num.getNat
      if fieldNumbers.contains fieldNumber then
        throwErrorAt field.field_num "protobuf field number {fieldNumber} is declared more than once"
      fieldNumbers := fieldNumbers.push fieldNumber
    if field.options.packed?.isSome then
      if field.mod != .repeated then
        throwErrorAt field.field_name
          "protobuf option `packed` is only valid on repeated fields"
      if field.decoder_rep_packed?.isNone then
        throwErrorAt field.field_name
          "protobuf option `packed` is only valid for packable scalar or enum fields"
    if field.options.wired_as_group?.isSome then
      if field.map_info?.isSome ||
          field.internal_type?.isSome ||
          field.enum_type?.isSome ||
          field.oneof_type?.isSome then
        throwErrorAt field.field_name
          "protobuf option `wired_as_group` is only valid on message-valued fields"
      if field.options.wired_as_group?.isEqSome true &&
          field.options.packed?.isSome then
        throwErrorAt field.field_name
          "protobuf group fields cannot use option `packed`"
    if field.map_info?.isSome && field.options.default?.isSome then
      throwErrorAt field.field_name "protobuf map fields cannot have explicit defaults"
  return out

end Protobuf.Notation
