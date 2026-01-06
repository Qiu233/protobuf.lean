module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Notation.Basic
public import Protobuf.Notation.Enum
public import Lean
import Protobuf.Notation.Syntax

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
deriving Inhabited

instance : ToString Modifier where
  toString
    | .default => "default"
    | .optional => "optional"
    | .repeated => "repeated"
    | .required => "required"

inductive InternalType where
  | string
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
  let internal_type? := getInternalType? x
  if let some x := internal_type? then
    if x != InternalType.string && x != InternalType.bytes then
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

private def InternalType.decoder_rep_packed [Monad m] [MonadQuotation m] : InternalType → m Ident
  | .string
  | .bytes =>   panic! "only scalar type is allowed to be packed"
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
deriving Inhabited

structure MapFieldMData where
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

def computeMData.map [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mutEnums mutOneofs messages : NameSet) (_name : Ident)
    (key_proto_type : Ident) (value_proto_type : Ident) (mod? : Modifier)
    (_proto_type : TSyntax `Protobuf.Notation.message_field_type)
    (field_name : Ident)
    (field_proj : Ident)
    (field_num : TSyntax `num)
    (options : Options) : m ProtoFieldMData := do
  let hashMapIdent := mkIdent `Std.HashMap
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
  let key_builder ← InternalType.builder key_internal_type
  let key_decoder? ← InternalType.decoder? key_internal_type
  let value_builder ←
    if let some value_internal_type := value_internal_type? then
      InternalType.builder value_internal_type
    else
      pure (mkIdentFrom value_proto_type (value_proto_type.getId.str "builder"))
  let value_decoder? ←
    if let some value_internal_type := value_internal_type? then
      InternalType.decoder? value_internal_type
    else
      pure (mkIdentFrom value_proto_type (value_proto_type.getId.str "decoder?"))
  let key_default : Term ← match key_internal_type with
    | .bool => `(false)
    | .string => `("")
    | .bytes => `({})
    | _ => `(0)
  let value_default : Term ← match value_internal_type? with
    | some itype =>
      match itype with
      | .bool => `(false)
      | .string => `("")
      | .bytes => `({})
      | _ => `(0)
    | none =>
      if value_enum_type?.isSome || !value_is_scalar then
        pure (mkIdentFrom value_proto_type (value_proto_type.getId.str "Default.Value"))
      else
        throwErrorAt value_proto_type "map value type must be scalar, enum, or message"
  let map_info := { key_proto_type, value_proto_type, key_lean_type, value_lean_type, key_builder, value_builder, key_decoder?, value_decoder?, key_default, value_default }
  let lean_type ← `(Std.HashMap $key_lean_type $value_lean_type)
  let default_map := (← `({}))
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
    test_unset := (← ``(Std.HashMap.isEmpty)),
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
    | .default | .required =>
      if internal_type?.isSome || enum_type?.isSome then
        pure (← `($lean_type_inner), LeanShape.strict)
      else
        pure (← `(Option $lean_type_inner), LeanShape.option)
    | .optional => pure (← `(Option $lean_type_inner), LeanShape.option)
    | .repeated => pure (← `(Array $lean_type_inner), LeanShape.array)

def computeMData.ordinary.computeCtorValue [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (name : Ident) (internal_type? : Option InternalType) (lean_shape : LeanShape) (enum_type? : Option Name) (proto_type : Ident) : m Term := do
  match lean_shape with
    | .strict =>
      if let some itype := internal_type? then
        match itype with
        | .bool => `(false)
        | .string => `("")
        | .bytes => `({})
        | _ => `(0)
      else if enum_type?.isSome then
        pure (mkIdentFrom proto_type (proto_type.getId.str "Default.Value"))
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
        | .bytes => `(ByteArray.isEmpty)
        | _ => `((· == 0))
      else if enum_type?.isSome then
        let x := mkIdentFrom proto_type (proto_type.getId.str "Default.Value")
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
  let lean_type_inner ← resolveInternalType proto_type
  let (is_scalar, internal_type?, enum_type?, oneof_type?) ← getProtoTypeMData mutEnums mutOneofs messages proto_type
  if oneof_type?.isSome && !(mod? matches .default) then
    throwErrorAt name "oneof field cannot have cardinality modifier: {oneof_type?.get!}"
  let (lean_type, lean_shape) ← computeMData.ordinary.computeShape mod? internal_type? enum_type? lean_type_inner
  let builder? ← internal_type?.mapM InternalType.builder
  let builder? := if oneof_type?.isNone then some (builder?.getD (mkIdentFrom proto_type (proto_type.getId.str "builder"))) else none
  let toMessage? := if is_scalar then none else some (mkIdentFrom proto_type (proto_type.getId.str "toMessage"))
  let fromMessage? := if is_scalar then none else some (mkIdentFrom proto_type (proto_type.getId.str "fromMessage"))
  let fromMessage?? := if oneof_type?.isSome then some (mkIdentFrom proto_type (proto_type.getId.str "fromMessage?")) else none
  let decoder?? ← internal_type?.mapM InternalType.decoder?
  let decoder?? := if oneof_type?.isNone then some (decoder??.getD (mkIdentFrom proto_type (proto_type.getId.str "decoder?"))) else none
  let decoder_rep_packed? ← internal_type?.mapM fun x => x.decoder_rep
  let decoder_rep_packed? :=
    if is_scalar then (decoder_rep_packed? <|> some (mkIdentFrom proto_type (proto_type.getId.str "decoder_rep_packed")))
    else none
  let decoder_rep? ← internal_type?.mapM InternalType.decoder_rep
  let decoder_rep? := if oneof_type?.isSome then none else some <| decoder_rep?.getD (mkIdentFrom proto_type (proto_type.getId.str "decoder_rep"))
  let default_lean_value ← match lean_shape with
    | .strict =>
      if internal_type?.isSome then `(Inhabited.default)
      else pure (mkIdentFrom proto_type (proto_type.getId.str "Default.Value"))
    | .option => `(Option.none) -- oneofs always go here
    | .array => `(#[])
    | .map => unreachable!
  let default_ctor_value ← computeMData.ordinary.computeCtorValue name internal_type? lean_shape enum_type? proto_type
  let test_unset ← computeMData.ordinary.computeTestUnset name internal_type? lean_shape enum_type? proto_type
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
  let mut out := #[]
  for mod? in ms, proto_type in t', field_name in n, field_proj in dots, field_num in fidx, options in options do
    match proto_type with
    | `(message_field_type| $s:message_field_type_map) => do
      let `(message_field_type_map| map<$key_proto_type:ident, $value_proto_type:ident>) := s | throwUnsupportedSyntax
      let r ← computeMData.map mutEnums mutOneofs messages name key_proto_type value_proto_type mod? proto_type field_name field_proj field_num options
      out := out.push r
    | `(message_field_type| $proto_type:ident) => do
      let r ← computeMData.ordinary mutEnums mutOneofs messages name mod? proto_type field_name field_proj field_num options
      out := out.push r
    | _ => throwUnsupportedSyntax
  return out

public meta section

public def elabOneofDecCore (mutEnums mutOneofs messages : NameSet) : Syntax → CommandElabM ProtobufDeclBlock := fun stx => do
  let `(oneofDec| oneof $name { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let mdata ← computeMData mutEnums mutOneofs messages name mod t' n fidx optionsStx
  mdata.forM fun x =>
    match x.mod with
    | .default => pure ()
    | _ => throwErrorAt x.field_name "Fields in oneofs must not have cardinality modifier"
  mdata.forM fun x => do
    if x.map_info?.isSome then
      throwErrorAt x.field_name "map fields cannot appear in oneofs"
  let ts := mdata.map fun x => x.lean_type_inner
  let push_name (component : String) := mkIdentFrom name (name.getId.str component)
  let ind ← `(@[proto_oneof] inductive $name where
    $[| $n:ident : $ts:term → $(ts.map (fun _ => name)):ident]*
    )
  let builder ← mdata.mapM fun m =>
    m.builder?.getDM (throwError "{decl_name%}: builder is absent") -- NOTE: builder is absent when type is a oneof, while nested oneof is forbidden by protobuf
  let decoder? ← mdata.mapM fun m =>
    m.decoder??.getDM (throwError "{decl_name%}: decoder? is absent")
  let nums := mdata.map ProtoFieldMData.field_num
  let toMessageId := push_name "toMessage"
  let toMessage ← `(partial def $toMessageId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message := fun val => do
    match val with
    $[| $(mdata.map ProtoFieldMData.field_proj) x =>
      let v ← ($builder:ident x)
      return Protobuf.Encoding.Message.mk #[Protobuf.Encoding.Record.mk $nums:num v]
      ]*
    )
  let msg ← mkIdent <$> mkFreshUserName `msg
  let ds ← mdata.zip decoder? |>.mapM fun (x, d) =>
    `(do
      let Option.some v ← ($d:ident $msg $(x.field_num):num) | throw (Protobuf.Encoding.ProtoError.userError "")
      pure (Option.some ($(x.field_proj) v)))
  let fused ← ds.foldrM (init := ← `(pure Option.none)) (fun x acc => `($x <|> $acc))
  let fromMessage?Id := push_name "fromMessage?"
  let fromMessage? ← `(partial def $fromMessage?Id:ident : Protobuf.Encoding.Message → Except Protobuf.Encoding.ProtoError (Option $name) := fun $msg => $fused:term)
  return { decls := #[ind], functions := #[toMessage, fromMessage?] }

@[scoped command_elab oneofDec]
public def elabOneofDec : CommandElab := fun stx => do
  let r ← elabOneofDecCore {} {} {} stx
  r.elaborate

end

private def construct_toMessage (name : Ident) (push_name : String → Ident) (fields : Array ProtoFieldMData) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let val ← mkIdent <$> mkFreshUserName `val
  let toMessageBody ← fields.mapM fun {mod, field_proj, field_num, options, internal_type?, builder?, enum_type?, oneof_type?, toMessage?, test_unset, map_info?, ..} => do
    if let some map_info := map_info? then
      let entries ← mkIdent <$> mkFreshUserName `entries
      let submsg ← mkIdent <$> mkFreshUserName `submsg
      let entry_key := mkIdent `entry_key
      let entry_val := mkIdent `entry_val
      let key_builder := map_info.key_builder
      let value_builder := map_info.value_builder
      `(Parser.Term.doSeqItem|
        let $msg:ident ← do
          if $test_unset ($field_proj $val) then
            pure $msg
          else
            let $entries:ident ← ($field_proj $val).toArray.mapM (fun ($entry_key:ident, $entry_val:ident) => do
              let $submsg:ident := Protobuf.Encoding.Message.emptyWithCapacity 2
              let $submsg:ident ← (1 : Nat) <~ ($key_builder $entry_key) # $submsg
              let $submsg:ident ← (2 : Nat) <~ ($value_builder $entry_val) # $submsg
              Encoding.ProtoVal.ofMessage $submsg
              )
            $field_num:num <~f (pure $entries) # $msg
        )
    else if oneof_type?.isSome then
      assert! toMessage?.isSome
      let toMessage := toMessage?.get!
      `(Parser.Term.doSeqItem|
        let $msg:ident ← (do
          let sub? ← (Option.mapM $toMessage:ident ($field_proj $val))
          let combined := Option.getD (Option.map (fun sub => Protobuf.Encoding.Message.combine $msg sub) sub?) $msg
          pure combined)
      )
    else
      assert! builder?.isSome
      let builder := builder?.get!
      match mod with
      | .default =>
        if internal_type?.isSome || enum_type?.isSome then
          `(Parser.Term.doSeqItem| let $msg ← do
            if $test_unset ($field_proj $val) then
              pure $msg
            else
              $field_num:num <~ ($builder ($field_proj $val)) # $msg)
        else
          `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~? (Option.mapM $builder ($field_proj $val)) # $msg)
      | .required =>
        if internal_type?.isSome || enum_type?.isSome then
          `(Parser.Term.doSeqItem| let $msg ← do
            if $test_unset ($field_proj $val) then
              pure $msg
            else
              $field_num:num <~ ($builder ($field_proj $val)) # $msg)
        else
          `(Parser.Term.doSeqItem|
            let $msg ← do
              if let Option.some v := ($field_proj $val) then
                $field_num:num <~ ($builder v) # $msg
              else
                throw (Protobuf.Encoding.ProtoError.missingRequiredField s!"required field `{$(quote field_proj.getId.toString)}` is missing when building the message")
              )
      | .optional =>
        `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~? (Option.mapM $builder ($field_proj $val)) # $msg)
      | .repeated =>
        if options.packed?.isEqSome true then
          `(Parser.Term.doSeqItem|
            let $msg ← do
              if $test_unset ($field_proj $val) then
                pure $msg
              else
                $field_num:num <~p (Array.mapM $builder ($field_proj $val)) # $msg)
        else
          `(Parser.Term.doSeqItem|
            let $msg ← do
              if $test_unset ($field_proj $val) then
                pure $msg
              else
                $field_num:num <~f (Array.mapM $builder ($field_proj $val)) # $msg)
  let toMessageId := push_name "toMessage"
  let toMessage ← `(partial def $toMessageId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message := fun $val => do
    let $msg:ident := Protobuf.Encoding.Message.emptyWithCapacity $(quote fields.size)
    $toMessageBody*
    let $msg := Protobuf.Encoding.Message.wire_map $msg ($(push_name "Unknown.Fields") $val)
    return $msg
    )
  return (toMessageId, toMessage)

private def construct_builder (name : Ident) (push_name : String → Ident) (toMessage : Ident) : CommandElabM (Ident × Command) := do
  let val ← mkIdent <$> mkFreshUserName `val
  let builderId := push_name "builder"
  let builder ← `(partial def $builderId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.ProtoVal := fun $val => do
    let m ← $toMessage:ident $val
    Encoding.ProtoVal.ofMessage m
    )
  return (builderId, builder)

private def construct_fromMessage (name : Ident) (push_name : String → Ident) (fields : Array ProtoFieldMData) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let ns := fields.map ProtoFieldMData.field_num
  let decoder ← fields.mapM (β := (Ident × TSyntax ``Parser.Term.doSeqItem)) fun {mod, field_name, field_proj, field_num, options, internal_type?, enum_type?, oneof_type?, decoder??, decoder_rep?, decoder_rep_packed?, fromMessage??, map_info?, ..} => do
    let var ← mkIdent <$> mkFreshUserName (field_name.getId)
    if let some map_info := map_info? then
      let key_decoder? := map_info.key_decoder?
      let value_decoder? := map_info.value_decoder?
      let key_default := map_info.key_default
      let value_default := map_info.value_default
      let entry := mkIdent `entry
      let map := mkIdent `map
      let stx ← `(Parser.Term.doSeqItem|
        let $var ← do
          let entries ← Encoding.Message.getExpandedMessage $msg $field_num:num
          let $map:ident ← entries.foldlM (init := Std.HashMap.emptyWithCapacity 8) (fun $map:ident $entry:ident => do
            let key? ← $key_decoder?:ident $entry 1
            let value? ← $value_decoder?:ident $entry 2
            let key := Option.getD key? $key_default
            let value := Option.getD value? $value_default
            pure (Std.HashMap.insert $map key value))
          pure $map
        )
      return (var, stx)
    else if oneof_type?.isSome then
      assert! fromMessage??.isSome
      let fromMessage? := fromMessage??.get!
      let stx ← `(Parser.Term.doSeqItem| let $var ← $fromMessage?:ident $msg)
      return (var, stx)
    else
      assert! decoder??.isSome
      let decoder? := decoder??.get!
      let stx ← match mod with
        | .default =>
          if internal_type?.isSome || enum_type?.isSome then
            `(Parser.Term.doSeqItem| let $var ← ($decoder? $msg $field_num:num <&> (fun x => Option.getD x Inhabited.default)))
          else
            `(Parser.Term.doSeqItem| let $var ← ($decoder? $msg $field_num:num))
        | .required =>
          if internal_type?.isSome || enum_type?.isSome then
            `(Parser.Term.doSeqItem| let $var ← ($decoder? $msg $field_num:num >>= (fun x => Option.getDM x
              (throw (Protobuf.Encoding.ProtoError.missingRequiredField s!"required field `{$(quote field_proj.getId.toString)}` is missing when decoding the message")))))
          else
            `(Parser.Term.doSeqItem| let $var ← do
              let t? ← ($decoder? $msg $field_num:num)
              if t?.isNone then
                throw (Protobuf.Encoding.ProtoError.missingRequiredField s!"required field `{$(quote field_proj.getId.toString)}` is missing when decoding the message")
              pure t?
              )
        | .optional =>
          `(Parser.Term.doSeqItem| let $var ← ($decoder? $msg $field_num:num))
        | .repeated =>
          if options.packed?.isEqSome true then
            assert! decoder_rep_packed?.isSome
            let decoder_rep_packed := decoder_rep_packed?.get!
            `(Parser.Term.doSeqItem| let $var ← ($decoder_rep_packed $msg $field_num:num))
          else
            assert! decoder_rep?.isSome
            let decoder_rep := decoder_rep?.get!
            `(Parser.Term.doSeqItem| let $var ← ($decoder_rep $msg $field_num:num))
      return (var, stx)
  let u := mkIdent `«Unknown.Fields»
  let decoder := decoder.push (← do
    let s ← `(Parser.Term.doSeqItem| let $u:ident ← do
      let idxs : Array Nat := #[$ns,*]
      let rs := Protobuf.Encoding.Message.records $msg
      let rem := rs.filter (fun x => x.fieldNum ∉ idxs)
      let rem := rem.map fun x => (x.fieldNum, x.value)
      let rem := rem.groupByKey Prod.fst
      let rem := rem.map (fun _ x => x.unzip.snd)
      pure rem
      )
    pure (u, s))
  let ps := fields.map ProtoFieldMData.field_name |>.push u
  let vs := decoder.unzip.fst
  let structInst ← `({ $[$ps:ident := $vs]* : $name })
  let ret ← `(Parser.Term.doSeqItem| return $structInst)
  let fromMessageId := push_name "fromMessage"
  let fromMessage ← `(partial def $fromMessageId:ident : Protobuf.Encoding.Message → Except Protobuf.Encoding.ProtoError $name := fun $msg => do
    $(decoder.unzip.snd)*
    $ret
    )
  return (fromMessageId, fromMessage)

private def construct_decoder_rep (name : Ident) (push_name : String → Ident) (fromMessage : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoderRepId := push_name "decoder_rep"
  let decoderRep ← `(partial def $decoderRepId:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Array $name) := fun $msg field_num => do
    let xs ← Encoding.Message.getExpandedMessage $msg field_num
    xs.mapM $fromMessage:ident
    )
  return (decoderRepId, decoderRep)

private def construct_merge (name : Ident) (push_name : String → Ident) (fields : Array ProtoFieldMData) : CommandElabM (Ident × Command) := do
  let a ← mkIdent <$> mkFreshUserName `a
  let b ← mkIdent <$> mkFreshUserName `b
  let mergeBody ← fields.mapM (β := (Ident × TSyntax ``Parser.Term.doSeqItem)) fun {mod, proto_type, field_name, field_proj, internal_type?, enum_type?, oneof_type?, map_info?, ..} => do
    let var ← mkIdent <$> mkFreshUserName (field_name.getId)
    let va ← `($field_proj $a)
    let vb ← `($field_proj $b)
    let merger := mkIdentFrom proto_type (proto_type.getId.append `merge)
    if let some _ := map_info? then
      let stx ← `(Parser.Term.doSeqItem| let $var := Std.HashMap.union $va $vb)
      return (var, stx)
    else if oneof_type?.isSome then
      let stx ← `(Parser.Term.doSeqItem| let $var := $vb <|> $va)
      return (var, stx)
    else
      let stx ← match mod with
        | .default | .required =>
          if internal_type?.isSome || enum_type?.isSome then
            `(Parser.Term.doSeqItem| let $var := $vb)
          else
            `(Parser.Term.doSeqItem| let $var := match $va:term, $vb:term with
              | Option.some x, Option.some y => Option.some ($merger x y)
              | Option.some x, _ => Option.some x
              | _, Option.some y => Option.some y
              | _, _ => Option.none)
        | .optional =>
          if internal_type?.isSome || enum_type?.isSome then
            `(Parser.Term.doSeqItem| let $var := $vb <|> $va)
          else
            `(Parser.Term.doSeqItem| let $var := match $va:term, $vb:term with
              | Option.some x, Option.some y => Option.some ($merger x y)
              | Option.some x, _ => Option.some x
              | _, Option.some y => Option.some y
              | _, _ => Option.none)
        | .repeated => `(Parser.Term.doSeqItem| let $var := $va ++ $vb) -- concatenate
      return (var, stx)
  let u := mkIdent `«Unknown.Fields»
  let mergeBody := mergeBody.push (← do
    let field_proj := push_name "Unknown.Fields"
    let va ← `($field_proj $a)
    let vb ← `($field_proj $b)
    let s ← `(Parser.Term.doSeqItem| let $u:ident := Protobuf.Encoding.merge_map $va $vb)
    pure (u, s))
  let ps := fields.map ProtoFieldMData.field_name |>.push u
  let (vs, mergeBody) := mergeBody.unzip
  let structInst ← `({ $[$ps:ident := $vs]* : $name })
  let ret ← `(Parser.Term.doSeqItem| return $structInst)
  let mergeId := push_name "merge"
  let merge ← `(partial def $mergeId:ident : $name → $name → $name := fun $a $b => Id.run do
    $mergeBody*
    $ret
    )
  return (mergeId, merge)

private def construct_decoder? (name : Ident) (push_name : String → Ident) (fromMessage merge : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoder?Id := push_name "decoder?"
  let decoder? ← `(partial def $decoder?Id:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Option $name) := fun $msg field_num => do
    let xs? ← Encoding.Message.getExpandedMessage $msg field_num
    let ms ← xs?.mapM $fromMessage:ident
    if let m :: ms := ms.toList then
      if ms.isEmpty then
        return some m
      else
        return some <| ms.foldl (init := m) $merge
    else
      return none
    )
  return (decoder?Id, decoder?)

private def construct_default (name : Ident) (push_name : String → Ident) (fields : Array ProtoFieldMData) : CommandElabM (Ident × Command) := do
  let u := mkIdent `«Unknown.Fields»
  let ps := fields.map ProtoFieldMData.field_name |>.push u
  let vs := fields.map (fun x => x.default_lean_value) |>.push (← ``(Std.HashMap.emptyWithCapacity 8))
  let structInst ← `({ $[$ps:ident := $vs]* : $name })
  let defaultId := push_name "Default.Value"
  let default ← `(partial def $defaultId:ident : $name := $structInst)
  return (defaultId, default)

private def construct_encode (name : Ident) (push_name : String → Ident) (toMessage : Ident) : CommandElabM (Ident × Command) := do
  let encodeId := push_name "encode"
  let s ← `(partial def $encodeId:ident : $name → Except Encoding.ProtoError ByteArray := fun x => do
    return Binary.Put.run 128 (Binary.put (← $toMessage x)))
  return (encodeId, s)

private def construct_decode (name : Ident) (push_name : String → Ident) (fromMessage : Ident) : CommandElabM (Ident × Command) := do
  let decodeId := push_name "decode"
  let s ← `(partial def $decodeId:ident : ByteArray → Except Encoding.ProtoError $name := fun bs => do
    let msg := Binary.Get.run (Binary.getThe Encoding.Message) bs |>.toExcept
    let msg ← Encoding.protoDecodeParseResultExcept msg
    $fromMessage:ident msg)
  return (decodeId, s)

public def elabMessageDecCore (mutEnums mutOneofs messages : NameSet) : Syntax → CommandElabM ProtobufDeclBlock := fun stx => do
  let `(messageDec| message $name $[$msgOptions?]? { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let mdata ← computeMData mutEnums mutOneofs messages name mod t' n fidx optionsStx
  mdata.forM fun x => do
    if x.oneof_type?.isSome then
      if x.field_num.getNat != 0 then
        throwErrorAt x.field_num "oneof field can only have dummy field number 0, but got {x.field_num.getNat}"
  let defs := mdata.map fun x => x.default_ctor_value
  let struct ← `(structure $name where
    $[$n:ident : $(mdata.map fun x => x.lean_type) := $defs]*
    «Unknown.Fields» : Std.HashMap Nat (Array Encoding.ProtoVal) := {})
  let push_name (component : String) := mkIdentFrom name (name.getId.str component)
  let (default', default) ← construct_default name push_name mdata
  let inhInst ← `(instance : Inhabited $name := ⟨$default'⟩)
  let (toMessage', toMessage) ← construct_toMessage name push_name mdata
  let (_, builder) ← construct_builder name push_name toMessage'
  let (fromMessage', fromMessage) ← construct_fromMessage name push_name mdata
  let (merge', merge) ← construct_merge name push_name mdata
  let (_, decoder?) ← construct_decoder? name push_name fromMessage' merge'
  let (_, decoder_rep) ← construct_decoder_rep name push_name fromMessage'
  let (_, encode) ← construct_encode name push_name toMessage'
  let (_, decode) ← construct_decode name push_name fromMessage'
  return { decls := #[struct], inhabitedFunctions := #[default], inhabitedInsts := #[inhInst], functions := #[toMessage, builder, fromMessage, merge, decoder?, decoder_rep, encode, decode] }

@[scoped command_elab messageDec]
public def elabMessageDec : CommandElab := fun stx => do
  let `(messageDec| message $name $[$msgOptions?]? { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let r ← elabMessageDecCore {} {} {name.getId} stx
  r.elaborate
