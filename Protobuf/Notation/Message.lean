module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Notation.Basic
public import Protobuf.Notation.Enum
public import Lean

public meta section

namespace Protobuf.Notation

open Encoding Notation

open Lean Meta Elab Term Command

syntax message_entry_modifier := &"optional" <|> &"repeated" <|> &"required"

syntax message_entry := (message_entry_modifier)? ident ident " = " num (options)? ";"

syntax (name := messageDec) "message " ident (options)? " {" ppLine (message_entry ppLine)* "}" : command

syntax (name := oneofDec) "oneof " ident " {" ppLine (message_entry ppLine)*  "}" : command

-- scoped syntax "options% " options : term

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
  is_scalar : Bool
  internal_type? : Option InternalType
  default_lean_value : Term
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

def computeMData [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mutEnums mutOneofs messages : NameSet) (name : Ident)
    (mod : Array (Option (TSyntax `Protobuf.Notation.message_entry_modifier)))
    (t' n : Array (TSyntax `ident)) (fidx : Array (TSyntax `num)) (optionsStx : Array (Option (TSyntax `Protobuf.Notation.options))) : m (Array ProtoFieldMData) := do
  let t ← t'.mapM resolveInternalType
  let ss ← t' |>.mapM fun t' => getProtoTypeMData mutEnums mutOneofs messages t'
  let ms ← mod.mapM fun mod? => do
    let some mod := mod? | return Modifier.default
    match mod with
    | `(message_entry_modifier| optional) => return Modifier.optional
    | `(message_entry_modifier| repeated) => return Modifier.repeated
    | `(message_entry_modifier| required) => return Modifier.required
    | _ => unreachable!
  let ts ← ms.zip (t.zip ss) |>.mapM fun (mod, t, (is_scalar, _, _, oneof_type?)) => do
      if oneof_type?.isSome && !(mod matches .default) then
        throwErrorAt name "oneof field cannot have cardinality modifier: {oneof_type?.get!}"
      let s ← match mod with
      | .default | .required =>
        if is_scalar then
          return (← `($t), LeanShape.strict)
        else
          return (← `(Option $t), LeanShape.option)
      | .optional => return (← `(Option $t), LeanShape.option)
      | .repeated => return (← `(Array $t), LeanShape.array)
  let dots ← n.mapM fun (x : Ident) => return mkIdentFrom x (name.getId.append x.getId)
  let options := optionsStx.map Options.parseD
  ms.zip (t'.zip (t.zip (ts.zip (n.zip (dots.zip (fidx.zip (options.zip ss))))))) |>.mapM
    fun (mod, proto_type, lean_type_inner, (lean_type, lean_shape), field_name, field_proj, field_num, options, (is_scalar, internal_type?, enum_type?, oneof_type?)) => do
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
          if internal_type?.isSome then
            `(Inhabited.default)
          else pure (mkIdentFrom proto_type (proto_type.getId.str "Default.Value"))
        | .option => `(Option.none) -- oneofs always go here
        | .array => `(#[])
      return { mod, proto_type, lean_type_inner, lean_type, field_name, field_proj, field_num, options, lean_shape, default_lean_value,
               is_scalar, internal_type?, enum_type?, oneof_type?, builder?, toMessage?, decoder??, fromMessage?, fromMessage??, decoder_rep_packed?, decoder_rep? }


public meta section

-- syntax (name := proto_oneof_variant_attr) "proto_oneof_variant " term : attr

-- def elabProtoOneOfVariantField (declName : Name) (stx : Syntax) : AttrM ProtoFieldMData := do
--   let `(proto_oneof_variant_attr| proto_oneof_variant $arg) := stx | throwUnsupportedSyntax
--   let `(Parser.Term.structInst| { $fields,* }) := arg | throwUnsupportedSyntax
--   let fields := fields.getElems
--   let fields ← fields.mapM fun x =>
--     match x with
--     | `(Parser.Term.structInstField| $fname:ident := $fval) => pure (fname.getId, fval)
--     | _ => withRef x throwUnsupportedSyntax
--   let fields := fields.toList
--   let find (n : Name) := (fields.lookup n).getDM (throwError "{n} is absent")
--   let result ← IO.mkRef (default : ProtoFieldMData)
--   match ← find `mod with
--     | `(default) => result.modify fun r => {r with mod := .default}
--     | `(optional) => result.modify fun r => {r with mod := .optional}
--     | `(repeated) => result.modify fun r => {r with mod := .repeated}
--     | `(required) => result.modify fun r => {r with mod := .required}
--     | s => withRef s throwUnsupportedSyntax
--   match ← find `proto_type with
--     | `($x:ident) => result.modify fun r => {r with proto_type := x}
--     | s => withRef s throwUnsupportedSyntax
--   match ← find `lean_type_inner with
--     | `($x:ident) => result.modify fun r => {r with lean_type_inner := x}
--     | s => withRef s throwUnsupportedSyntax
--   match ← find `lean_type with
--     | x => result.modify fun r => {r with lean_type := x}
--   match ← find `field_name with
--     | `($x:ident) => result.modify fun r => {r with field_name := x}
--     | s => withRef s throwUnsupportedSyntax
--   match ← find `field_proj with
--     | `($x:ident) =>
--       if x.getId.isSuffixOf declName then
--         result.modify fun r => {r with field_proj := mkIdentFrom x declName}
--       else
--         throwErrorAt x "{x} is not suffix of {declName}"
--         -- result.modify fun r => {r with field_proj := x}
--     | s => withRef s throwUnsupportedSyntax
--   match ← find `field_num with
--     | `($x:num) => result.modify fun r => {r with field_num := x}
--     | s => withRef s throwUnsupportedSyntax
--   match ← find `options with
--     | `(options% $opts) => result.modify fun r => {r with options := Options.parse opts}
--     | s => withRef s throwUnsupportedSyntax
--   match ← find `is_scalar with
--     | `(true) => result.modify fun r => {r with is_scalar := true}
--     | `(false) => result.modify fun r => {r with is_scalar := false}
--     | s => withRef s throwUnsupportedSyntax
--   result.get

-- initialize protoOneOfVariantField : ParametricAttribute ProtoFieldMData ←
--   registerParametricAttribute
--     { name := `proto_oneof_variant_attr,
--       descr := "mark inductive type constructor to be a oneof variants",
--       getParam := fun declName stx => do
--         elabProtoOneOfVariantField declName stx
--       }

-- public def getProtoOneOfVariants [Monad m] [MonadEnv m] : m (NameMap ProtoFieldMData) := do
--   let env ← getEnv
--   return protoOneOfVariantField.ext.getState env |>.snd

-- public def isProtoOneOfVariant [Monad m] [MonadEnv m] (x : Name) : m (Option ProtoFieldMData) := do
--   let env ← getEnv
--   return protoOneOfVariantField.getParam? env x



public def elabOneofDecCore (mutEnums mutOneofs messages : NameSet) : Syntax → CommandElabM ProtobufDeclBlock := fun stx => do
  let `(oneofDec| oneof $name { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let mdata ← computeMData mutEnums mutOneofs messages name mod t' n fidx optionsStx
  mdata.forM fun x =>
    match x.mod with
    | .default => pure ()
    | _ => throwErrorAt x.field_name "Fields in oneofs must not have cardinality modifier"
  let ts := mdata.map fun x => x.lean_type_inner
  let push_name (component : String) := mkIdentFrom name (name.getId.str component)
  -- let mdataAttr ← mdata.mapM fun x => do
  --   let opts ← x.options.raw.mapM fun (id, val) => `(options_entry| $id:ident = $val)
  --   `(attr| proto_oneof_variant {
  --         mod := $(mkIdent (Name.mkStr1 (toString x.mod))),
  --         proto_type := $(x.proto_type), lean_type_inner := $(x.lean_type_inner), lean_type := $(x.lean_type),
  --         field_proj := $(x.field_proj), field_name := $(x.field_name), field_num := $(x.field_num), is_scalar := $(quote x.is_scalar),
  --         options := options% [$opts,*] })
  let ind ← `(@[proto_oneof] inductive $name where
    $[| $n:ident : $ts:term → $(ts.map (fun _ => name)):ident]*
    )
  -- let attrs ← mdata.zip mdataAttr |>.mapM fun (x, attr) =>
  --   `(attribute [$attr:attr] $(x.field_proj))
  -- attrs.forM elabCommand
  -- emplace : OneOf → Message → Message
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
  let toMessageBody ← fields.mapM fun {mod, field_proj, field_num, options, is_scalar, builder?, oneof_type?, toMessage?, ..} => do
    if oneof_type?.isSome then
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
        if is_scalar then
          `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~ ($builder ($field_proj $val)) # $msg)
        else
          `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~? (Option.mapM $builder ($field_proj $val)) # $msg)
      | .required =>
        if is_scalar then
          `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~ ($builder ($field_proj $val)) # $msg)
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
        if options.packed?.getD is_scalar then
          `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~p (Array.mapM $builder ($field_proj $val)) # $msg)
        else
          `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~f (Array.mapM $builder ($field_proj $val)) # $msg)
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
  let decoder ← fields.mapM (β := (Ident × TSyntax ``Parser.Term.doSeqItem)) fun {mod, field_name, field_proj, field_num, options, is_scalar, oneof_type?, decoder??, decoder_rep?, decoder_rep_packed?, fromMessage?? ..} => do
    let var ← mkIdent <$> mkFreshUserName (field_name.getId)
    if oneof_type?.isSome then
      assert! fromMessage??.isSome
      let fromMessage? := fromMessage??.get!
      let stx ← `(Parser.Term.doSeqItem| let $var ← $fromMessage?:ident $msg)
      return (var, stx)
    else
      assert! decoder??.isSome
      let decoder? := decoder??.get!
      let stx ← match mod with
        | .default =>
          if is_scalar then
            `(Parser.Term.doSeqItem| let $var ← ($decoder? $msg $field_num:num <&> (fun x => Option.getD x Inhabited.default)))
          else
            `(Parser.Term.doSeqItem| let $var ← ($decoder? $msg $field_num:num))
        | .required =>
          if is_scalar then
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
          if options.packed?.getD is_scalar then
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
  let mergeBody ← fields.mapM (β := (Ident × TSyntax ``Parser.Term.doSeqItem)) fun {mod, proto_type, field_name, field_proj := field_proj, is_scalar, oneof_type?, ..} => do
    let var ← mkIdent <$> mkFreshUserName (field_name.getId)
    let va ← `($field_proj $a)
    let vb ← `($field_proj $b)
    let merger := mkIdentFrom proto_type (proto_type.getId.append `merge)
    if oneof_type?.isSome then
      let stx ← `(Parser.Term.doSeqItem| let $var := $vb <|> $va)
      return (var, stx)
    else
      let stx ← match mod with
        | .default | .required =>
          if is_scalar then
            `(Parser.Term.doSeqItem| let $var := $vb)
          else if (proto_type matches `(string) | `(bytes)) then
            `(Parser.Term.doSeqItem| let $var := $vb <|> $va) -- optional, last first
          else
            `(Parser.Term.doSeqItem| let $var := match $va:term, $vb:term with
              | Option.some x, Option.some y => Option.some ($merger x y)
              | Option.some x, _ => Option.some x
              | _, Option.some y => Option.some y
              | _, _ => Option.none)
        | .optional =>
          if is_scalar || (proto_type matches `(string) | `(bytes)) then
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

public def elabMessageDecCore (mutEnums mutOneofs messages : NameSet) : Syntax → CommandElabM ProtobufDeclBlock := fun stx => do
  let `(messageDec| message $name $[$msgOptions?]? { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  -- let msgOptions := Options.parseD msgOptions?
  let mdata ← computeMData mutEnums mutOneofs messages name mod t' n fidx optionsStx
  mdata.forM fun x => do
    if x.oneof_type?.isSome then
      if x.field_num.getNat != 0 then
        throwErrorAt x.field_num "oneof field can only have dummy field number 0, but got {x.field_num.getNat}"
  let struct ← `(structure $name where
    $[$n:ident : $(mdata.map fun x => x.lean_type)]*
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
  return { decls := #[struct], inhabitedFunctions := #[default], inhabitedInsts := #[inhInst], functions := #[toMessage, builder, fromMessage, merge, decoder?, decoder_rep] }

@[scoped command_elab messageDec]
public def elabMessageDec : CommandElab := fun stx => do
  let `(messageDec| message $name $[$msgOptions?]? { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let r ← elabMessageDecCore {} {} {name.getId} stx
  r.elaborate
