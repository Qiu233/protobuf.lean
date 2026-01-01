module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public import Protobuf.Desc.Enum
public import Lean

public meta section

namespace Protobuf.Desc

open Encoding

open Lean Meta Elab Term Command

syntax message_entry_modifier := "optional" <|> "repeated"

syntax message_entry_config_entry := ident " = " term

syntax message_entry_config := "[" message_entry_config_entry,*,? "]"

syntax message_entry := (message_entry_modifier)? ident ident " = " num (message_entry_config)? ";"

syntax (name := messageDec) "message " ident "{" message_entry* "}" : command

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

private inductive Modifier where
  /-- singular scalar fields are encoded as plain scalar type with default value -/
  | default
  /-- all optional -/
  | optional
  | repeated

private inductive InternalType where
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

private def isScalarType [Monad m] [MonadEnv m] : TSyntax `ident → m Bool := fun x => do
  let a := getInternalType? x |>.map (fun x => x != InternalType.string && x != InternalType.bytes) |>.getD false
  return a || (← isProtoEnum x.getId)

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
  | .string =>  ``(Encoding.Message.getRepeatedString)
  | .bytes =>   ``(Encoding.Message.getRepeatedBytes)
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

private structure FieldConfig where
  raw : Array (Ident × Term)
  entries : Std.HashMap Name Term
deriving Inhabited

private def FieldConfig.get? (cfg : FieldConfig) (x : Name) : Option Term := cfg.entries[x]?

private def FieldConfig.is_true (cfg : FieldConfig) (x : Name) : Bool :=
  if let some y := cfg.get? x then
    y matches `(true)
  else false

private def FieldConfig.packed (cfg : FieldConfig) : Bool := cfg.is_true `packed

private def expandMessageEntryConfig (s : TSyntax ``message_entry_config) : FieldConfig :=
  match s with
  | `(message_entry_config| [ $[$name = $val],* ]) =>
    let ls := name.zip val
    let map := Std.HashMap.ofList <| ls.toList.map fun (x, v) => (x.getId, v)
    { raw := ls, entries := map }
  | _ => unreachable!

private structure MData where
  mod : Modifier
  proto_type : TSyntax `ident
  lean_type_inner : TSyntax `ident
  lean_type : TSyntax `term
  field_name : TSyntax `ident
  field_proj : TSyntax `ident
  field_num : TSyntax `num
  config : FieldConfig
  is_scalar : Bool


private def construct_toMessage (name : Ident) (push_name : String → Ident) (fields : Array MData) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let val ← mkIdent <$> mkFreshUserName `val
  let builder ← fields.mapM fun {mod, proto_type, lean_type_inner := _, lean_type := _, field_name := _, field_proj, field_num, config, is_scalar} => do
    let itype? := getInternalType? proto_type
    let builder? ← itype?.mapM InternalType.builder
    let builder := builder?.getD (mkIdentFrom proto_type (proto_type.getId.str "builder"))
    match mod with
    | .default =>
      if is_scalar then
        ``($field_num:num <~ ($builder ($field_proj $val)) # $msg)
      else
        ``($field_num:num <~? ($builder <$> ($field_proj $val)) # $msg)
    | .optional =>
      ``($field_num:num <~? ($builder <$> ($field_proj $val)) # $msg)
    | .repeated =>
      if config.packed then
        ``($field_num:num <~p (Array.map $builder ($field_proj $val)) # $msg)
      else
        ``($field_num:num <~f (Array.map $builder ($field_proj $val)) # $msg)
  let toMessageBody ← builder.foldrM (init := ← `($msg)) fun b acc => `(let $msg:ident := $b; $acc)
  let toMessageId := push_name "toMessage"
  let toMessage ← `(partial def $toMessageId:ident : $name → Protobuf.Encoding.Message := fun $val =>
    let $msg:ident := Protobuf.Encoding.Message.emptyWithCapacity $(quote fields.size)
    $toMessageBody
    )
  return (toMessageId, toMessage)

private def construct_builder (name : Ident) (push_name : String → Ident) (toMessage : Ident) : CommandElabM (Ident × Command) := do
  let val ← mkIdent <$> mkFreshUserName `val
  let builderId := push_name "builder"
  let builder ← `(partial def $builderId:ident : $name → Protobuf.Encoding.ProtoVal := fun $val =>
    Encoding.ProtoVal.ofMessage ($toMessage:ident $val)
    )
  return (builderId, builder)

private def construct_fromMessage (name : Ident) (push_name : String → Ident) (fields : Array MData) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoder ← fields.mapM (β := (Ident × TSyntax ``Parser.Term.doSeqItem)) fun {mod, proto_type, lean_type_inner := _, lean_type := _, field_name, field_proj, field_num, config, is_scalar} => do
    let itype? := getInternalType? proto_type
    let decoder? ← itype?.mapM InternalType.decoder?
    let decoder? := decoder?.getD (mkIdentFrom proto_type (proto_type.getId.str "decoder?"))
    let decoder_rep_packed? ← itype?.mapM fun x => x.decoder_rep
    let decoder_rep_packed? :=
      if is_scalar then (decoder_rep_packed? <|> some (mkIdentFrom proto_type (proto_type.getId.str "decoder_rep_packed")))
      else none
    let var ← mkIdent <$> mkFreshUserName (field_name.getId)
    let stx ← match mod with
    | .default =>
      if is_scalar then
        `(Parser.Term.doSeqItem| let $var ← ($decoder? $msg $field_num:num <&> (fun x => Option.getD x Inhabited.default)))
      else
        `(Parser.Term.doSeqItem| let $var ← ($decoder? $msg $field_num:num))
    | .optional =>
      `(Parser.Term.doSeqItem| let $var ← ($decoder? $msg $field_num:num))
    | .repeated =>
      if config.packed then
        assert! decoder_rep_packed?.isSome
        let decoder_rep_packed := decoder_rep_packed?.get!
        `(Parser.Term.doSeqItem| let $var ← ($decoder_rep_packed $msg $field_num:num))
      else
        let decoder_rep? ← itype?.mapM InternalType.decoder_rep
        let decoder_rep := decoder_rep?.getD (mkIdentFrom proto_type (proto_type.getId.str "decoder_rep"))
        `(Parser.Term.doSeqItem| let $var ← ($decoder_rep $msg $field_num:num))
    return (var, stx)
  let ps := fields.map MData.field_name
  let vs := decoder.unzip.fst
  let structInst ← `({ $[$ps:ident := $vs]* : $name })
  let ret ← `(Parser.Term.doSeqItem| return $structInst)
  let fromMessageId := push_name "fromMessage"
  let fromMessage ← `(partial def $fromMessageId:ident : Protobuf.Encoding.Message → Except Protobuf.Encoding.ProtoDecodeError $name := fun $msg => do
    $(decoder.unzip.snd)*
    $ret
    )
  return (fromMessageId, fromMessage)

private def construct_decoder? (name : Ident) (push_name : String → Ident) (fromMessage : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoder?Id := push_name "decoder?"
  let decoder? ← `(partial def $decoder?Id:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoDecodeError (Option $name) := fun $msg field_num => do
    let bytes? ← Encoding.Message.getBytes? $msg field_num
    bytes?.mapM fun bytes => do
      let r := Binary.Get.run (Binary.getThe Protobuf.Encoding.Message) bytes
      let m ← Encoding.protoDecodeParseResultExcept r.toExcept
      $fromMessage:ident m
    )
  return (decoder?Id, decoder?)

private def construct_decoder_rep (name : Ident) (push_name : String → Ident) (fromMessage : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoderRepId := push_name "decoder_rep"
  let decoderRep ← `(partial def $decoderRepId:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoDecodeError (Array $name) := fun $msg field_num => do
    let xs ← Encoding.Message.getRepeatedBytes $msg field_num
    xs.mapM fun bytes => do
      let r := Binary.Get.run (Binary.getThe Protobuf.Encoding.Message) bytes
      let m ← Encoding.protoDecodeParseResultExcept r.toExcept
      $fromMessage:ident m
    )
  return (decoderRepId, decoderRep)

@[scoped command_elab messageDec]
public def elabMessageDec : CommandElab := fun stx => do
  let `(messageDec| message $name { $[$[$mod]? $t' $n = $fidx $[$cfgStx]? ;]* }) := stx | throwUnsupportedSyntax
  let self_rec := t'.any fun t' => t'.getId == name.getId
  let t ← t'.mapM resolveInternalType
  let ms ← mod.mapM fun mod? => do
    let some mod := mod? | return Modifier.default
    match mod with
    | `(message_entry_modifier| optional) => return Modifier.optional
    | `(message_entry_modifier| repeated) => return Modifier.repeated
    | _ => unreachable!
  let ss ← t' |>.mapM fun t' => isScalarType t'
  let ts ← ms.zip (t.zip ss) |>.mapM fun (mod, t, scalar) => do
      match mod with
      | .default =>
        if scalar then
          `($t)
        else
          `(Option $t)
      | .optional => `(Option $t)
      | .repeated => `(Array $t)
  let struct ← `(structure $name where $[$n:ident : $ts]* deriving Inhabited)
  let push_name (component : String) := mkIdentFrom name (name.getId.str component)
  let dots ← n.mapM fun (x : Ident) => return mkIdentFrom x (name.getId.append x.getId)
  let cfg := cfgStx.map (fun x => (x.map expandMessageEntryConfig).getD default)
  let mdata := ms.zip (t'.zip (t.zip (ts.zip (n.zip (dots.zip (fidx.zip (cfg.zip ss))))))) |>.map
    fun (mod, proto_type, lean_type_inner, lean_type, field_name, field_proj, field_num, config, is_scalar) =>
      { mod, proto_type, lean_type_inner, lean_type, field_name, field_proj, field_num, config, is_scalar : MData}
  let (toMessage', toMessage) ← construct_toMessage name push_name mdata
  let (_, builder) ← construct_builder name push_name toMessage'
  let (fromMessage', fromMessage) ← construct_fromMessage name push_name mdata
  let (_, decoder?) ← construct_decoder? name push_name fromMessage'
  let (_, decoder_rep) ← construct_decoder_rep name push_name fromMessage'
  if self_rec then
    let m ← `(mutual
        $toMessage
        $builder
        $fromMessage
        $decoder?
        $decoder_rep
      end)
    elabCommand struct
    elabCommand m
  else
    elabCommand struct
    elabCommand toMessage
    elabCommand builder
    elabCommand fromMessage
    elabCommand decoder?
    elabCommand decoder_rep
