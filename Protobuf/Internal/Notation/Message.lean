module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Internal.Notation.Basic
public import Protobuf.Internal.Notation.Enum
public import Lean

public meta section

namespace Protobuf.Internal.Notation

open Encoding Notation

open Lean Meta Elab Term Command

syntax message_entry_modifier := &"optional" <|> &"repeated" <|> &"required"

syntax message_entry := (message_entry_modifier)? ident ident " = " num (options)? ";"

syntax (name := messageDec) "message " ident (options)? "{" message_entry* "}" : command

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
  | required

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

private def isScalarType : TSyntax `ident → CommandElabM Bool := fun x => do
  if let some x := getInternalType? x then
    return x != InternalType.string && x != InternalType.bytes
  let ns ← try resolveGlobalConst x
    catch _ => return false
  if ns.length > 1 then
    throwErrorAt x "{x} is ambiguous"
  isProtoEnum ns[0]!

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

private structure MData where
  mod : Modifier
  proto_type : TSyntax `ident
  lean_type_inner : TSyntax `ident
  lean_type : TSyntax `term
  field_name : TSyntax `ident
  field_proj : TSyntax `ident
  field_num : TSyntax `num
  options : Options
  is_scalar : Bool

private def construct_toMessage (name : Ident) (push_name : String → Ident) (fields : Array MData) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let val ← mkIdent <$> mkFreshUserName `val
  let toMessageBody ← fields.mapM fun {mod, proto_type, lean_type_inner := _, lean_type := _, field_name := _, field_proj, field_num, options, is_scalar} => do
    let itype? := getInternalType? proto_type
    let builder? ← itype?.mapM InternalType.builder
    let builder := builder?.getD (mkIdentFrom proto_type (proto_type.getId.str "builder"))
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

private def construct_fromMessage (name : Ident) (push_name : String → Ident) (fields : Array MData) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let ns := fields.map MData.field_num
  let decoder ← fields.mapM (β := (Ident × TSyntax ``Parser.Term.doSeqItem)) fun {mod, proto_type, lean_type_inner := _, lean_type := _, field_name, field_proj, field_num, options, is_scalar} => do
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
        let decoder_rep? ← itype?.mapM InternalType.decoder_rep
        let decoder_rep := decoder_rep?.getD (mkIdentFrom proto_type (proto_type.getId.str "decoder_rep"))
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
  let ps := fields.map MData.field_name |>.push u
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

private def construct_merge (name : Ident) (push_name : String → Ident) (fields : Array MData) : CommandElabM (Ident × Command) := do
  let a ← mkIdent <$> mkFreshUserName `a
  let b ← mkIdent <$> mkFreshUserName `b
  let mergeBody ← fields.mapM (β := (Ident × TSyntax ``Parser.Term.doSeqItem)) fun {mod, proto_type, lean_type_inner := _, lean_type := _, field_name, field_proj := field_proj, field_num := _, options := _, is_scalar} => do
    let var ← mkIdent <$> mkFreshUserName (field_name.getId)
    let va ← `($field_proj $a)
    let vb ← `($field_proj $b)
    let merger := mkIdentFrom proto_type (proto_type.getId.append `merge)
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
  let ps := fields.map MData.field_name |>.push u
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

@[scoped command_elab messageDec]
public def elabMessageDec : CommandElab := fun stx => do
  let `(messageDec| message $name $[$msgOptions?]? { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  -- let msgOptions := Options.parseD msgOptions?
  let self_rec := t'.any fun t' => t'.getId == name.getId
  let t ← t'.mapM resolveInternalType
  let ms ← mod.mapM fun mod? => do
    let some mod := mod? | return Modifier.default
    match mod with
    | `(message_entry_modifier| optional) => return Modifier.optional
    | `(message_entry_modifier| repeated) => return Modifier.repeated
    | `(message_entry_modifier| required) => return Modifier.required
    | _ => unreachable!
  let ss ← t' |>.mapM fun t' => isScalarType t'
  let ts ← ms.zip (t.zip ss) |>.mapM fun (mod, t, scalar) => do
      match mod with
      | .default | .required =>
        if scalar then
          `($t)
        else
          `(Option $t)
      | .optional => `(Option $t)
      | .repeated => `(Array $t)
  let struct ← `(structure $name where
    $[$n:ident : $ts]*
    «Unknown.Fields» : Std.HashMap Nat (Array Encoding.ProtoVal)
    deriving Inhabited)
  let push_name (component : String) := mkIdentFrom name (name.getId.str component)
  let dots ← n.mapM fun (x : Ident) => return mkIdentFrom x (name.getId.append x.getId)
  let options := optionsStx.map Options.parseD
  let mdata := ms.zip (t'.zip (t.zip (ts.zip (n.zip (dots.zip (fidx.zip (options.zip ss))))))) |>.map
    fun (mod, proto_type, lean_type_inner, lean_type, field_name, field_proj, field_num, options, is_scalar) =>
      { mod, proto_type, lean_type_inner, lean_type, field_name, field_proj, field_num, options, is_scalar : MData}
  let (toMessage', toMessage) ← construct_toMessage name push_name mdata
  let (_, builder) ← construct_builder name push_name toMessage'
  let (fromMessage', fromMessage) ← construct_fromMessage name push_name mdata
  let (merge', merge) ← construct_merge name push_name mdata
  let (_, decoder?) ← construct_decoder? name push_name fromMessage' merge'
  let (_, decoder_rep) ← construct_decoder_rep name push_name fromMessage'
  if self_rec then
    let m ← `(mutual
        $toMessage
        $builder
        $fromMessage
        $merge
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
    elabCommand merge
    elabCommand decoder?
    elabCommand decoder_rep
