module

public import Lean
public import Protobuf.Desc.Basic
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire

meta section

namespace Protobuf.Desc

open Lean Meta Elab Term Command

initialize protoEnumAttr : TagAttribute ←
  registerTagAttribute `proto_enum "mark inductive type to be a protobuf enum"

public def getProtoEnums [Monad m] [MonadEnv m] : m NameSet := do
  let env ← getEnv
  return protoEnumAttr.ext.getState env

public def isProtoEnum [Monad m] [MonadEnv m] (x : Name) : m Bool := do
  let env ← getEnv
  return protoEnumAttr.hasTag env x

syntax enum_entry := ident " = " num ";"

syntax (name := enumDec) "enum " ident "{" enum_entry* "}" : command

private def construct_builder (name : Ident) (push_name : String → Ident) (toInt32 : Ident) : CommandElabM (Ident × Command) := do
  let val ← mkIdent <$> mkFreshUserName `val
  let builderId := push_name "builder"
  let builder ← `(def $builderId:ident : $name → Protobuf.Encoding.ProtoVal := fun $val =>
    Encoding.ProtoVal.ofVarint_int32 ($toInt32 $val)
    )
  return (builderId, builder)

private def construct_decoder? (name : Ident) (push_name : String → Ident) (fromInt32 : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoder?Id := push_name "decoder?"
  let decoder? ← `(def $decoder?Id:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoDecodeError (Option $name) := fun $msg field_num => do
    let x? ← Encoding.Message.getVarint_int32? $msg field_num
    return x?.map $fromInt32
    )
  return (decoder?Id, decoder?)

private def construct_decoder_rep (name : Ident) (push_name : String → Ident) (fromInt32 : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoderRepId := push_name "decoder_rep"
  let decoderRep ← `(def $decoderRepId:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoDecodeError (Array $name) := fun $msg field_num => do
    let xs ← Encoding.Message.getRepeatedVarint_int32 $msg field_num
    return xs.map $fromInt32
    )
  return (decoderRepId, decoderRep)

private def construct_decoder_rep_packed (name : Ident) (push_name : String → Ident) (fromInt32 : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoderRepId := push_name "decoder_rep_packed"
  let decoderRep ← `(def $decoderRepId:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoDecodeError (Array $name) := fun $msg field_num => do
    let xs ← Encoding.Message.getPackedVarint_int32 $msg field_num
    return xs.map $fromInt32
    )
  return (decoderRepId, decoderRep)

@[scoped command_elab enumDec]
public def elabEnumDef : CommandElab := fun stx => do
  let `(enumDec| enum $name { $[$e = $n;]* }) := stx | throwUnsupportedSyntax
  if e.isEmpty then
    throwError "enum declaration must have variant(s)"
  -- if !(n.any (fun n => n.getNat == 0)) then
  --   throwError "enum declaration must have a variant equal to 0"
  let unknownName := `«Unknown.Value»
  let unknownIdent := mkIdent unknownName
  let ind ← `(@[proto_enum] inductive $name where $[| $e:ident]* | $unknownIdent:ident (raw : Int32) )
  let push_name (component : String) := mkIdentFrom name (name.getId.str component)
  let dots ← e.mapM fun x => `(.$x)
  let toInt32Id := push_name "toInt32"
  let toInt32 ← `(def $toInt32Id:ident : $name → Int32
    $[| $dots:term => $n:num]*
    | .$unknownIdent raw => raw
    )
  let fromInt32Id := push_name "fromInt32"
  let fromInt32 ← `(def $fromInt32Id:ident : Int32 → $name
    $[| $n:num => $dots:term]*
    | raw => .$unknownIdent raw
    )
  let inhabited ← `(instance : Inhabited $name where default := .$unknownIdent 0)
  let (_, builder) ← construct_builder name push_name toInt32Id
  let (_, decoder?) ← construct_decoder? name push_name fromInt32Id
  let (_, decoder_rep) ← construct_decoder_rep name push_name fromInt32Id
  let (_, decoder_rep_packed) ← construct_decoder_rep_packed name push_name fromInt32Id
  elabCommand ind
  elabCommand toInt32
  elabCommand fromInt32
  elabCommand inhabited
  elabCommand builder
  elabCommand decoder?
  elabCommand decoder_rep
  elabCommand decoder_rep_packed
