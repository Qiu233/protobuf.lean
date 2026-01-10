module

public import Lean
public meta import Protobuf.Notation.Basic
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Utils
import Protobuf.Notation.Syntax

public meta section

namespace Protobuf.Notation

open Lean Meta Elab Term Command

initialize protoEnumAttr : TagAttribute ←
  registerTagAttribute `proto_enum "mark inductive type to be a protobuf enum"

public def getProtoEnums [Monad m] [MonadEnv m] : m NameSet := do
  let env ← getEnv
  return protoEnumAttr.ext.getState env

public def isProtoEnum [Monad m] [MonadEnv m] (x : Name) : m Bool := do
  let env ← getEnv
  return protoEnumAttr.hasTag env x

private def construct_builder (name : Ident) (push_name : String → Ident) (toInt32 : Ident) : CommandElabM (Ident × Command) := do
  let val ← mkIdent <$> mkFreshUserName `val
  let builderId := push_name "builder"
  let builder ← `(partial def $builderId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.ProtoVal := fun $val =>
    Encoding.ProtoVal.ofVarint_int32 ($toInt32 $val)
    )
  return (builderId, builder)

private def construct_decoder? (name : Ident) (push_name : String → Ident) (fromInt32 : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoder?Id := push_name "decoder?"
  let decoder? ← `(partial def $decoder?Id:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Option $name) := fun $msg field_num => do
    let x? ← Encoding.Message.getVarint_int32? $msg field_num
    return x?.map $fromInt32
    )
  return (decoder?Id, decoder?)

private def construct_decoder_rep (name : Ident) (push_name : String → Ident) (fromInt32 : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoderRepId := push_name "decoder_rep"
  let decoderRep ← `(partial def $decoderRepId:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Array $name) := fun $msg field_num => do
    let xs ← Encoding.Message.getRepeatedVarint_int32 $msg field_num
    return xs.map $fromInt32
    )
  return (decoderRepId, decoderRep)

private def construct_decoder_rep_packed (name : Ident) (push_name : String → Ident) (fromInt32 : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoderRepId := push_name "decoder_rep_packed"
  let decoderRep ← `(partial def $decoderRepId:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Array $name) := fun $msg field_num => do
    let xs ← Encoding.Message.getPackedVarint_int32 $msg field_num
    return xs.map $fromInt32
    )
  return (decoderRepId, decoderRep)

public def elabEnumDecCore : Syntax → CommandElabM ProtobufDeclBlock := fun stx => do
  let `(enumDec| enum $name $[$opts?]? { $[$e = $n;]* }) := stx | throwUnsupportedSyntax
  if e.isEmpty then
    throwError "enum declaration must have variant(s)"
  let options := opts?.map Options.parse |>.getD default
  let unknownName := `«Unknown.Value»
  let unknownIdent := mkIdent unknownName
  let ind ← `(@[proto_enum] inductive $name where $[| $e:ident]* | $unknownIdent:ident (raw : Int32) deriving BEq)
  let push_name (component : String) := mkIdentFrom name (name.getId.str component)
  let dots := e.map fun x => mkIdentFrom x (name.getId.append x.getId)
  let toInt32Id := push_name "toInt32"
  let toInt32 ← `(partial def $toInt32Id:ident : $name → Int32
    $[| $dots:term => $n:num]*
    | .$unknownIdent raw => raw
    )
  let fromInt32Id := push_name "fromInt32"
  let fromInt32Alts ← do
    let allow_alias := options.allow_alias? |>.getD false
    if !allow_alias then
      let gs := (n.zip e).map (fun (n, x) => (n.getNat, x)) |>.groupKeyed
      let ds := gs.filter (fun _ y => y.size > 1)
      for (n, xs) in ds do
        let dup := xs[1]!
        logErrorAt dup m!"{n} is duplicated for {dup}"
      if !ds.isEmpty then
        throwError "option `allow_alias` is not enabled but alias(es) exist"
    let t := n.zip dots
    let t := t.eraseDupsBy (fun a b => a.fst.getNat == b.fst.getNat)
    t.mapM fun (n, d) => `(Parser.Term.matchAltExpr| | $n:num => $d:term)
  let fromInt32 ← `(partial def $fromInt32Id:ident : Int32 → $name
    $fromInt32Alts:matchAlt*
    | raw => .$unknownIdent raw
    )
  let nullVariant? := dots.zip n |>.find? fun (_, y) => y.getNat == 0
  let nullVariant? ← nullVariant?.mapM (fun x => `($x.fst))
  let nullVariant ← nullVariant?.getDM `(.$unknownIdent 0)
  let inhabited ← `(instance : Inhabited $name where default := $nullVariant)
  let default_valueId := push_name "Default.Value"
  let default_value ← `(partial def $default_valueId : $name := $nullVariant)
  let (_, builder) ← construct_builder name push_name toInt32Id
  let (_, decoder?) ← construct_decoder? name push_name fromInt32Id
  let (_, decoder_rep) ← construct_decoder_rep name push_name fromInt32Id
  let (_, decoder_rep_packed) ← construct_decoder_rep_packed name push_name fromInt32Id
  return { decls := #[ind], functions := #[
          toInt32,
          fromInt32,
          builder,
          decoder?,
          decoder_rep,
          decoder_rep_packed,
        ], inhabitedFunctions := #[default_value], inhabitedInsts := #[inhabited] }

@[scoped command_elab enumDec]
public def elabEnumDec : CommandElab := fun stx => do
  let r ← elabEnumDecCore stx
  r.elaborate
