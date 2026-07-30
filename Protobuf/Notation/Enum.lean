module

public import Lean
public meta import Protobuf.Notation.Basic
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Utils
public meta import Protobuf.Notation.Syntax

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

private def construct_builder
    (name : Ident) (push_name : String → Ident)
    (toInt32 isKnown isClosed : Ident) : CommandElabM (Ident × Command) := do
  let val ← mkIdent <$> mkFreshUserName `val
  let builderId := push_name "builder"
  let builder ← `(partial def $builderId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.ProtoVal := fun $val => do
    if $isClosed:ident && !($isKnown:ident $val) then
      throw (.userError s!"cannot encode an unknown value of closed enum {$(quote name.getId.toString)}")
    Encoding.ProtoVal.ofVarint_int32 ($toInt32 $val))
  return (builderId, builder)

private def construct_decoder?
    (name : Ident) (push_name : String → Ident)
    (fromInt32 isKnown isClosed : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let out ← mkIdent <$> mkFreshUserName `out
  let record ← mkIdent <$> mkFreshUserName `record
  let raw ← mkIdent <$> mkFreshUserName `raw
  let value ← mkIdent <$> mkFreshUserName `value
  let decoder?Id := push_name "decoder?"
  let decoder? ← `(partial def $decoder?Id:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Option $name) := fun $msg field_num => do
    let mut $out:ident : Option $name := none
    for $record:ident in ($msg).getRecordsOf field_num do
      match ($record).value with
      | .VARINT $raw:ident =>
          let $value:ident :=
            $fromInt32:ident (Int32.ofBitVec (UInt32.ofNat $raw:ident).toBitVec)
          if !$isClosed:ident || $isKnown:ident $value:ident then
            $out:ident := some $value:ident
      | _ =>
          throw (.invalidWireType s!"expected VARINT for enum {$(quote name.getId.toString)}")
    return $out:ident)
  return (decoder?Id, decoder?)

private def construct_decoder_rep
    (name : Ident) (push_name : String → Ident)
    (fromInt32 isKnown isClosed : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoderRepId := push_name "decoder_rep"
  let decoderRep ← `(partial def $decoderRepId:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Array $name) := fun $msg field_num => do
    let xs ← Encoding.Message.getRepeatedVarint_int32 $msg field_num
    return (xs.map $fromInt32).filter fun x => !$isClosed:ident || $isKnown:ident x)
  return (decoderRepId, decoderRep)

private def construct_decoder_rep_packed
    (name : Ident) (push_name : String → Ident)
    (fromInt32 isKnown isClosed : Ident) : CommandElabM (Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let decoderRepId := push_name "decoder_rep_packed"
  let decoderRep ← `(partial def $decoderRepId:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Array $name) := fun $msg field_num => do
    let xs ← Encoding.Message.getPackedVarint_int32 $msg field_num
    return (xs.map $fromInt32).filter fun x => !$isClosed:ident || $isKnown:ident x)
  return (decoderRepId, decoderRep)

private def enumValueToInt (stx : TSyntax `enum_value) : CommandElabM Int := do
  let value : Int ←
    match stx with
    | `(enum_value| $n:num) =>
        let some magnitude := protobufIntLiteralValue? n
          | throwErrorAt n "invalid protobuf enum integer literal"
        pure (Int.ofNat magnitude)
    | `(enum_value| -$n:num) =>
        let some magnitude := protobufIntLiteralValue? n
          | throwErrorAt n "invalid protobuf enum integer literal"
        pure (-Int.ofNat magnitude)
    | _ => throwUnsupportedSyntax
  if value < -2147483648 || value > 2147483647 then
    throwErrorAt stx "protobuf enum value {value} is outside the int32 range"
  return value

private def enumValueToTerm (stx : TSyntax `enum_value) : CommandElabM Term := do
  match stx with
  | `(enum_value| $n:num) =>
      let some canonical := canonicalProtobufIntLiteral? n
        | throwErrorAt n "invalid protobuf enum integer literal"
      `($canonical:num)
  | `(enum_value| -$n:num) =>
      let some canonical := canonicalProtobufIntLiteral? n
        | throwErrorAt n "invalid protobuf enum integer literal"
      `(-$canonical:num)
  | _ => throwUnsupportedSyntax

public def elabEnumDecCore : Syntax → CommandElabM ProtobufDeclBlock := fun stx => do
  let `(enumDec| enum $rawName $[$opts?]? { $[$e = $n:enum_value;]* }) := stx | throwUnsupportedSyntax
  let name := protectGeneratedTypeName rawName
  if e.isEmpty then
    throwError "enum declaration must have variant(s)"
  let safeEntries := e.map protectGeneratedMemberName
  let values ← n.mapM enumValueToInt
  let valueTerms ← n.mapM enumValueToTerm
  let options := opts?.map Options.parse |>.getD default
  options.validate #[`allow_alias, `closed]
  if !options.closed && values[0]! != 0 then
    throwErrorAt n[0]!
      "the first value of an open protobuf enum must have numeric value 0"
  let unknownName := `«Unknown.Value»
  let unknownIdent := mkIdent unknownName
  let ind ← `(@[proto_enum] inductive $name where
    $[| $safeEntries:ident]*
    | $unknownIdent:ident (raw : Int32))
  let push_name (component : String) := helperIdent name component
  let dots := safeEntries.map fun x =>
    mkIdentFrom x (name.getId.append x.getId)
  let toInt32Id := push_name "toInt32"
  let toInt32 ← `(partial def $toInt32Id:ident : $name → Int32
    $[| $dots:term => $valueTerms:term]*
    | .$unknownIdent raw => raw
    )
  /-
  Protobuf enum identity is numeric. In particular, two source names admitted
  by `allow_alias` denote the same value; a structural BEq instance would make
  them unequal and would serialize a zero-valued alias as a non-default field.
  -/
  let lhs ← mkIdent <$> mkFreshUserName `lhs
  let rhs ← mkIdent <$> mkFreshUserName `rhs
  let beq ← `(instance : BEq $name where
    beq $lhs:ident $rhs:ident :=
      $toInt32Id:ident $lhs:ident == $toInt32Id:ident $rhs:ident)
  let fromInt32Id := push_name "fromInt32"
  let fromInt32Alts ← do
    let allow_alias := options.allow_alias? |>.getD false
    if !allow_alias then
      let gs := (values.zip e).groupKeyed
      let ds := gs.filter (fun _ y => y.size > 1)
      for (n, xs) in ds do
        let dup := xs[1]!
        logErrorAt dup m!"{n} is duplicated for {dup}"
      if !ds.isEmpty then
        throwError "option `allow_alias` is not enabled but alias(es) exist"
    let t := (valueTerms.zip values).zip dots
    let t := t.eraseDupsBy (fun a b => a.fst.snd == b.fst.snd)
    t.mapM fun ((valueTerm, _), d) => `(Parser.Term.matchAltExpr| | $valueTerm:term => $d:term)
  let raw ← mkIdent <$> mkFreshUserName `raw
  -- Pattern matching directly on `Int32` exposes its BitVec-based
  -- representation to Lean's equation compiler, which gets stuck for
  -- negative literals.  Match on the mathematical `Int` view instead.
  let fromInt32 ← `(partial def $fromInt32Id:ident : Int32 → $name := fun $raw =>
    match ($raw).toInt with
    $fromInt32Alts:matchAlt*
    | _ => .$unknownIdent $raw
    )
  /-
  Keep implementation-only helpers below a nested namespace.  Enum value
  identifiers share the enum namespace and protobuf legitimately permits
  values named `isKnown` or `isClosed`; putting helpers at those flat names
  made such schemas fail with duplicate Lean declarations.
  -/
  let internalName (component : String) :=
    helperIdent name component
  let isKnownId := internalName "isKnown"
  let isKnown ← `(partial def $isKnownId:ident : $name → Bool
    | .$unknownIdent _ => false
    | _ => true)
  let isClosedId := internalName "isClosed"
  let isClosedValue := options.closed
  let isClosed ← `(partial def $isClosedId:ident : Bool := $(quote isClosedValue))
  /-
  Protobuf's implicit enum default is always the first declared value.
  Open enums are checked above to ensure that this first value is numeric zero;
  closed proto2/Editions enums may put a zero-valued declaration later in the
  list, but that later declaration must not replace the first value as default.
  -/
  let defaultVariant : Term := dots[0]!
  let inhabited ← `(instance : Inhabited $name where default := $defaultVariant)
  let default_valueId := push_name "Default.Value"
  let default_value ← `(partial def $default_valueId : $name := $defaultVariant)
  let (_, builder) ← construct_builder name push_name toInt32Id isKnownId isClosedId
  let (_, decoder?) ← construct_decoder? name push_name fromInt32Id isKnownId isClosedId
  let (_, decoder_rep) ← construct_decoder_rep name push_name fromInt32Id isKnownId isClosedId
  let (_, decoder_rep_packed) ←
    construct_decoder_rep_packed name push_name fromInt32Id isKnownId isClosedId
  return {
    decls := #[ind]
    functions := #[
      toInt32,
      fromInt32,
      isKnown,
      isClosed,
      builder,
      decoder?,
      decoder_rep,
      decoder_rep_packed
    ]
    inhabitedFunctions := #[default_value]
    inhabitedInsts := #[inhabited]
    insts := #[beq]
  }

@[scoped command_elab enumDec]
public def elabEnumDec : CommandElab := fun stx => do
  let r ← elabEnumDecCore stx
  r.elaborate
