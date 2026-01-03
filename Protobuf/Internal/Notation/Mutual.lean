module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Internal.Notation.Basic
public import Protobuf.Internal.Notation.Enum
public import Protobuf.Internal.Notation.Message
public import Lean

public meta section

namespace Protobuf.Internal.Notation

open Encoding Notation

open Lean Meta Elab Term Command

syntax proto_decl := enumDec <|> messageDec <|> oneofDec

syntax (name := proto_mutual_stx) "proto_mutual " "{" ppLine (proto_decl ppLine)* "}" : command

@[scoped command_elab proto_mutual_stx]
public def elabProtoMutual : CommandElab := fun stx => do
  let `(proto_mutual_stx| proto_mutual { $ds* }) := stx | throwUnsupportedSyntax
  let enums := NameSet.ofArray <| ds.filterMap fun x =>
    match x with
    | `(proto_decl| enum $name $[$opts?]? { $[$e = $n;]* }) => some name.getId
    | _ => none
  let oneofs := NameSet.ofArray <| ds.filterMap fun x =>
    match x with
    | `(proto_decl| oneof $name { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) => some name.getId
    | _ => none
  let messages := NameSet.ofArray <| ds.filterMap fun x =>
    match x with
    | `(proto_decl| message $name $[$msgOptions?]? { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) => some name.getId
    | _ => none
  let r ← ds.mapM fun x => do
    let inner := x.raw[0]
    match inner.getKind with
    | ``enumDec => elabEnumDecCore inner
    | ``messageDec => elabMessageDecCore enums oneofs messages inner
    | ``oneofDec => elabOneofDecCore enums oneofs messages inner
    | _ => throwErrorAt x "invalid kind"
  let block := r.foldl (init := (default : ProtobufDeclBlock)) ProtobufDeclBlock.merge
  -- runTermElabM fun _ => do
  --   for c in block.decls do
  --     logInfo m!"{c}"
  --   for c in block.inhabitedFunctions do
  --     logInfo m!"{c}"
  --   for c in block.inhabitedInsts do
  --     logInfo m!"{c}"
  --   for c in block.functions do
  --     logInfo m!"{c}"
  --   for c in block.insts do
  --     logInfo m!"{c}"
  block.elaborate
