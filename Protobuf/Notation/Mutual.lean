module

import Protobuf.Encoding
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
public meta import Protobuf.Notation.Basic
public import Protobuf.Notation.Enum
public import Protobuf.Notation.Message
public import Lean
import Protobuf.Notation.Syntax

public meta section

namespace Protobuf.Notation

open Encoding Notation

open Lean Meta Elab Term Command

@[scoped command_elab proto_mutual_stx]
public def elabProtoMutual : CommandElab := fun stx => do
  let `(proto_mutual_stx| proto_mutual { $ds* }) := stx | throwUnsupportedSyntax
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
    | ``enumDec => throwErrorAt inner "enums cannot be inside proto_mutual"
    | ``messageDec => elabMessageDecCore {} oneofs messages inner
    | ``oneofDec => elabOneofDecCore {} oneofs messages inner
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
