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
  let mut localOneofDecls :
      Array (Ident × Array OneofAlternativeMData) := #[]
  for declaration in ds do
    let inner := declaration.raw[0]
    if inner.getKind == ``oneofDec then
      localOneofDecls :=
        localOneofDecls.push (← oneofAlternativesOfSyntax inner)
  let oneofs :=
    NameSet.ofArray <| localOneofDecls.map fun (name, _) => name.getId
  let localOneofs :=
    localOneofDecls.foldl (init := ({} : LocalOneofAlternatives))
      fun alternatives (name, fields) =>
        alternatives.insert name.getId fields
  let messages := NameSet.ofArray <| ds.filterMap fun x =>
    match x with
    | `(proto_decl| message $name $[$msgOptions?]? { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) =>
        some (protectGeneratedTypeName name).getId
    | _ => none
  let mut block : ProtobufDeclBlock := default
  let mut messageFields :
      Array (Ident × Array MessageFieldTagMData) := #[]
  for x in ds do
    let inner := x.raw[0]
    match inner.getKind with
    | ``enumDec => throwErrorAt inner "enums cannot be inside proto_mutual"
    | ``messageDec => do
        let result ←
          elabMessageDecCore {} oneofs messages localOneofs inner
        block := block.merge result.declBlock
        messageFields :=
          messageFields.push (result.messageName, result.fieldTags)
    | ``oneofDec => do
        let result ←
          elabOneofDecCore {} oneofs messages inner
        block := block.merge result
    | _ => throwErrorAt x "invalid kind"
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
  for (name, fields) in messageFields do
    registerMessageFieldTags name fields
  for (name, alternatives) in localOneofDecls do
    registerOneofAlternatives name alternatives
