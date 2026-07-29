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
  let declarationNames := NameSet.ofArray <| ds.filterMap fun declaration =>
    let inner := declaration.raw[0]
    match inner.getKind with
    | ``messageDec =>
        match inner with
        | `(messageDec| message $name $[$_msgOptions?]? {
            $[$[$_mod]? $_t' $_n = $_fidx $[$_optionsStx]? ;]* }) =>
            some (protectGeneratedTypeName name).getId
        | _ => none
    | ``oneofDec =>
        match inner with
        | `(oneofDec| oneof $name {
            $[$[$_mod]? $_t' $_n = $_fidx $[$_optionsStx]? ;]* }) =>
            some (protectGeneratedTypeName name).getId
        | _ => none
    | ``enumDec =>
        match inner with
        | `(enumDec| enum $name $[$_opts?]? {
            $[$_entry = $_value:enum_value;]* }) =>
            some (protectGeneratedTypeName name).getId
        | _ => none
    | _ => none
  let hasSiblingCollision (owner : Ident) (components : Array String) : Bool :=
    let ownerName := owner.getId.eraseMacroScopes
    components.any fun component =>
      declarationNames.contains (ownerName.str component)
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
        let `(messageDec| message $rawName $[$_msgOptions?]? {
            $[$[$_mod]? $_t' $fieldNames = $_fidx
              $[$fieldOptions]? ;]* }) := inner
          | throwUnsupportedSyntax
        let name := protectGeneratedTypeName rawName
        let mut helperComponents := legacyMessageHelperComponents
        for fieldName in fieldNames, optionsStx? in fieldOptions do
          let options := Options.parseD optionsStx?
          if options.default?.isSome then
            let fieldName := fieldName.getId.eraseMacroScopes.toString
            helperComponents :=
              helperComponents.push s!"get_{fieldName}"
                |>.push s!"has_{fieldName}"
        let suppressLegacyHelpers :=
          hasSiblingCollision name helperComponents
        let result ←
          elabMessageDecCore {} oneofs messages localOneofs
            suppressLegacyHelpers inner
        block := block.merge result.declBlock
        messageFields :=
          messageFields.push (result.messageName, result.fieldTags)
    | ``oneofDec => do
        let `(oneofDec| oneof $rawName {
            $[$[$_mod]? $_t' $_n = $_fidx
              $[$_optionsStx]? ;]* }) := inner
          | throwUnsupportedSyntax
        let name := protectGeneratedTypeName rawName
        let suppressLegacyHelpers :=
          hasSiblingCollision name legacyOneofHelperComponents
        let result ←
          elabOneofDecCore {} oneofs messages suppressLegacyHelpers inner
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
