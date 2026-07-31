module

public import Protobuf.ProtoMessage
public meta import Protobuf.Notation.Message.Metadata
public meta import Protobuf.Notation.Message.Encode
public meta import Protobuf.Notation.Message.DirectEncode
public meta import Protobuf.Notation.Message.Validate
public meta import Protobuf.Notation.Message.Decode
public meta import Protobuf.Notation.Message.Accessors
import Protobuf.Notation.Syntax

public meta section

namespace Protobuf.Notation

open Encoding Notation

open Lean Meta Elab Term Command

structure MessageElabResult where
  messageName : Ident
  fieldTags : Array MessageFieldTagMData
  declBlock : ProtobufDeclBlock

public def elabMessageDecCore
    (mutEnums mutOneofs messages : NameSet)
    (localOneofs : LocalOneofAlternatives) :
    Syntax → CommandElabM MessageElabResult := fun stx => do
  let `(messageDec| message $rawName $[$msgOptions?]? { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let name := protectGeneratedTypeName rawName
  let safeFieldNames := n.map protectGeneratedMemberName
  let msgOptions := Options.parseD msgOptions?
  msgOptions.validate #[]
  let mdata ←
    computeMData mutEnums mutOneofs messages name mod t' safeFieldNames
      fidx optionsStx
  let fieldTags ← validateEmbeddedOneofAlternatives localOneofs mdata
  mdata.forM fun x => do
    if x.oneof_type?.isSome then
      if x.field_num.getNat != 0 then
        throwErrorAt x.field_num "oneof field can only have dummy field number 0, but got {x.field_num.getNat}"
  let defs := mdata.map fun x => x.default_ctor_value
  let struct ← `(structure $name where
    $[$safeFieldNames:ident : $(mdata.map fun x => x.lean_type) := $defs]*
    «Unknown.Fields» : Std.HashMap Nat (Array Encoding.ProtoVal) := {})
  let push_name (component : String) := helperIdent name component
  let (default', default) ← construct_default name push_name mdata
  let inhInst ← `(instance : Inhabited $name := ⟨$default'⟩)
  let (toMessage', toMessage) ← construct_toMessage name push_name mdata
  let directEncoding ←
    constructDirectEncoding name push_name mdata
  let (_, builder) ← construct_builder name push_name toMessage'
  let (_, builderPartial) ←
    construct_builder name push_name (push_name "toMessagePartial") "builderPartial"
  let (fromMessage', fromSpannedChunks', fromMessage) ←
    construct_fromMessage name push_name localOneofs mdata
  let (_, merge) ← construct_merge name push_name mdata
  let requiredValidators ←
    constructMessageRequiredValidator name push_name mdata
  let (_, decoder?) ← construct_decoder? name push_name fromMessage'
  let (_, decoder_rep) ← construct_decoder_rep name push_name fromMessage'
  let defaultAccessors ←
    constructExplicitDefaultAccessors name mdata
  let (encodeId, encode) ←
    constructDirectEncode name push_name directEncoding
  let (decodeId, decode) ←
    construct_decode name push_name fromSpannedChunks'
  let protoMessageInst ←
    `(instance : Protobuf.ProtoMessage $name where
        encode := $encodeId:ident
        decode := $decodeId:ident)
  return {
    messageName := name
    fieldTags
    declBlock := {
      decls := #[struct],
      inhabitedFunctions := #[default],
      inhabitedInsts := #[inhInst],
      encodingFunctions :=
        toMessage ++ directEncoding.commands |>.push builder |>.push builderPartial,
      mergeFunctions := #[merge],
      validationFunctions := requiredValidators,
      decodingFunctions := fromMessage ++ #[decoder?, decoder_rep],
      functions := defaultAccessors ++ #[encode, decode],
      insts := #[protoMessageInst]
    }
  }

@[scoped command_elab messageDec]
public def elabMessageDec : CommandElab := fun stx => do
  let `(messageDec| message $rawName $[$msgOptions?]? { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let name := protectGeneratedTypeName rawName
  let r ← elabMessageDecCore {} {} {name.getId} {} stx
  r.declBlock.elaborate
  registerMessageFieldTags r.messageName r.fieldTags

end Protobuf.Notation
