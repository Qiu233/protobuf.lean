module

import Lean.Data.NameTrie
public import Protobuf.Internal.Desc

open System Lean

public section

namespace Protobuf.Versions

open Encoding Notation google.protobuf

protected def packagePrefixRev (pkg : String) : List String :=
  let pkg := pkg.trim
  if pkg.isEmpty then
    []
  else
    (pkg.splitOn ".").reverse

structure M.Context where
  currentMacroScope : Nat := 0
  ref : Syntax := mkNullNode
  currentNamePrefixRev : List String := []

structure M.State where
  nextMacroScope : Nat := 0
  types : NameTrie String := {}

abbrev M := ReaderT M.Context $ StateRefT M.State $ ExceptT String BaseIO

@[inline]
def M.run : M α → Except String α := fun x => (unsafe unsafeBaseIO (x {} |>.run' {}))

@[inline]
def withNamePrefix (prefixRev : List String) (x : M α) : M α := fun c =>
  x { c with currentNamePrefixRev := prefixRev }

protected def nameFromPrefixRev (prefixRev : List String) (raw : String) : Name :=
  let rec go (ns : List String) : Name :=
    match ns with
    | [] => Name.anonymous
    | x :: ns => (go ns).str x
  (go prefixRev).str raw

protected def builtinIdent (s : String) : TSyntax `ident :=
  mkIdent (Name.mkStr1 s)

@[inline]
def wrapName : String → M Name := fun s c =>
  let rec go (ns : List String) : Name :=
    match ns with
    | [] => Name.anonymous
    | x :: ns => (go ns).str x
  return (go c.currentNamePrefixRev).str s

@[specialize]
def withNewNameLevel (n : String) (x : M α) : M α := fun c => x { c with currentNamePrefixRev := n :: c.currentNamePrefixRev }

@[specialize]
def withNewNameLevel? (n : Option String) (x : M α) : M α := fun c =>
  if let some n := n then
    x { c with currentNamePrefixRev := n :: c.currentNamePrefixRev }
  else
    x c

@[specialize]
def withPackageName (n : String) (x : M α) : M α := fun c =>
  let n := n.trim
  let xs := n.splitOn "."
  if xs.isEmpty then
    x c
  else
    x { c with currentNamePrefixRev := xs.reverse ++ c.currentNamePrefixRev }

@[specialize, always_inline]
protected def M.withFreshMacroScope {α} (x : M α) : M α := do
  let fresh ← modifyGetThe M.State (fun st => (st.nextMacroScope, { st with nextMacroScope := st.nextMacroScope + 1 }))
  withReader (fun ctx => { ctx with currentMacroScope := fresh }) x

def resolveName (raw : String) : M Name := do
  -- TODO: fully check string validity
  if raw.isEmpty then
    throw s!"{decl_name%}: input is empty"
  let rec conc (ns : List String) : Name :=
    match ns with
    | [] => Name.anonymous
    | x :: ns => (conc ns).str x
  let leading := raw.rawStartPos.get raw
  if leading == '.' then
    let full := raw.drop 1
    let xs := full.splitOn "."
    return conc xs.reverse
  let name := raw
  let mut ns ← M.Context.currentNamePrefixRev <$> readThe M.Context
  let trie ← M.State.types <$> getThe M.State
  repeat
    let n := conc (name :: ns)
    if let some t := trie.find? n then
      if t == name then
        return n
    if ns.isEmpty then
      break
    ns := ns.tail
  throw s!"{decl_name%}: {raw} cannot be resolved"

def registerType (raw : String) : M Unit := do
  let x ← wrapName raw
  modifyThe M.State (fun s => { s with types := s.types.insert x raw })

def reservedFieldNames : List String :=
  [ "toMessage"
  , "fromMessage"
  , "fromMessage?" -- invalid protobuf name
  , "builder"
  , "merge"
  , "decoder?" -- invalid protobuf name
  , "decoder_rep"
  , "decoder_rep_packed"
  , "Default.Value" -- invalid protobuf name
  , "Unknown.Fields" -- invalid protobuf name
  , "encode"
  , "decode"
  ]

def reservedEnumValueNames : List String :=
  [ "toInt32"
  , "fromInt32"
  , "builder"
  , "decoder?" -- invalid protobuf name
  , "decoder_rep"
  , "decoder_rep_packed"
  , "Default.Value" -- invalid protobuf name
  , "Unknown.Value" -- invalid protobuf name
  ]

def sanitizeFieldName (name : String) : String :=
  if reservedFieldNames.contains name then
    s!"{name}_"
  else
    name

def sanitizeEnumValueName (name : String) : String :=
  if reservedEnumValueNames.contains name then
    s!"{name}_"
  else
    name

def sanitizeFieldDescriptor (field : FieldDescriptorProto) : FieldDescriptorProto :=
  match field.name with
  | some name =>
      let name' := sanitizeFieldName name
      if name' == name then field else { field with name := some name' }
  | none => field

def sanitizeEnumValueDescriptor (value : EnumValueDescriptorProto) : EnumValueDescriptorProto :=
  match value.name with
  | some name =>
      let name' := sanitizeEnumValueName name
      if name' == name then value else { value with name := some name' }
  | none => value

def sanitizeEnumDescriptor (e : EnumDescriptorProto) : EnumDescriptorProto :=
  { e with value := e.value.map sanitizeEnumValueDescriptor }

partial def sanitizeDescriptor (msg : DescriptorProto) : DescriptorProto :=
  { msg with
    field := msg.field.map sanitizeFieldDescriptor
    extension := msg.extension.map sanitizeFieldDescriptor
    nested_type := msg.nested_type.map sanitizeDescriptor
    enum_type := msg.enum_type.map sanitizeEnumDescriptor
  }

def sanitizeFileDescriptor (file : FileDescriptorProto) : FileDescriptorProto :=
  { file with
    message_type := file.message_type.map sanitizeDescriptor
    enum_type := file.enum_type.map sanitizeEnumDescriptor
    extension := file.extension.map sanitizeFieldDescriptor
  }

def sanitizeFileDescriptorSet (desc : FileDescriptorSet) : FileDescriptorSet :=
  { desc with file := desc.file.map sanitizeFileDescriptor }

def checkFieldName (name : String) : M String := do
  return sanitizeFieldName name

def checkEnumValueName (name : String) : M String := do
  return sanitizeEnumValueName name

@[always_inline]
instance : MonadRef M where
  getRef := fun c => return c.ref
  withRef stx x := fun c => x {c with ref := stx}

@[always_inline]
instance : MonadQuotation M where
  getCurrMacroScope := fun c => return c.currentMacroScope
  getContext := return .anonymous
  withFreshMacroScope := M.withFreshMacroScope

scoped macro "get!! " src:term:max " ! " err:term : term =>
  ``(Option.getDM $src (throw s!"{decl_name%}: {$err}"))

scoped macro "get!! " src:term:max : term => ``(Option.getDM $src (throw s!"{decl_name%}"))

scoped macro "is_true!! " v:term:max : term => ``(Option.getD $v false)

open Parser Term in
scoped syntax:min term "&." noWs (fieldIdx <|> rawIdent) argument* : term

scoped macro_rules
  | `($x&.%$tk$f $args*) => `($x >>= (fun x => x |>.%$tk$f $args*))

scoped syntax ppRealGroup(ppRealFill(ppIndent("if! " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

scoped macro_rules
  | `(if! $c then $t else $e) => `(if (Option.getD $c false) then $t else $e)

scoped prefix:min "!! " => Option.getD (dflt := false)
