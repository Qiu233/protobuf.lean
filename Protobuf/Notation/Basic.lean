module

public import Lean
import Protobuf.Utils
import Protobuf.Notation.Syntax


/-!
# DESIGN NOTE

The Lean side meta-programming based protobuf language (we may call it *proto-lean*) is non-standard.

*proto-lean* is protobuf version-invariant and edition-invariant, that is, who writes *proto-lean* code
  is responsible to decide the specifics.
A typical "writer" is a protoc plugin which targets Lean 4 as the host language.

Nevertheless, we still provide this happy path to define immediate messages
  without needing to fall back to the encoding/decoding primitives.

## There are no nested declarations
Instead, we flatten all declaration to the top level (in the sense of Lean 4).

## Qualified names are allowed at declaration places

2. Options are not set inside the declaration body
Options setting block is adjacent to the declaration name, like
```
message A [...] {
  ...
}
```

3. Semantics of options are not the same as protobuf standard
We use options to instruct the very specific behavior of the stuff.

For example, when `packed` is true, we **always** generate seralizing code which
  **always** serializes that field in the packed wire format.

`wired_as_group = true` selects the legacy start-group/end-group wire
representation for a message-valued field.  Version frontends synthesize it
for proto2 `group` declarations and Editions `message_encoding = DELIMITED`;
the generated Lean declarations remain ordinary statically typed messages.

-/


public section

open Lean Meta Elab Term Command

namespace Protobuf.Notation

meta def mkFreshUserName (n : Name) : CommandElabM Name := do
  withFreshMacroScope do
    MonadQuotation.addMacroScope n

structure Options where
  raw : Array (Ident × TSyntax `options_value)
  entries : Std.HashMap Name (Array (TSyntax `options_value))
deriving Inhabited, Repr

private def Options.recognized : Array Name :=
  #[`packed,
    `deprecated,
    `allow_alias,
    `closed,

    --
    `wired_as_group,
    `default,

    -- Descriptor-schema annotations carried by the checked-in
    -- `google.protobuf.descriptor` notation.  They do not affect wire code,
    -- but are legitimate repeated/source-retention metadata rather than
    -- generator controls.
    `retention,
    `targets,
  ]

private def Options.boolean : Array Name :=
  #[`packed, `deprecated, `allow_alias, `closed, `wired_as_group]

private def Options.repeatable : Array Name :=
  #[`targets]

@[always_inline]
private def Options.zip : Array Ident → Array (TSyntax `options_value) → Options := fun name val =>
  let raw := name.zip val
  -- Options synthesized from descriptors carry fresh macro scopes.  Option
  -- names are schema keys, not hygienic Lean bindings, so normalize them
  -- before lookup (`default` in particular otherwise becomes `default✝` and
  -- is silently missed).
  let entries :=
    raw.map (fun (x, v) => (x.getId.eraseMacroScopes, v)) |>.groupKeyed
  { raw, entries }

@[always_inline]
local instance : GetElem? Options Name (Array (TSyntax `options_value)) (fun options name => name ∈ options.entries) where
  getElem xs i h := xs.entries[i]
  getElem? xs i := xs.entries[i]?

@[always_inline]
private def Options.first? (options : Options) (x : Name) : Option (TSyntax `options_value) :=
  if let some xs := options[x]? then
    xs[0]?
  else
    none

@[always_inline]
private def Options.is_true? (options : Options) (x : Name) : Option Bool :=
  if let some y := options.first? x then
    y matches `(options_value| true)
  else none

@[always_inline]
def Options.parse : TSyntax ``options → Options
  | `(options| [ $[$name = $val],* ]) => Options.zip name val
  | _ => unreachable!

@[always_inline]
def Options.parseD : Option (TSyntax ``options) → Options
  | some s =>
    match s with
    | `(options| [ $[$name = $val],* ]) => Options.zip name val
    | _ => unreachable!
  | none => default

/--
Validate notation options while the schema is being elaborated.

The notation layer is a compile-time schema compiler.  Silently accepting a
misspelled or inapplicable option would otherwise defer the failure to generated
runtime code (and `packed` on a non-packable field used to reach an assertion in
the encoder).
-/
def Options.validate
    [Monad m] [MonadError m] [MonadRef m] [AddMessageContext m]
    (options : Options) (allowed : Array Name) : m Unit := do
  let mut seen : Array Name := #[]
  for (nameStx, value) in options.raw do
    let name := nameStx.getId.eraseMacroScopes
    unless Options.recognized.contains name do
      throwErrorAt nameStx "unknown protobuf notation option `{name}`"
    unless allowed.contains name do
      throwErrorAt nameStx "protobuf notation option `{name}` is not valid in this context"
    if seen.contains name && !Options.repeatable.contains name then
      throwErrorAt nameStx "protobuf notation option `{name}` is specified more than once"
    seen := seen.push name
    if Options.boolean.contains name then
      let isBoolean :=
        (value matches `(options_value| true)) ||
        (value matches `(options_value| false))
      unless isBoolean do
        throwErrorAt value "protobuf notation option `{name}` expects `true` or `false`"

@[always_inline]
def Options.packed? (options : Options) : Option Bool := options.is_true? `packed

@[always_inline]
def Options.deprecated (options : Options) : Bool := options.is_true? `deprecated |>.getD false

@[always_inline]
def Options.allow_alias? (options : Options) : Option Bool := options.is_true? `allow_alias

@[always_inline]
def Options.closed (options : Options) : Bool := options.is_true? `closed |>.getD false

@[always_inline]
def Options.wired_as_group? (options : Options) : Option Bool := options.is_true? `wired_as_group

@[always_inline]
def Options.default? (options : Options) : Option (TSyntax `options_value) := options.first? `default

/--
The namespace component containing statically generated protobuf helpers.

A valid protobuf simple identifier cannot contain `.`, so storing the dot in
one `Name.str` component makes this namespace disjoint from every schema name.
-/
def helperNamespaceComponent : String := "protobuf.internal"

@[inline]
def helperNamespaceName (typeName : Name) : Name :=
  /-
  Proto-lean quotations attach macro scopes to schema identifiers.  Those
  scopes belong to the identifier as a whole, so appending helper components
  after them produces names such as
  `Message.<macro-scope>.«protobuf.internal».encode`.  In particular, a
  qualified type reference inside a generated mutual block can then resolve
  through the wrong prefix.  Protobuf schema names are deliberately
  non-hygienic (and are already printed/resolved as such), so normalize the
  type name before extending it.
  -/
  typeName.eraseMacroScopes.str helperNamespaceComponent

@[inline]
def helperName (typeName : Name) (component : String) : Name :=
  (helperNamespaceName typeName).str component

@[inline]
def helperIdent (typeId : Ident) (component : String) : Ident :=
  mkIdentFrom typeId (helperName typeId.getId component)

/--
Lean members synthesized for every generated structure/inductive.

Direct proto-lean notation does not pass through descriptor sanitization, so a
legal field, enum value, or oneof alternative such as `mk`, `rec`, or
`casesOn` must be moved to one impossible name component before elaboration.
-/
def leanGeneratedMemberNames : Array String :=
  #["mk", "rec", "recOn", "casesOn", "below", "brecOn", "noConfusion",
    "noConfusionType", "ctorIdx", "ctorElim", "ctorElimType", "_sizeOf_1",
    "_sizeOf_inst"]

def protectGeneratedMemberName (member : Ident) : Ident :=
  match member.getId.eraseMacroScopes with
  | .str .anonymous raw =>
      if leanGeneratedMemberNames.contains raw then
        mkIdentFrom member (Name.mkStr1 s!"{raw}.protobuf")
      else
        member
  | _ => member

/--
Protect a protobuf type declaration/reference whose final component collides
with a member Lean synthesizes for the enclosing inductive or structure.

Unlike field syntax, type names may be qualified (`Outer.rec`).  Normalize
macro scopes first and replace only the final schema component, keeping
declarations and references on the same collision-proof spelling.
-/
def protectGeneratedTypeName (typeId : Ident) : Ident :=
  let normalized := typeId.getId.eraseMacroScopes
  match normalized with
  | .str parent raw =>
      if leanGeneratedMemberNames.contains raw then
        mkIdentFrom typeId (parent.str s!"{raw}.protobuf")
      else
        mkIdentFrom typeId normalized
  | _ => mkIdentFrom typeId normalized

structure ProtobufDeclBlock where
  decls : Array Command := #[]
  inhabitedFunctions : Array Command := #[]
  inhabitedInsts : Array Command := #[]
  /--
  The mutually recursive wire-building core (`toMessage`/`builder`).

  These declarations can recurse across every message in a protobuf type SCC,
  but do not depend on the decoding core.
  -/
  encodingFunctions : Array Command := #[]
  /--
  The mutually recursive structural merge core.

  Message merges can recurse through an entire type SCC, but they do not call
  any decoder. Elaborating them first keeps them out of the larger
  `fromMessage`/`decoder?` mutual block.
  -/
  mergeFunctions : Array Command := #[]
  /--
  The mutually recursive wire-decoding core
  (`fromMessage`/`decoder?` and oneof decoding).

  Keeping this separate from `encodingFunctions` prevents a recursive protobuf
  SCC from becoming one unnecessarily large Lean `mutual` definition.
  -/
  decodingFunctions : Array Command := #[]
  /--
  Non-recursive wrappers whose dependencies have already been elaborated, such
  as `encode` and `decode`.
  -/
  functions : Array Command := #[]
  insts : Array Command := #[]
deriving Inhabited, Repr

def ProtobufDeclBlock.elaborate (block : ProtobufDeclBlock) : CommandElabM Unit := do
  let {
    decls,
    inhabitedFunctions,
    inhabitedInsts,
    encodingFunctions,
    mergeFunctions,
    decodingFunctions,
    functions,
    insts
  } := block
  let elaborateMutual (commands : Array Command) : CommandElabM Unit := do
    unless commands.isEmpty do
      let command ← `(mutual
          $commands:command*
        end)
      elabCommand command
  /-
  Lean's automatically generated `SizeOf` specification proofs are
  particularly expensive for a mutually recursive protobuf SCC containing a
  wide message: they expand a size expression for every field through every
  member of the SCC. Keep the ordinary `SizeOf` instance available to users,
  but omit its unused constructor-equation theorems from generated protobuf
  declarations.
  -/
  if decls.size == 1 then
    for decl in decls do
      let command ← `(set_option genSizeOfSpec false in
          $decl:command)
      elabCommand command
  else if !decls.isEmpty then
    let declMut ← `(set_option genSizeOfSpec false in
        mutual
          $decls:command*
        end)
    elabCommand declMut
  inhabitedFunctions.forM elabCommand
  inhabitedInsts.forM elabCommand
  elaborateMutual encodingFunctions
  elaborateMutual mergeFunctions
  elaborateMutual decodingFunctions
  functions.forM elabCommand
  insts.forM elabCommand

def ProtobufDeclBlock.merge : ProtobufDeclBlock → ProtobufDeclBlock → ProtobufDeclBlock := fun a b =>
  { decls := a.decls ++ b.decls,
    inhabitedFunctions := a.inhabitedFunctions ++ b.inhabitedFunctions,
    inhabitedInsts := a.inhabitedInsts ++ b.inhabitedInsts,
    encodingFunctions := a.encodingFunctions ++ b.encodingFunctions,
    mergeFunctions := a.mergeFunctions ++ b.mergeFunctions,
    decodingFunctions := a.decodingFunctions ++ b.decodingFunctions,
    functions := a.functions ++ b.functions,
    insts := a.insts ++ b.insts }
