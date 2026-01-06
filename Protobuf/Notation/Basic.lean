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
When `wired_as_group` is true, the field is **always** wired in the delimited way.

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

-- TODO: maybe force this?
private def Options.recognized : Array Name :=
  #[`packed,
    `deprecated,
    `allow_alias,

    --
    `wired_as_group,
  ]

@[always_inline]
private def Options.zip : Array Ident → Array (TSyntax `options_value) → Options := fun name val =>
  let raw := name.zip val
  let entries := raw.map (fun (x, v) => (x.getId, v)) |>.groupKeyed
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

@[always_inline]
def Options.packed? (options : Options) : Option Bool := options.is_true? `packed

@[always_inline]
def Options.deprecated (options : Options) : Bool := options.is_true? `deprecated |>.getD false

@[always_inline]
def Options.allow_alias? (options : Options) : Option Bool := options.is_true? `allow_alias

@[always_inline]
def Options.wired_as_group? (options : Options) : Option Bool := options.is_true? `wired_as_group

structure ProtobufDeclBlock where
  decls : Array Command := #[]
  inhabitedFunctions : Array Command := #[]
  inhabitedInsts : Array Command := #[]
  functions : Array Command := #[]
  insts : Array Command := #[]
deriving Inhabited, Repr

def ProtobufDeclBlock.elaborate (block : ProtobufDeclBlock) : CommandElabM Unit := do
  let { decls, inhabitedFunctions, inhabitedInsts, functions, insts } := block
  let inhabitedFunctionsMut ← `(mutual
      $inhabitedFunctions:command*
    end)
  let inhabitedInstsMut ← `(mutual
      $inhabitedInsts:command*
    end)
  let functionsMut ← `(mutual
      $functions:command*
    end)
  let instsMut ← `(mutual
      $insts:command*
    end)
  if decls.size == 1 then
    decls.forM elabCommand
  else
    let declMut ← `(mutual
        $decls:command*
      end)
    elabCommand declMut
  elabCommand inhabitedFunctionsMut
  elabCommand inhabitedInstsMut
  elabCommand functionsMut
  elabCommand instsMut

def ProtobufDeclBlock.merge : ProtobufDeclBlock → ProtobufDeclBlock → ProtobufDeclBlock := fun a b =>
  { decls := a.decls ++ b.decls,
    inhabitedFunctions := a.inhabitedFunctions ++ b.inhabitedFunctions,
    inhabitedInsts := a.inhabitedInsts ++ b.inhabitedInsts,
    functions := a.functions ++ b.functions,
    insts := a.insts ++ b.insts }
