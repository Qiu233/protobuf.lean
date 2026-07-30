module

public meta import Protobuf.Notation.Message.Metadata

public meta section

namespace Protobuf.Notation

open Lean Meta Elab Term Command

/--
Generate value and presence accessors for explicit-presence fields with schema
defaults.

The structure projection deliberately remains `Option α`: an absent field has
no presence even though protobuf's value accessor returns the declared default.
Both functions are ordinary statically compiled Lean declarations.
-/
def constructExplicitDefaultAccessors
    (name : Ident) (fields : Array ProtoFieldMData) :
    CommandElabM (Array Command) := do
  let mut out := #[]
  for field in fields do
    let some defaultValue := field.explicit_default? | continue
    unless field.lean_shape == .option do
      continue
    let fieldNameId := field.field_name.getId.eraseMacroScopes
    /-
    A single name component containing `.` cannot originate from any legal
    protobuf identifier, including nested message/type names. This keeps
    generated accessors from conflicting with structure projections.
    -/
    let nestedPrefix :=
      (name.getId.str "Explicit.Default.Accessors").append fieldNameId
    let nestedGetId := mkIdentFrom name (nestedPrefix.str "get")
    let nestedHasId := mkIdentFrom name (nestedPrefix.str "has")
    let msg ← mkIdent <$> mkFreshUserName `msg
    let getCmd ←
      `(def $nestedGetId:ident ($msg : $name) : $(field.lean_type_inner) :=
          ($(field.field_proj) $msg).getD $defaultValue)
    let hasCmd ←
      `(def $nestedHasId:ident ($msg : $name) : Bool :=
          ($(field.field_proj) $msg).isSome)
    out := out.push getCmd |>.push hasCmd
  return out

end Protobuf.Notation
