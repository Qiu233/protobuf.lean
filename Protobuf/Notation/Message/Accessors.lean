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
    (name : Ident) (fields : Array ProtoFieldMData)
    (legacyHelpers : Bool := true) :
    CommandElabM (Array Command) := do
  let mut out := #[]
  for field in fields do
    let some defaultValue := field.explicit_default? | continue
    unless field.lean_shape == .option do
      continue
    let fieldNameId := field.field_name.getId.eraseMacroScopes
    let fieldName := fieldNameId.toString
    /-
    The nested names are the collision-free, stable API.  A protobuf schema is
    allowed to contain fields named `get_foo` and `has_foo` next to a field
    `foo` with an explicit default.  Such projections occupy `Message.get_foo`
    and `Message.has_foo`, so unconditional flat accessors made valid schemas
    fail Lean elaboration.

    Keep the historical flat spellings when they are available, but always
    emit accessors below a namespace path that cannot conflict with a sibling
    structure projection.
    -/
    -- A single name component containing `.` cannot originate from any legal
    -- protobuf identifier, including nested message/type names.
    let nestedPrefix :=
      (name.getId.str "Explicit.Default.Accessors").append fieldNameId
    let nestedGetId := mkIdentFrom name (nestedPrefix.str "get")
    let nestedHasId := mkIdentFrom name (nestedPrefix.str "has")
    /-
    These two spellings are compatibility aliases, not canonical helpers.
    Construct them directly below the message namespace instead of using
    `pushName`, which now deliberately targets `«protobuf.internal»`.
    -/
    let getId :=
      mkIdentFrom name (name.getId.str s!"get_{fieldName}")
    let hasId :=
      mkIdentFrom name (name.getId.str s!"has_{fieldName}")
    let projectionNames := fields.map (·.field_proj.getId.eraseMacroScopes)
    let msg ← mkIdent <$> mkFreshUserName `msg
    let getCmd ←
      `(def $nestedGetId:ident ($msg : $name) : $(field.lean_type_inner) :=
          ($(field.field_proj) $msg).getD $defaultValue)
    let hasCmd ←
      `(def $nestedHasId:ident ($msg : $name) : Bool :=
          ($(field.field_proj) $msg).isSome)
    out := out.push getCmd |>.push hasCmd
    if legacyHelpers &&
        !projectionNames.contains getId.getId.eraseMacroScopes then
      out := out.push (←
        `(def $getId:ident ($msg : $name) : $(field.lean_type_inner) :=
            $nestedGetId:ident $msg))
    if legacyHelpers &&
        !projectionNames.contains hasId.getId.eraseMacroScopes then
      out := out.push (←
        `(def $hasId:ident ($msg : $name) : Bool :=
            $nestedHasId:ident $msg))
  return out

end Protobuf.Notation
