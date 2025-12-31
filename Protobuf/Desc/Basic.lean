module

public import Lean

open Lean Meta Elab Term Command

namespace Protobuf.Desc

public meta def mkFreshUserName (n : Name) : CommandElabM Name := do
  withFreshMacroScope do
    MonadQuotation.addMacroScope n
