import Protobuf.Encoding.Basic
import Protobuf.Encoding

namespace Protobuf.Encoding

scoped syntax:max (name := hexBytesLiteral) "hex!" str : term

open Lean Elab Meta Term in
@[scoped term_elab hexBytesLiteral]
private def elabHexBytesLiteral : TermElab := fun stx _ => do
  let `(hex! $str) := stx | throwUnsupportedSyntax
  let val := str.getString
  if val.length % 2 = 1 then
    throwErrorAt str "hex bytes literal must have even number of length"
  let cs := val.data.toArray
  for x in cs do
    let r := x.isDigit || (x ≥ 'a' && x ≤ 'f') || (x ≥ 'A' && x ≤ 'F')
    if !r then
      throwErrorAt str "invalid character '{x}'"
  let c2v : Char → UInt8 := fun c =>
    if c.isDigit then
      (c.val - '0'.val).toUInt8
    else if (c ≥ 'a' && c ≤ 'f') then
      (c.val + 10 - 'a'.val).toUInt8
    else
      (c.val + 10 - 'A'.val).toUInt8
  let half := cs.size / 2
  let highs := List.range half |>.map (· * 2) |>.map (c2v cs[·]!)
  let lows := List.range half |>.map (· * 2 + 1) |>.map (c2v cs[·]!)
  let vs := highs.zipWith (ys := lows) fun h l => (h * 16) ||| l
  let u8Type := Expr.const ``UInt8 []
  let es ← vs.mapM fun v => mkNumeral u8Type v.toNat
  let r ← mkArrayLit u8Type es
  return Expr.app (Expr.const ``ByteArray.mk []) r
