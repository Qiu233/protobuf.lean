import Protobuf.Encoding.Basic
import Protobuf.Encoding
import Protobuf.Encoding.Notation

namespace Protobuf.Encoding

def _root_.ByteArray.toHexLiteral (arr : ByteArray) (lower : Bool := false) : String :=
  let b2c : UInt8 → Char := fun x =>
    if x < 10 then
      Char.ofUInt8 (x + '0'.toUInt8)
    else
      Char.ofUInt8 (x - 10 + if lower then 'a'.toUInt8 else 'A'.toUInt8)
  let b2h : UInt8 → List Char := fun x =>
    let high := x / 16
    let low := x % 16
    [b2c high, b2c low]
  let s := arr.data.toList.map b2h |>.flatMap id
  String.mk s

scoped instance : Repr ByteArray where
  reprPrec x _ := s!"hex!\"{x.toHexLiteral}\""
