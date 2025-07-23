import Protobuf.Encoding
import Protobuf.Encoding.Pretty
-- import Protobuf.Class

namespace Protobuf

open Protobuf.Encoding
open Binary

#eval Get.run (getThe Message) hex!"089601" |>.toExcept

#eval Get.run (getThe Message) hex!"0a06616263313233" |>.toExcept

#eval Get.run get_varint ⟨#[0b10010110, 0b00000001]⟩ |>.toExcept

#eval Put.run 128 <| put_varint 150

#eval Put.run 128 <| put_varint (-2 : Int64).toUInt64.toNat

#eval ((0x7FFFFFFF : Int32) <<< 1).xor ((0x7FFFFFFF : Int32) >>> 31)


#check Lean.Name.toString



structure A where
  a : Int32
  b : Option String
deriving Inhabited


open AuxNotation in
instance : ProtoMessage A where
  encode x := do
    encode_sint32 0 x.a
    x.b.forM (encode_string 1)
  decode := do
    let a ← checked% ``A.a decode_sint32 at 0
    let b ← checked% ``A.b decode_string? at 1
    return { a := a, b := b }

run_meta do
  let s ← `(a)
  let t ← `($(s).b)
  println! "{t}"
