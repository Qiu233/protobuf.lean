module

public import Protobuf.Encoding
public import Binary
import Binary.Hex

open Binary
open Protobuf Encoding

local instance : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

#eval Get.run (Binary.getThe Message) hex!"089601" |>.toExcept

#eval Get.run (getThe Message) hex!"0a06616263313233" |>.toExcept

#eval Get.run get_varint ⟨#[0b10010110, 0b00000001]⟩ |>.toExcept

#eval put_varint 150 ⟨#[]⟩
