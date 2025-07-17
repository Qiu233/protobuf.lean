import Protobuf.Encoding
import Protobuf.Encoding.Pretty

open Protobuf.Encoding
open Binary

#eval Get.run (getThe Message) hex!"089601" |>.toExcept

#eval Get.run (getThe Message) hex!"0a06616263313233" |>.toExcept

#eval Get.run get_varint ⟨#[0b10010110, 0b00000001]⟩ |>.toExcept

#eval put_varint 150 ⟨#[]⟩
