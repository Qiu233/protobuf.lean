module

public import Protobuf.Encoding
public import Binary
meta import Protobuf.Notation
meta import Protobuf.Elab
import Binary.Hex

open Binary
open Protobuf Encoding Internal Notation

local instance : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

#eval Get.run (Binary.getThe Message) hex!"089601" |>.toExcept

#eval Get.run (getThe Message) hex!"0a06616263313233" |>.toExcept

#eval Get.run get_varint ⟨#[0b10010110, 0b00000001]⟩ |>.toExcept

#eval put_varint 150 ⟨#[]⟩

set_option protobuf.trace.descriptor true
set_option protobuf.trace.notation true

-- #load_proto_file "Test/B.proto"
#load_proto_file "Test/official/google/protobuf/descriptor.proto"

#check google.protobuf.Edition.EDITION_2023
