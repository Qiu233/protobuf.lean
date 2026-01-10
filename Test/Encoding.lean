module

public import Protobuf.Encoding
public import Binary
meta import Protobuf.Notation
meta import Protobuf.Elab
import Binary.Hex

open Binary
open Protobuf Encoding Notation

local instance : Repr ByteArray where
  reprPrec x p := reprPrec x.data p

#eval Get.run (Binary.getThe Message) hex!"089601" |>.toExcept

#eval Get.run (getThe Message) hex!"0a06616263313233" |>.toExcept

#eval Get.run get_varint ⟨#[0b10010110, 0b00000001]⟩ |>.toExcept

#eval put_varint 150 ⟨#[]⟩

set_option protobuf.trace.descriptor true
set_option protobuf.trace.notation true

#check google.protobuf.Edition.EDITION_2023


#check String.fromUTF8

-- #load_proto_file "Test/tmp_editions_req.proto"
-- #check demo.Foo.encode

message A {
  optional int32 v = 1 [default = 1];
}

extend A {
  optional int32 w = 2 [default = 2];
}

#check A.has_w

#eval A.«Default.Value»
#eval default (α := A)
#eval { : A}
