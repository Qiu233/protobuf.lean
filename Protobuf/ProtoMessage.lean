module

public import Protobuf.Encoding


public section

namespace Protobuf

/-- Binary protobuf encoding and decoding for a generated message type. -/
class ProtoMessage (α : Type u) where
  encode : α → Except Encoding.ProtoError ByteArray
  decode : ByteArray → Except Encoding.ProtoError α

export ProtoMessage (encode decode)

/--
Decode a binary protobuf value while specifying its result type positionally.
-/
@[always_inline]
def decodeThe (α : Type u) [ProtoMessage α]
    (input : ByteArray) : Except Encoding.ProtoError α :=
  decode input

end Protobuf
