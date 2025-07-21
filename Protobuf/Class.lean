import Protobuf.Encoding

namespace Protobuf

class ProtoMessage (α : Type) where
  encode : α → Encoding.Message
  decode : Encoding.Message → Except String α
