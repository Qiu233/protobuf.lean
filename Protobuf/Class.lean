import Protobuf.Encoding

namespace Protobuf

class Default (α : Type) [BEq α] where
  pdefault : α
  isDefault : α → Bool := fun x => x == pdefault

export Default (pdefault)

class ProtoMessage (α : Type) where
  encode : α → Encoding.Message
  decode : Encoding.Message → Except String α
