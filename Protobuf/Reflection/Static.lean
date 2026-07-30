module

public import Protobuf.Reflection.Bootstrap
public import Protobuf.Encoding

public section

namespace Protobuf.Reflection

/-- Associates a statically generated Lean message type with its schema. -/
class ReflectMessage (α : Type) where
  descriptor : MessageDescriptor
  /-- Build wire data without rejecting absent required fields. -/
  toMessagePartial : α → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message
  /-- Decode and validate required fields using the generated static decoder. -/
  fromMessage : Protobuf.Encoding.Message → Except Protobuf.Encoding.ProtoError α

/-- Associates a statically generated Lean enum type with its schema. -/
class ReflectEnum (α : Type) where
  descriptor : EnumDescriptor
  toInt32 : α → Int32
  fromInt32 : Int32 → α

@[inline]
def messageDescriptor (α : Type) [ReflectMessage α] : MessageDescriptor :=
  ReflectMessage.descriptor (α := α)

@[inline]
def enumDescriptor (α : Type) [ReflectEnum α] : EnumDescriptor :=
  ReflectEnum.descriptor (α := α)

end Protobuf.Reflection
