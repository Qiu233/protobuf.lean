module

public import Protobuf.Reflection.Static
public import Protobuf.Encoding

public section

namespace Protobuf.Reflection

open google.protobuf Protobuf.Encoding

inductive ReflectionError where
  | staleDescriptor (fullName : String)
  | wrongContainingType (fieldName messageName : String)
  | unresolvedMessageType (fullName : String)
  | unresolvedEnumType (fullName : String)
  | invalidFieldDescriptor (fieldName detail : String)
  | expectedSingular (fieldName : String)
  | expectedRepeated (fieldName : String)
  | wrongValueType (fieldName expected : String)
  | unknownClosedEnumValue (enumName : String) (number : Int32)
  | wire (error : ProtoError)
deriving Repr

instance : ToString ReflectionError where
  toString
    | .staleDescriptor name => s!"descriptor `{name}` is not present in its pool"
    | .wrongContainingType fieldName messageName =>
        s!"field `{fieldName}` does not belong to message `{messageName}`"
    | .unresolvedMessageType name => s!"message type `{name}` is not registered"
    | .unresolvedEnumType name => s!"enum type `{name}` is not registered"
    | .invalidFieldDescriptor name detail =>
        s!"invalid descriptor for field `{name}`: {detail}"
    | .expectedSingular name => s!"field `{name}` is repeated"
    | .expectedRepeated name => s!"field `{name}` is singular"
    | .wrongValueType name expected =>
        s!"value for field `{name}` is not a protobuf {expected}"
    | .unknownClosedEnumValue name number =>
        s!"{number} is not declared by closed enum `{name}`"
    | .wire error => error.toString

/--
A schema-aware value used by dynamic reflection.

Strings retain their bytes. Call `UnvalidatedString.toString?` when the
field's UTF-8 policy requires a Lean `String`.
-/
inductive Value where
  | int32 (value : Int32)
  | int64 (value : Int64)
  | uint32 (value : UInt32)
  | uint64 (value : UInt64)
  | bool (value : Bool)
  | string (value : Protobuf.UnvalidatedString)
  | bytes (value : ByteArray)
  | float (value : Float32)
  | double (value : Float)
  | enum (descriptor : EnumDescriptor) (number : Int32)
  | message (descriptor : MessageDescriptor) (wire : Encoding.Message)
deriving Inhabited

structure DynamicMessage where
  descriptor : MessageDescriptor
  wire : Encoding.Message := .empty
deriving Inhabited

/--
An explicit source of extensions. No process-global extension registration is
consulted unless the caller chooses the generated pool's resolver.
-/
structure ExtensionResolver where
  findExtensionByNumber :
    MessageDescriptor → Int32 → IO (Option FieldDescriptor)

def DescriptorPool.extensionResolver (pool : DescriptorPool) :
    ExtensionResolver where
  findExtensionByNumber extendee number :=
    pool.findExtensionByNumber extendee number

def generatedExtensionResolver : ExtensionResolver :=
  generatedPool.extensionResolver

private abbrev RM := ExceptT ReflectionError IO

private def liftWire (result : Except ProtoError α) : RM α :=
  match result with
  | .ok value => pure value
  | .error error => throw (.wire error)

private def normalizeFullName (name : String) : String :=
  name.dropPrefix "." |>.toString

private def fieldProto (field : FieldDescriptor) : RM FieldDescriptorProto := do
  let some proto ← field.toProto
    | throw (.staleDescriptor field.fullName)
  return proto

private def fieldNumber (field : FieldDescriptor) (proto : FieldDescriptorProto) :
    RM Nat := do
  let some number := proto.number
    | throw (.invalidFieldDescriptor field.fullName "field number is absent")
  if number <= 0 then
    throw (.invalidFieldDescriptor field.fullName
      s!"field number {number} is not positive")
  return number.toInt.toNat

private def fieldType (field : FieldDescriptor) :
    RM FieldDescriptorProto.Type := do
  let some type ← field.effectiveWireType
    | throw (.invalidFieldDescriptor field.fullName "field type is absent")
  return type

private def isRepeated (proto : FieldDescriptorProto) : Bool :=
  proto.label == some .LABEL_REPEATED

private def checkContainingType
    (message : DynamicMessage) (field : FieldDescriptor)
    (proto : FieldDescriptorProto) : RM Unit := do
  if proto.extendee.isSome then
    let expected := normalizeFullName proto.extendee.get!
    if !(← field.pool.isBasedOn message.descriptor.pool) ||
        expected != message.descriptor.fullName then
      throw (.wrongContainingType field.fullName message.descriptor.fullName)
  else
    let some containing ← field.containingMessage
      | throw (.invalidFieldDescriptor field.fullName
          "ordinary field has no containing message")
    if containing != message.descriptor then
      throw (.wrongContainingType field.fullName message.descriptor.fullName)

private def resolveMessage
    (field : FieldDescriptor) (proto : FieldDescriptorProto) :
    RM MessageDescriptor := do
  let some raw := proto.type_name
    | throw (.invalidFieldDescriptor field.fullName "message type_name is absent")
  let name := normalizeFullName raw
  let some descriptor ← field.pool.findMessageByName name
    | throw (.unresolvedMessageType name)
  return descriptor

private def resolveEnum
    (field : FieldDescriptor) (proto : FieldDescriptorProto) :
    RM EnumDescriptor := do
  let some raw := proto.type_name
    | throw (.invalidFieldDescriptor field.fullName "enum type_name is absent")
  let name := normalizeFullName raw
  let some descriptor ← field.pool.findEnumByName name
    | throw (.unresolvedEnumType name)
  return descriptor

private def singularArray (value : Option α) : Array α :=
  value.map (#[·]) |>.getD #[]

private def isVarintType : FieldDescriptorProto.Type → Bool
  | .TYPE_INT32 | .TYPE_INT64 | .TYPE_UINT32 | .TYPE_UINT64
  | .TYPE_SINT32 | .TYPE_SINT64 | .TYPE_BOOL | .TYPE_ENUM => true
  | _ => false

private def isI64Type : FieldDescriptorProto.Type → Bool
  | .TYPE_FIXED64 | .TYPE_SFIXED64 | .TYPE_DOUBLE => true
  | _ => false

private def isI32Type : FieldDescriptorProto.Type → Bool
  | .TYPE_FIXED32 | .TYPE_SFIXED32 | .TYPE_FLOAT => true
  | _ => false

private def wireValueCompatible
    (type : FieldDescriptorProto.Type) (repeated : Bool)
    (value : ProtoVal) : Bool :=
  match value with
  | .VARINT _ => isVarintType type
  | .I64 _ => isI64Type type
  | .I32 _ => isI32Type type
  | .GROUPED _ => type == .TYPE_GROUP
  | .LEN _ =>
      type == .TYPE_STRING || type == .TYPE_BYTES || type == .TYPE_MESSAGE ||
        (repeated && (isVarintType type || isI64Type type || isI32Type type))

private def valueActivatesOneofField
    (field : FieldDescriptor) (proto : FieldDescriptorProto)
    (value : ProtoVal) : RM Bool := do
  let type ← fieldType field
  if !wireValueCompatible type false value then
    return false
  if type != .TYPE_ENUM then
    return true
  let enum ← resolveEnum field proto
  if !(← enum.isClosed).getD false then
    return true
  let some raw := value.isVARINT? | return false
  let number := Int32.ofBitVec (UInt32.ofNat raw).toBitVec
  return (← enum.findValueByNumber number).isSome

private inductive OneofReadWindow where
  | ordinary
  | inactive
  | active (start : Nat)

/--
Find the portion of the wire that contributes to one member of a oneof.

A later, valid sibling clears an earlier member. Repeated occurrences of the
same message member merge only until a different sibling becomes active.
Wrong-wire records and unknown values of closed enums remain unknown data and
do not select a oneof case.
-/
private def oneofReadWindow
    (message : DynamicMessage) (field : FieldDescriptor)
    (proto : FieldDescriptorProto) : RM OneofReadWindow := do
  let some oneofIndex := proto.oneof_index | return .ordinary
  let some containing ← field.containingMessage
    | throw (.invalidFieldDescriptor field.fullName
        "oneof field has no containing message")
  let fields ← containing.fields
  let mut siblings : Array
      (FieldDescriptor × FieldDescriptorProto × Nat) := #[]
  for sibling in fields do
    let siblingProto ← fieldProto sibling
    if siblingProto.oneof_index == some oneofIndex then
      siblings := siblings.push
        (sibling, siblingProto, ← fieldNumber sibling siblingProto)
  let mut targetActive := false
  let mut targetStart := 0
  for index in [:message.wire.records.size] do
    let record := message.wire.records[index]!
    for (sibling, siblingProto, siblingNumber) in siblings do
      if record.fieldNum == siblingNumber &&
          (← valueActivatesOneofField sibling siblingProto record.value) then
        if sibling == field then
          if !targetActive then
            targetStart := index
          targetActive := true
        else
          targetActive := false
  if targetActive then
    return .active targetStart
  return .inactive

private def decodeEnumValues
    (message : DynamicMessage) (field : FieldDescriptor)
    (proto : FieldDescriptorProto) (number : Nat) (repeated : Bool) :
    RM (Array Value) := do
  let enum ← resolveEnum field proto
  let raw ←
    if repeated then
      liftWire (message.wire.getRepeatedVarint_int32 number)
    else
      liftWire (message.wire.getExpandedVarint_int32 number)
  let closed := (← enum.isClosed).getD false
  let mut out := #[]
  for value in raw do
    if closed && (← enum.findValueByNumber value).isNone then
      continue
    out := out.push (.enum enum value)
  if repeated then
    return out
  return out.back?.map (#[·]) |>.getD #[]

private def decodeValues
    (message : DynamicMessage) (field : FieldDescriptor)
    (proto : FieldDescriptorProto) : RM (Array Value) := do
  let message ←
    match ← oneofReadWindow message field proto with
    | .ordinary => pure message
    | .inactive => pure { message with wire := .empty }
    | .active start =>
        pure { message with
          wire := {
            records := message.wire.records.extract
              start message.wire.records.size
          }
        }
  let number ← fieldNumber field proto
  let type ← fieldType field
  let repeated := isRepeated proto
  let compatibleWire : Encoding.Message := {
    records := message.wire.records.filter fun record =>
      record.fieldNum != number ||
        wireValueCompatible type repeated record.value
  }
  let message := { message with wire := compatibleWire }
  match type with
  | .TYPE_DOUBLE =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedI64_double number)).map .double
      else
        return singularArray (← liftWire
          (message.wire.getI64_double? number)) |>.map .double
  | .TYPE_FLOAT =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedI32_float number)).map .float
      else
        return singularArray (← liftWire
          (message.wire.getI32_float? number)) |>.map .float
  | .TYPE_INT64 =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedVarint_int64 number)).map .int64
      else
        return singularArray (← liftWire
          (message.wire.getVarint_int64? number)) |>.map .int64
  | .TYPE_UINT64 =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedVarint_uint64 number)).map .uint64
      else
        return singularArray (← liftWire
          (message.wire.getVarint_uint64? number)) |>.map .uint64
  | .TYPE_INT32 =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedVarint_int32 number)).map .int32
      else
        return singularArray (← liftWire
          (message.wire.getVarint_int32? number)) |>.map .int32
  | .TYPE_FIXED64 =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedI64_fixed64 number)).map .uint64
      else
        return singularArray (← liftWire
          (message.wire.getI64_fixed64? number)) |>.map .uint64
  | .TYPE_FIXED32 =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedI32_fixed32 number)).map .uint32
      else
        return singularArray (← liftWire
          (message.wire.getI32_fixed32? number)) |>.map .uint32
  | .TYPE_BOOL =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedBool number)).map .bool
      else
        return singularArray (← liftWire
          (message.wire.getBool? number)) |>.map .bool
  | .TYPE_STRING =>
      if repeated then
        return (← liftWire
          (message.wire.getExpandedUnvalidatedString number)).map .string
      else
        return singularArray (← liftWire
          (message.wire.getUnvalidatedString? number)) |>.map .string
  | .TYPE_GROUP =>
      let child ← resolveMessage field proto
      if repeated then
        return (← liftWire (message.wire.getExpandedGroup number)).map
          (.message child ·)
      else
        let occurrences ← liftWire (message.wire.getExpandedGroup number)
        if occurrences.isEmpty then
          return #[]
        return #[.message child
          (occurrences.foldl (init := .empty) Encoding.Message.combine)]
  | .TYPE_MESSAGE =>
      let child ← resolveMessage field proto
      let occurrences ← liftWire (message.wire.getExpandedMessage number)
      if repeated then
        return occurrences.map (.message child ·)
      else if occurrences.isEmpty then
        return #[]
      else
        return #[.message child
          (occurrences.foldl (init := .empty) Encoding.Message.combine)]
  | .TYPE_BYTES =>
      if repeated then
        return (← liftWire (message.wire.getExpandedBytes number)).map .bytes
      else
        return singularArray (← liftWire
          (message.wire.getBytes? number)) |>.map .bytes
  | .TYPE_UINT32 =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedVarint_uint32 number)).map .uint32
      else
        return singularArray (← liftWire
          (message.wire.getVarint_uint32? number)) |>.map .uint32
  | .TYPE_ENUM =>
      decodeEnumValues message field proto number repeated
  | .TYPE_SFIXED32 =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedI32_sfixed32 number)).map .int32
      else
        return singularArray (← liftWire
          (message.wire.getI32_sfixed32? number)) |>.map .int32
  | .TYPE_SFIXED64 =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedI64_sfixed64 number)).map .int64
      else
        return singularArray (← liftWire
          (message.wire.getI64_sfixed64? number)) |>.map .int64
  | .TYPE_SINT32 =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedVarint_sint32 number)).map .int32
      else
        return singularArray (← liftWire
          (message.wire.getVarint_sint32? number)) |>.map .int32
  | .TYPE_SINT64 =>
      if repeated then
        return (← liftWire (message.wire.getRepeatedVarint_sint64 number)).map .int64
      else
        return singularArray (← liftWire
          (message.wire.getVarint_sint64? number)) |>.map .int64
  | .«Unknown.Value» value =>
      throw (.invalidFieldDescriptor field.fullName
        s!"unknown field type number {value}")

/--
Return the values physically present on the wire.

For a singular scalar the result has zero or one element; singular message
occurrences are merged. Repeated packable fields accept both packed and
expanded encodings. Unknown numeric values of a closed enum are omitted and
remain in the raw message as unknown data.
-/
def DynamicMessage.presentValues
    (message : DynamicMessage) (field : FieldDescriptor) :
    IO (Except ReflectionError (Array Value)) :=
  (do
    let proto ← fieldProto field
    checkContainingType message field proto
    decodeValues message field proto).run

def DynamicMessage.getSingular?
    (message : DynamicMessage) (field : FieldDescriptor) :
    IO (Except ReflectionError (Option Value)) :=
  (do
    let proto ← fieldProto field
    checkContainingType message field proto
    if isRepeated proto then
      throw (ReflectionError.expectedSingular field.fullName)
    let values ← decodeValues message field proto
    return values[0]?).run

def DynamicMessage.getRepeated
    (message : DynamicMessage) (field : FieldDescriptor) :
    IO (Except ReflectionError (Array Value)) :=
  (do
    let proto ← fieldProto field
    checkContainingType message field proto
    unless isRepeated proto do
      throw (ReflectionError.expectedRepeated field.fullName)
    decodeValues message field proto).run

private def encodeValue
    (field : FieldDescriptor) (proto : FieldDescriptorProto)
    (type : FieldDescriptorProto.Type) (value : Value) : RM ProtoVal := do
  match type, value with
  | .TYPE_DOUBLE, .double value => liftWire (ProtoVal.ofI64_double value)
  | .TYPE_FLOAT, .float value => liftWire (ProtoVal.ofI32_float value)
  | .TYPE_INT64, .int64 value => liftWire (ProtoVal.ofVarint_int64 value)
  | .TYPE_UINT64, .uint64 value => liftWire (ProtoVal.ofVarint_uint64 value)
  | .TYPE_INT32, .int32 value => liftWire (ProtoVal.ofVarint_int32 value)
  | .TYPE_FIXED64, .uint64 value => liftWire (ProtoVal.ofI64_fixed64 value)
  | .TYPE_FIXED32, .uint32 value => liftWire (ProtoVal.ofI32_fixed32 value)
  | .TYPE_BOOL, .bool value => liftWire (ProtoVal.ofBool value)
  | .TYPE_STRING, .string value => liftWire (ProtoVal.ofUnvalidatedString value)
  | .TYPE_BYTES, .bytes value => liftWire (ProtoVal.ofBytes value)
  | .TYPE_UINT32, .uint32 value => liftWire (ProtoVal.ofVarint_uint32 value)
  | .TYPE_SFIXED32, .int32 value => liftWire (ProtoVal.ofI32_sfixed32 value)
  | .TYPE_SFIXED64, .int64 value => liftWire (ProtoVal.ofI64_sfixed64 value)
  | .TYPE_SINT32, .int32 value => liftWire (ProtoVal.ofVarint_sint32 value)
  | .TYPE_SINT64, .int64 value => liftWire (ProtoVal.ofVarint_sint64 value)
  | .TYPE_ENUM, .enum descriptor number =>
      let expected ← resolveEnum field proto
      if descriptor != expected then
        throw (.wrongValueType field.fullName s!"enum `{expected.fullName}`")
      if (← expected.isClosed).getD false &&
          (← expected.findValueByNumber number).isNone then
        throw (.unknownClosedEnumValue expected.fullName number)
      liftWire (ProtoVal.ofVarint_int32 number)
  | .TYPE_MESSAGE, .message descriptor wire =>
      let expected ← resolveMessage field proto
      if descriptor != expected then
        throw (.wrongValueType field.fullName s!"message `{expected.fullName}`")
      liftWire (ProtoVal.ofMessage wire)
  | .TYPE_GROUP, .message descriptor wire =>
      let expected ← resolveMessage field proto
      if descriptor != expected then
        throw (.wrongValueType field.fullName s!"group `{expected.fullName}`")
      liftWire (ProtoVal.ofGroup wire)
  | .«Unknown.Value» unknown, _ =>
      throw (.invalidFieldDescriptor field.fullName
        s!"unknown field type number {unknown}")
  | _, _ =>
      throw (.wrongValueType field.fullName s!"field of type {repr type}")

private def retainedFieldUnknowns
    (message : DynamicMessage) (field : FieldDescriptor)
    (proto : FieldDescriptorProto) (number : Nat) : RM (Array ProtoVal) := do
  let values := message.wire.getValuesOf number
  let type ← fieldType field
  if type == .TYPE_ENUM then
    let enum ← resolveEnum field proto
    if (← enum.isClosed).getD false then
      let some enumProto ← enum.toProto
        | throw (.staleDescriptor enum.fullName)
      return ← liftWire <|
        Encoding.Message.retainEnumExtensionUnknownValues
          values (isRepeated proto) true fun raw =>
            let number := Int32.ofBitVec (UInt32.ofNat raw).toBitVec
            enumProto.value.any fun value => value.number == some number
  return values.filter fun value =>
    !wireValueCompatible type (isRepeated proto) value

private def eraseFieldNumber (wire : Encoding.Message) (number : Nat) :
    Encoding.Message :=
  { records := wire.records.filter fun record => record.fieldNum != number }

private def clearOneofSiblings
    (message : DynamicMessage) (field : FieldDescriptor)
    (proto : FieldDescriptorProto) : RM Encoding.Message := do
  let some oneofIndex := proto.oneof_index | return message.wire
  let some containing ← field.containingMessage
    | throw (.invalidFieldDescriptor field.fullName
        "oneof field has no containing message")
  let siblings ← containing.fields
  let mut wire := message.wire
  for sibling in siblings do
    if sibling == field then
      continue
    let siblingProto ← fieldProto sibling
    if siblingProto.oneof_index == some oneofIndex then
      let siblingNumber ← fieldNumber sibling siblingProto
      let unknowns ← retainedFieldUnknowns
        { message with wire } sibling siblingProto siblingNumber
      wire := eraseFieldNumber wire siblingNumber
      for value in unknowns do
        wire := wire.set siblingNumber value
  return wire

private def setValuesM
    (message : DynamicMessage) (field : FieldDescriptor)
    (values : Array Value) : RM DynamicMessage := do
  let proto ← fieldProto field
  checkContainingType message field proto
  if !isRepeated proto && values.size > 1 then
    throw (.expectedSingular field.fullName)
  let number ← fieldNumber field proto
  let type ← fieldType field
  let mut encoded := #[]
  for value in values do
    encoded := encoded.push (← encodeValue field proto type value)
  let retained ← retainedFieldUnknowns message field proto number
  let initialWire : Encoding.Message ←
    if encoded.isEmpty then
      pure message.wire
    else
      clearOneofSiblings message field proto
  let mut wire := initialWire
  wire := eraseFieldNumber wire number
  for value in retained do
    wire := wire.set number value
  for value in encoded do
    wire := wire.set number value
  return { message with wire }

/--
Replace a field's reflected values. Passing an empty array clears the field.
Repeated packable values are emitted in expanded form, which protobuf parsers
must accept regardless of the field's preferred packing.
-/
def DynamicMessage.setValues
    (message : DynamicMessage) (field : FieldDescriptor)
    (values : Array Value) : IO (Except ReflectionError DynamicMessage) :=
  (setValuesM message field values).run

def DynamicMessage.setSingular
    (message : DynamicMessage) (field : FieldDescriptor) (value : Value) :
    IO (Except ReflectionError DynamicMessage) :=
  (do
    let proto ← fieldProto field
    if isRepeated proto then
      throw (ReflectionError.expectedSingular field.fullName)
    setValuesM message field #[value]).run

def DynamicMessage.clearField
    (message : DynamicMessage) (field : FieldDescriptor) :
    IO (Except ReflectionError DynamicMessage) :=
  (setValuesM message field #[]).run

def DynamicMessage.decode
    (descriptor : MessageDescriptor) (bytes : ByteArray) :
    Except ReflectionError DynamicMessage := do
  if bytes.size > 0x7fffffff then
    throw (.wire (.invalidBuffer
      "protobuf messages must be smaller than 2 GiB"))
  let parsed :=
    Binary.Get.run (Binary.getThe Encoding.Message) bytes |>.toExcept
  let wire ←
    match Encoding.protoDecodeParseResultExcept parsed with
    | .ok wire => pure wire
    | .error error => throw (.wire error)
  return { descriptor, wire }

def DynamicMessage.encode (message : DynamicMessage) :
    Except ReflectionError ByteArray := do
  match message.wire.validateForEncoding with
  | .error error => throw (.wire error)
  | .ok () =>
    let bytes := Binary.Put.run (Binary.put message.wire)
    if bytes.size > 0x7fffffff then
      throw (.wire (.userError
        "serialized protobuf message exceeds the 2 GiB limit"))
    return bytes

def DynamicMessage.ofStatic
    (value : α) [ReflectMessage α] :
    Except ReflectionError DynamicMessage := do
  let wire ←
    match ReflectMessage.toMessagePartial value with
    | .ok wire => pure wire
    | .error error => throw (.wire error)
  return {
    descriptor := messageDescriptor α
    wire
  }

def DynamicMessage.toStatic
    (message : DynamicMessage) (α : Type) [ReflectMessage α] :
    Except ReflectionError α := do
  let expected := messageDescriptor α
  if message.descriptor != expected then
    throw (.wrongContainingType expected.fullName message.descriptor.fullName)
  match ReflectMessage.fromMessage message.wire with
  | .ok value => return value
  | .error error => throw (.wire error)

def Value.ofStaticEnum (value : α) [ReflectEnum α] : Value :=
  .enum (enumDescriptor α) (ReflectEnum.toInt32 value)

def Value.toStaticEnum
    (value : Value) (α : Type) [ReflectEnum α] :
    IO (Except ReflectionError α) :=
  (show RM α from do
    let .enum descriptor number := value
      | throw (ReflectionError.wrongValueType
          (enumDescriptor α).fullName "enum")
    let expected := enumDescriptor α
    if descriptor != expected then
      throw (ReflectionError.wrongValueType
        expected.fullName s!"enum `{expected.fullName}`")
    if (← expected.isClosed).getD false &&
        (← expected.findValueByNumber number).isNone then
      throw (ReflectionError.unknownClosedEnumValue expected.fullName number)
    return ReflectEnum.fromInt32 number).run

def DynamicMessage.findKnownField
    (message : DynamicMessage) (number : Int32)
    (extensions? : Option ExtensionResolver := none) :
    IO (Option FieldDescriptor) := do
  if let some field ← message.descriptor.findFieldByNumber number then
    return some field
  match extensions? with
  | none => return none
  | some extensions =>
      extensions.findExtensionByNumber message.descriptor number

end Protobuf.Reflection
