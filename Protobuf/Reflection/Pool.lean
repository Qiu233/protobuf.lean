module

public import Protobuf.Internal.Desc
public import Protobuf.Base64

public section

namespace Protobuf.Reflection

open google.protobuf

/--
The identity of a descriptor pool.

Names alone do not identify descriptors: two independent dynamic pools may
contain unrelated declarations with the same protobuf full name.
-/
structure PoolId where
  private mk ::
  value : Nat
deriving BEq, Hashable, Inhabited

instance : Repr PoolId where
  reprPrec id _ := s!"PoolId({id.value})"

inductive PoolError where
  | invalidDescriptor (detail : String)
  | duplicateFile (name : String)
  | duplicateSymbol (fullName existingFile newFile : String)
  | duplicateExtensionNumber
      (extendee : String) (number : Int32) (existingName newName : String)
  | decodeFailure (detail : String)
  | encodeFailure (detail : String)
deriving Repr, BEq

instance : ToString PoolError where
  toString
    | .invalidDescriptor detail => s!"invalid file descriptor: {detail}"
    | .duplicateFile name =>
        s!"a different descriptor for protobuf file `{name}` is already registered"
    | .duplicateSymbol fullName existingFile newFile =>
        s!"protobuf symbol `{fullName}` from `{newFile}` conflicts with `{existingFile}`"
    | .duplicateExtensionNumber extendee number existingName newName =>
        s!"protobuf extensions `{existingName}` and `{newName}` both use field {number} of `{extendee}`"
    | .decodeFailure detail => s!"cannot decode FileDescriptorProto: {detail}"
    | .encodeFailure detail => s!"cannot encode FileDescriptorProto: {detail}"

private structure FileData where
  proto : FileDescriptorProto
  canonicalBytes : ByteArray

private structure MessageData where
  fileName : String
  fullName : String
  proto : DescriptorProto

private structure EnumData where
  fileName : String
  fullName : String
  proto : EnumDescriptorProto
  isClosed : Bool

private structure EnumValueData where
  fileName : String
  fullName : String
  enumFullName : String
  index : Nat

private structure FieldData where
  fileName : String
  fullName : String
  proto : FieldDescriptorProto
  effectiveType : Option FieldDescriptorProto.Type
  containingMessage : Option String
  extensionScope : Option String
  isExtension : Bool

private structure OneofData where
  fileName : String
  fullName : String
  containingMessage : String
  index : Nat
  proto : OneofDescriptorProto

private structure ServiceData where
  fileName : String
  fullName : String
  proto : ServiceDescriptorProto

private structure MethodData where
  fileName : String
  fullName : String
  service : String
  index : Nat
  proto : MethodDescriptorProto

private inductive SymbolData where
  | message (data : MessageData)
  | enum (data : EnumData)
  | enumValue (data : EnumValueData)
  | field (data : FieldData)
  | oneof (data : OneofData)
  | service (data : ServiceData)
  | method (data : MethodData)

private def SymbolData.fileName : SymbolData → String
  | .message data => data.fileName
  | .enum data => data.fileName
  | .enumValue data => data.fileName
  | .field data => data.fileName
  | .oneof data => data.fileName
  | .service data => data.fileName
  | .method data => data.fileName

private structure PoolState where
  files : Std.HashMap String FileData := {}
  symbols : Std.HashMap String SymbolData := {}
  extensions : Std.HashMap String String := {}
deriving Inhabited

private initialize fallbackPoolStateRef : IO.Ref PoolState ← IO.mkRef {}

/--
A mutable collection of immutable protobuf file descriptors.

The reference is intentionally hidden. Registration is atomic and is the only
operation which mutates a pool.
-/
structure DescriptorPool where
  private mk ::
  id : PoolId
  private state : IO.Ref PoolState

/-- Fallback used only by Lean's failure path for `initialize` declarations. -/
protected def DescriptorPool.inhabitedFallback : DescriptorPool :=
  { id := default, state := fallbackPoolStateRef }

instance : Inhabited DescriptorPool :=
  ⟨DescriptorPool.inhabitedFallback⟩

instance : BEq DescriptorPool where
  beq a b := a.id == b.id

instance : Hashable DescriptorPool where
  hash pool := hash pool.id

instance : Repr DescriptorPool where
  reprPrec pool _ := s!"DescriptorPool({repr pool.id})"

private initialize poolUnderlays :
    IO.Ref (Std.HashMap PoolId DescriptorPool) ← IO.mkRef {}

structure FileDescriptor where
  pool : DescriptorPool
  name : String
deriving Repr, Inhabited

structure MessageDescriptor where
  pool : DescriptorPool
  fullName : String
deriving Repr, Inhabited

structure EnumDescriptor where
  pool : DescriptorPool
  fullName : String
deriving Repr, Inhabited

structure EnumValueDescriptor where
  enum : EnumDescriptor
  index : Nat
deriving Repr, Inhabited

structure FieldDescriptor where
  pool : DescriptorPool
  fullName : String
deriving Repr, Inhabited

structure OneofDescriptor where
  pool : DescriptorPool
  fullName : String
deriving Repr, Inhabited

structure ServiceDescriptor where
  pool : DescriptorPool
  fullName : String
deriving Repr, Inhabited

structure MethodDescriptor where
  pool : DescriptorPool
  fullName : String
deriving Repr, Inhabited

instance : BEq FileDescriptor where
  beq a b := a.pool == b.pool && a.name == b.name

instance : BEq MessageDescriptor where
  beq a b := a.pool == b.pool && a.fullName == b.fullName

instance : BEq EnumDescriptor where
  beq a b := a.pool == b.pool && a.fullName == b.fullName

instance : BEq EnumValueDescriptor where
  beq a b := a.enum == b.enum && a.index == b.index

instance : BEq FieldDescriptor where
  beq a b := a.pool == b.pool && a.fullName == b.fullName

instance : BEq OneofDescriptor where
  beq a b := a.pool == b.pool && a.fullName == b.fullName

instance : BEq ServiceDescriptor where
  beq a b := a.pool == b.pool && a.fullName == b.fullName

instance : BEq MethodDescriptor where
  beq a b := a.pool == b.pool && a.fullName == b.fullName

private initialize nextPoolId : IO.Ref Nat ← IO.mkRef 0

/-- Make an independent, initially empty descriptor pool. -/
def DescriptorPool.new : IO DescriptorPool := do
  let id ← nextPoolId.modifyGet fun id => (id, id + 1)
  let state ← IO.mkRef {}
  return { id := .mk id, state }

/--
Make a pool which resolves missing declarations through `underlay`.

New files are stored only in the returned pool. They may reference types from
the underlay, but may not redefine an underlay file or symbol.
-/
def DescriptorPool.newWithUnderlay
    (underlay : DescriptorPool) : IO DescriptorPool := do
  let pool ← DescriptorPool.new
  poolUnderlays.modify (·.insert pool.id underlay)
  return pool

private def DescriptorPool.directUnderlay?
    (pool : DescriptorPool) : IO (Option DescriptorPool) := do
  return (← poolUnderlays.get)[pool.id]?

/-- Whether `base` is this pool or one of its transitive underlays. -/
partial def DescriptorPool.isBasedOn
    (pool base : DescriptorPool) : IO Bool := do
  if pool == base then
    return true
  let some underlay ← pool.directUnderlay? | return false
  underlay.isBasedOn base

private def qualify (scope name : String) : String :=
  if scope.isEmpty then name else s!"{scope}.{name}"

private def normalizeFullName (name : String) : String :=
  name.dropPrefix "." |>.toString

private def extensionKey (extendee : String) (number : Int32) : String :=
  s!"{normalizeFullName extendee}\x00{number}"

private partial def DescriptorPool.findFileData
    (pool : DescriptorPool) (name : String) : IO (Option (DescriptorPool × FileData)) := do
  if let some data := (← pool.state.get).files[name]? then
    return some (pool, data)
  let some underlay ← pool.directUnderlay? | return none
  underlay.findFileData name

private partial def DescriptorPool.findSymbolData
    (pool : DescriptorPool) (fullName : String) :
    IO (Option (DescriptorPool × SymbolData)) := do
  if let some data := (← pool.state.get).symbols[fullName]? then
    return some (pool, data)
  let some underlay ← pool.directUnderlay? | return none
  underlay.findSymbolData fullName

private partial def DescriptorPool.findExtensionName
    (pool : DescriptorPool) (key : String) :
    IO (Option (DescriptorPool × String)) := do
  if let some fullName := (← pool.state.get).extensions[key]? then
    return some (pool, fullName)
  let some underlay ← pool.directUnderlay? | return none
  underlay.findExtensionName key

private def requiredName (kind : String) (name? : Option String) :
    Except PoolError String := do
  let some name := name?
    | throw (.invalidDescriptor s!"{kind} has no name")
  if name.isEmpty then
    throw (.invalidDescriptor s!"{kind} has an empty name")
  if name.contains '.' then
    throw (.invalidDescriptor s!"{kind} name `{name}` is not a simple identifier")
  return name

private def editionEnumClosed
    (inherited : Option FeatureSet.EnumType) (enum : EnumDescriptorProto) :
    Except PoolError Bool := do
  let feature? :=
    match enum.options.bind (·.features) |>.bind (·.enum_type) with
    | some feature => some feature
    | none => inherited
  match feature? with
  | none | some .OPEN => return false
  | some .CLOSED => return true
  | some .ENUM_TYPE_UNKNOWN =>
      throw (.invalidDescriptor "an editions enum has ENUM_TYPE_UNKNOWN closedness")
  | some (.«Unknown.Value» value) =>
      throw (.invalidDescriptor s!"an editions enum has unknown closedness value {value}")

private def enumClosedness
    (file : FileDescriptorProto) (inherited : Option FeatureSet.EnumType)
    (enum : EnumDescriptorProto) :
    Except PoolError Bool := do
  match file.syntax.getD "proto2" with
  | "proto2" => return true
  | "proto3" => return false
  | "editions" => editionEnumClosed inherited enum
  | syntaxName => throw (.invalidDescriptor s!"unknown syntax `{syntaxName}`")

private def fieldEffectiveType
    (file : FileDescriptorProto)
    (inheritedEncoding : Option FeatureSet.MessageEncoding)
    (field : FieldDescriptorProto) (isMapField : Bool := false) :
    Except PoolError (Option FieldDescriptorProto.Type) := do
  let some type := field.type | return none
  if file.syntax.getD "proto2" != "editions" ||
      type != .TYPE_MESSAGE || isMapField then
    return some type
  let encoding :=
    (field.options.bind (·.features) |>.bind (·.message_encoding)).orElse
      (fun _ => inheritedEncoding) |>.getD .LENGTH_PREFIXED
  match encoding with
  | .LENGTH_PREFIXED => return some .TYPE_MESSAGE
  | .DELIMITED => return some .TYPE_GROUP
  | .MESSAGE_ENCODING_UNKNOWN =>
      throw (.invalidDescriptor
        "an editions message field has MESSAGE_ENCODING_UNKNOWN")
  | .«Unknown.Value» value =>
      throw (.invalidDescriptor
        s!"an editions message field has unknown message_encoding value {value}")

private def enumSymbols
    (fileName enumFullName valueScope : String) (enum : EnumDescriptorProto)
    (closed : Bool) : Except PoolError (Array (String × SymbolData)) := do
  let mut out : Array (String × SymbolData) :=
    #[(enumFullName, .enum {
      fileName
      fullName := enumFullName
      proto := enum
      isClosed := closed
    })]
  for index in [:enum.value.size] do
    let value := enum.value[index]!
    let name ← requiredName s!"value in enum `{enumFullName}`" value.name
    let fullName := qualify valueScope name
    out := out.push (fullName, .enumValue {
      fileName
      fullName
      enumFullName
      index
    })
  return out

private def isMapField
    (containingFullName : String) (message : DescriptorProto)
    (field : FieldDescriptorProto) : Bool :=
  if field.type != some .TYPE_MESSAGE then
    false
  else
    let target := normalizeFullName (field.type_name.getD "")
    message.nested_type.any fun nested =>
      nested.options.bind (·.map_entry) == some true &&
        nested.name.any fun name =>
          let entryFullName := qualify containingFullName name
          target == entryFullName || target == name ||
            entryFullName.endsWith s!".{target}"

private partial def collectMessage
    (file : FileDescriptorProto) (fileName scope : String)
    (inheritedEnumType : Option FeatureSet.EnumType)
    (inheritedMessageEncoding : Option FeatureSet.MessageEncoding)
    (message : DescriptorProto) : Except PoolError (Array (String × SymbolData)) := do
  let name ← requiredName "message" message.name
  let fullName := qualify scope name
  let enumType :=
    (message.options.bind (·.features) |>.bind (·.enum_type)).orElse
      (fun _ => inheritedEnumType)
  let mut out := #[(fullName, .message { fileName, fullName, proto := message })]
  for field in message.field do
    let fieldName ← requiredName s!"field in `{fullName}`" field.name
    let fieldFullName := qualify fullName fieldName
    let effectiveType ←
      fieldEffectiveType file inheritedMessageEncoding field
        (isMapField fullName message field)
    out := out.push (fieldFullName, .field {
      fileName
      fullName := fieldFullName
      proto := field
      effectiveType
      containingMessage := some fullName
      extensionScope := none
      isExtension := false
    })
  for i in [:message.oneof_decl.size] do
    let oneof := message.oneof_decl[i]!
    let oneofName ← requiredName s!"oneof in `{fullName}`" oneof.name
    let oneofFullName := qualify fullName oneofName
    out := out.push (oneofFullName, .oneof {
      fileName
      fullName := oneofFullName
      containingMessage := fullName
      index := i
      proto := oneof
    })
  for ext in message.extension do
    let extName ← requiredName s!"extension in `{fullName}`" ext.name
    let extFullName := qualify fullName extName
    let effectiveType ←
      fieldEffectiveType file inheritedMessageEncoding ext
    out := out.push (extFullName, .field {
      fileName
      fullName := extFullName
      proto := ext
      effectiveType
      containingMessage := none
      extensionScope := some fullName
      isExtension := true
    })
  for enum in message.enum_type do
    let enumName ← requiredName s!"enum in `{fullName}`" enum.name
    let enumFullName := qualify fullName enumName
    let closed ← enumClosedness file enumType enum
    out := out ++ (← enumSymbols fileName enumFullName fullName enum closed)
  for nested in message.nested_type do
    out := out ++ (← collectMessage file fileName fullName enumType
      inheritedMessageEncoding nested)
  return out

private def collectSymbols (file : FileDescriptorProto) :
    Except PoolError (String × Array (String × SymbolData)) := do
  let some fileName := file.name
    | throw (.invalidDescriptor "file has no name")
  if fileName.isEmpty then
    throw (.invalidDescriptor "file has an empty name")
  let package := file.package.getD ""
  let fileFeatures := file.options.bind (·.features)
  let inheritedEnumType := fileFeatures.bind (·.enum_type)
  let inheritedMessageEncoding := fileFeatures.bind (·.message_encoding)
  let mut out := #[]
  for message in file.message_type do
    out := out ++ (← collectMessage file fileName package inheritedEnumType
      inheritedMessageEncoding message)
  for enum in file.enum_type do
    let name ← requiredName "top-level enum" enum.name
    let fullName := qualify package name
    let closed ← enumClosedness file inheritedEnumType enum
    out := out ++ (← enumSymbols fileName fullName package enum closed)
  for ext in file.extension do
    let name ← requiredName "top-level extension" ext.name
    let fullName := qualify package name
    let effectiveType ←
      fieldEffectiveType file inheritedMessageEncoding ext
    out := out.push (fullName, .field {
      fileName
      fullName
      proto := ext
      effectiveType
      containingMessage := none
      extensionScope := none
      isExtension := true
    })
  for service in file.service do
    let name ← requiredName "service" service.name
    let fullName := qualify package name
    out := out.push (fullName, .service { fileName, fullName, proto := service })
    for i in [:service.method.size] do
      let method := service.method[i]!
      let methodName ← requiredName s!"method in `{fullName}`" method.name
      let methodFullName := qualify fullName methodName
      out := out.push (methodFullName, .method {
        fileName
        fullName := methodFullName
        service := fullName
        index := i
        proto := method
      })
  return (fileName, out)

private def insertSymbols
    (state : PoolState) (fileName : String)
    (symbols : Array (String × SymbolData)) :
    Except PoolError PoolState := do
  let mut next := state
  for (fullName, symbol) in symbols do
    if let some old := next.symbols[fullName]? then
      throw (.duplicateSymbol fullName old.fileName fileName)
    next := { next with symbols := next.symbols.insert fullName symbol }
    if let .field data := symbol then
      if data.isExtension then
        let some extendee := data.proto.extendee
          | throw (.invalidDescriptor
              s!"extension `{fullName}` has no extendee")
        let some number := data.proto.number
          | throw (.invalidDescriptor
              s!"extension `{fullName}` has no field number")
        if number <= 0 then
          throw (.invalidDescriptor
            s!"extension `{fullName}` has invalid field number {number}")
        let key := extensionKey extendee number
        if let some oldName := next.extensions[key]? then
          throw (.duplicateExtensionNumber
            (normalizeFullName extendee) number oldName fullName)
        next := { next with extensions := next.extensions.insert key fullName }
  return next

private def checkUnderlayConflicts
    (pool : DescriptorPool) (fileName : String)
    (symbols : Array (String × SymbolData)) :
    ExceptT PoolError IO Unit := do
  let some underlay ← pool.directUnderlay? | return
  if (← underlay.findFileData fileName).isSome then
    throw (.duplicateFile fileName)
  for (fullName, symbol) in symbols do
    if let some (_, old) ← underlay.findSymbolData fullName then
      throw (.duplicateSymbol fullName old.fileName fileName)
    if let .field data := symbol then
      if data.isExtension then
        let some extendee := data.proto.extendee
          | throw (.invalidDescriptor
              s!"extension `{fullName}` has no extendee")
        let some number := data.proto.number
          | throw (.invalidDescriptor
              s!"extension `{fullName}` has no field number")
        let key := extensionKey extendee number
        if let some (_, oldName) ← underlay.findExtensionName key then
          throw (.duplicateExtensionNumber
            (normalizeFullName extendee) number oldName fullName)

/--
Atomically register one file.

Registering the exact same descriptor again is idempotent. A same-name file
with different contents, or any symbol collision, is rejected without
partially changing the pool. Dependencies may be registered later.
-/
def DescriptorPool.registerFile
    (pool : DescriptorPool) (file : FileDescriptorProto) :
    IO (Except PoolError FileDescriptor) :=
  (show ExceptT PoolError IO FileDescriptor from do
    let canonicalBytes ← liftExcept <|
      (FileDescriptorProto.«protobuf.internal».encode file).mapError fun err =>
        PoolError.encodeFailure (toString err)
    let (fileName, symbols) ← collectSymbols file
    checkUnderlayConflicts pool fileName symbols
    ExceptT.mk <| pool.state.modifyGet fun state =>
      match state.files[fileName]? with
      | some old =>
          if old.canonicalBytes == canonicalBytes then
            (.ok { pool, name := fileName }, state)
          else
            (.error (.duplicateFile fileName), state)
      | none =>
          match insertSymbols state fileName symbols with
          | .error err => (.error err, state)
          | .ok next =>
              let next := {
                next with
                files := next.files.insert fileName { proto := file, canonicalBytes }
              }
              (.ok { pool, name := fileName }, next)).run

def DescriptorPool.registerFileBytes
    (pool : DescriptorPool) (bytes : ByteArray) :
    IO (Except PoolError FileDescriptor) :=
  (show ExceptT PoolError IO FileDescriptor from do
    let file ← liftExcept <|
      (FileDescriptorProto.«protobuf.internal».decode bytes).mapError fun err =>
        PoolError.decodeFailure (toString err)
    ExceptT.mk <| pool.registerFile file).run

def DescriptorPool.registerFileBase64
    (pool : DescriptorPool) (encoded : String) :
    IO (Except PoolError FileDescriptor) :=
  (show ExceptT PoolError IO FileDescriptor from do
    let bytes ← liftExcept <|
      (Protobuf.Base64.decode encoded).mapError fun err =>
        PoolError.decodeFailure s!"invalid base64: {err}"
    ExceptT.mk <| pool.registerFileBytes bytes).run

def DescriptorPool.registerFileBase64!
    (pool : DescriptorPool) (encoded : String) : IO FileDescriptor := do
  IO.ofExcept (← pool.registerFileBase64 encoded)

def DescriptorPool.findFileByName
    (pool : DescriptorPool) (name : String) : IO (Option FileDescriptor) := do
  match ← pool.findFileData name with
  | some (owner, _) => return some { pool := owner, name }
  | none => return none

def DescriptorPool.findMessageByName
    (pool : DescriptorPool) (fullName : String) : IO (Option MessageDescriptor) := do
  match ← pool.findSymbolData fullName with
  | some (owner, .message _) => return some { pool := owner, fullName }
  | _ => return none

def DescriptorPool.findEnumByName
    (pool : DescriptorPool) (fullName : String) : IO (Option EnumDescriptor) := do
  match ← pool.findSymbolData fullName with
  | some (owner, .enum _) => return some { pool := owner, fullName }
  | _ => return none

def DescriptorPool.findEnumValueByName
    (pool : DescriptorPool) (fullName : String) :
    IO (Option EnumValueDescriptor) := do
  match ← pool.findSymbolData fullName with
  | some (owner, .enumValue data) =>
      return some {
        enum := { pool := owner, fullName := data.enumFullName }
        index := data.index
      }
  | _ => return none

def DescriptorPool.findFieldByName
    (pool : DescriptorPool) (fullName : String) : IO (Option FieldDescriptor) := do
  match ← pool.findSymbolData fullName with
  | some (owner, .field _) => return some { pool := owner, fullName }
  | _ => return none

def DescriptorPool.findExtensionByName
    (pool : DescriptorPool) (fullName : String) : IO (Option FieldDescriptor) := do
  match ← pool.findSymbolData fullName with
  | some (owner, .field data) =>
      return if data.isExtension then some { pool := owner, fullName } else none
  | _ => return none

def DescriptorPool.findExtensionByNumber
    (pool : DescriptorPool) (extendee : MessageDescriptor) (number : Int32) :
    IO (Option FieldDescriptor) := do
  if !(← pool.isBasedOn extendee.pool) then
    return none
  let some (owner, fullName) ←
      pool.findExtensionName (extensionKey extendee.fullName number)
    | return none
  return some { pool := owner, fullName }

def DescriptorPool.findOneofByName
    (pool : DescriptorPool) (fullName : String) : IO (Option OneofDescriptor) := do
  match ← pool.findSymbolData fullName with
  | some (owner, .oneof _) => return some { pool := owner, fullName }
  | _ => return none

def DescriptorPool.findServiceByName
    (pool : DescriptorPool) (fullName : String) : IO (Option ServiceDescriptor) := do
  match ← pool.findSymbolData fullName with
  | some (owner, .service _) => return some { pool := owner, fullName }
  | _ => return none

def DescriptorPool.findMethodByName
    (pool : DescriptorPool) (fullName : String) : IO (Option MethodDescriptor) := do
  match ← pool.findSymbolData fullName with
  | some (owner, .method _) => return some { pool := owner, fullName }
  | _ => return none

/-- All registered files, sorted by file name. -/
def DescriptorPool.files (pool : DescriptorPool) : IO (Array FileDescriptor) := do
  let names := (← pool.state.get).files.keysArray.qsort (· < ·)
  return names.map fun name => { pool, name }

private def getFileData (descriptor : FileDescriptor) : IO (Option FileData) := do
  return (← descriptor.pool.state.get).files[descriptor.name]?

private def getMessageData (descriptor : MessageDescriptor) : IO (Option MessageData) := do
  match (← descriptor.pool.state.get).symbols[descriptor.fullName]? with
  | some (.message data) => return some data
  | _ => return none

private def getEnumData (descriptor : EnumDescriptor) : IO (Option EnumData) := do
  match (← descriptor.pool.state.get).symbols[descriptor.fullName]? with
  | some (.enum data) => return some data
  | _ => return none

private def getFieldData (descriptor : FieldDescriptor) : IO (Option FieldData) := do
  match (← descriptor.pool.state.get).symbols[descriptor.fullName]? with
  | some (.field data) => return some data
  | _ => return none

private def getOneofData (descriptor : OneofDescriptor) : IO (Option OneofData) := do
  match (← descriptor.pool.state.get).symbols[descriptor.fullName]? with
  | some (.oneof data) => return some data
  | _ => return none

private def getServiceData (descriptor : ServiceDescriptor) : IO (Option ServiceData) := do
  match (← descriptor.pool.state.get).symbols[descriptor.fullName]? with
  | some (.service data) => return some data
  | _ => return none

private def getMethodData (descriptor : MethodDescriptor) : IO (Option MethodData) := do
  match (← descriptor.pool.state.get).symbols[descriptor.fullName]? with
  | some (.method data) => return some data
  | _ => return none

def FileDescriptor.toProto (descriptor : FileDescriptor) :
    IO (Option FileDescriptorProto) := do
  return (← getFileData descriptor).map (·.proto)

def FileDescriptor.package (descriptor : FileDescriptor) : IO (Option String) := do
  return (← descriptor.toProto).map (·.package.getD "")

def FileDescriptor.dependencyNames (descriptor : FileDescriptor) :
    IO (Array String) := do
  return (← descriptor.toProto).map (·.dependency) |>.getD #[]

def FileDescriptor.dependencies (descriptor : FileDescriptor) :
    IO (Array (Option FileDescriptor)) := do
  (← descriptor.dependencyNames).mapM descriptor.pool.findFileByName

def FileDescriptor.messages (descriptor : FileDescriptor) :
    IO (Array MessageDescriptor) := do
  let some proto ← descriptor.toProto | return #[]
  let scope := proto.package.getD ""
  return proto.message_type.filterMap fun message =>
    message.name.map fun name =>
      { pool := descriptor.pool, fullName := qualify scope name }

def FileDescriptor.enums (descriptor : FileDescriptor) :
    IO (Array EnumDescriptor) := do
  let some proto ← descriptor.toProto | return #[]
  let scope := proto.package.getD ""
  return proto.enum_type.filterMap fun enum =>
    enum.name.map fun name =>
      { pool := descriptor.pool, fullName := qualify scope name }

def FileDescriptor.extensions (descriptor : FileDescriptor) :
    IO (Array FieldDescriptor) := do
  let some proto ← descriptor.toProto | return #[]
  let scope := proto.package.getD ""
  return proto.extension.filterMap fun field =>
    field.name.map fun name =>
      { pool := descriptor.pool, fullName := qualify scope name }

def FileDescriptor.services (descriptor : FileDescriptor) :
    IO (Array ServiceDescriptor) := do
  let some proto ← descriptor.toProto | return #[]
  let scope := proto.package.getD ""
  return proto.service.filterMap fun service =>
    service.name.map fun name =>
      { pool := descriptor.pool, fullName := qualify scope name }

def MessageDescriptor.toProto (descriptor : MessageDescriptor) :
    IO (Option DescriptorProto) := do
  return (← getMessageData descriptor).map (·.proto)

def MessageDescriptor.file (descriptor : MessageDescriptor) :
    IO (Option FileDescriptor) := do
  return (← getMessageData descriptor).map fun data =>
    { pool := descriptor.pool, name := data.fileName }

def MessageDescriptor.fields (descriptor : MessageDescriptor) :
    IO (Array FieldDescriptor) := do
  let some data ← getMessageData descriptor | return #[]
  return data.proto.field.filterMap fun field =>
    field.name.map fun name =>
      { pool := descriptor.pool, fullName := qualify descriptor.fullName name }

def MessageDescriptor.extensions (descriptor : MessageDescriptor) :
    IO (Array FieldDescriptor) := do
  let some data ← getMessageData descriptor | return #[]
  return data.proto.extension.filterMap fun field =>
    field.name.map fun name =>
      { pool := descriptor.pool, fullName := qualify descriptor.fullName name }

def MessageDescriptor.oneofs (descriptor : MessageDescriptor) :
    IO (Array OneofDescriptor) := do
  let some data ← getMessageData descriptor | return #[]
  return data.proto.oneof_decl.filterMap fun oneof =>
    oneof.name.map fun name =>
      { pool := descriptor.pool, fullName := qualify descriptor.fullName name }

def MessageDescriptor.nestedMessages (descriptor : MessageDescriptor) :
    IO (Array MessageDescriptor) := do
  let some data ← getMessageData descriptor | return #[]
  return data.proto.nested_type.filterMap fun message =>
    message.name.map fun name =>
      { pool := descriptor.pool, fullName := qualify descriptor.fullName name }

def MessageDescriptor.nestedEnums (descriptor : MessageDescriptor) :
    IO (Array EnumDescriptor) := do
  let some data ← getMessageData descriptor | return #[]
  return data.proto.enum_type.filterMap fun enum =>
    enum.name.map fun name =>
      { pool := descriptor.pool, fullName := qualify descriptor.fullName name }

def MessageDescriptor.findFieldByNumber
    (descriptor : MessageDescriptor) (number : Int32) :
    IO (Option FieldDescriptor) := do
  let some data ← getMessageData descriptor | return none
  let some field := data.proto.field.find? fun field => field.number == some number
    | return none
  return field.name.map fun name =>
    { pool := descriptor.pool, fullName := qualify descriptor.fullName name }

def MessageDescriptor.findFieldByName
    (descriptor : MessageDescriptor) (name : String) :
    IO (Option FieldDescriptor) :=
  descriptor.pool.findFieldByName (qualify descriptor.fullName name)

/-- Whether this synthetic message is the entry type of a protobuf map. -/
def MessageDescriptor.isMapEntry
    (descriptor : MessageDescriptor) : IO (Option Bool) := do
  return (← descriptor.toProto).map fun proto =>
    proto.options.bind (·.map_entry) == some true

def EnumDescriptor.toProto (descriptor : EnumDescriptor) :
    IO (Option EnumDescriptorProto) := do
  return (← getEnumData descriptor).map (·.proto)

def EnumDescriptor.isClosed (descriptor : EnumDescriptor) : IO (Option Bool) := do
  return (← getEnumData descriptor).map (·.isClosed)

def EnumDescriptor.file (descriptor : EnumDescriptor) :
    IO (Option FileDescriptor) := do
  return (← getEnumData descriptor).map fun data =>
    { pool := descriptor.pool, name := data.fileName }

def EnumDescriptor.values (descriptor : EnumDescriptor) :
    IO (Array EnumValueDescriptor) := do
  let some data ← getEnumData descriptor | return #[]
  return (Array.range data.proto.value.size).map fun index =>
    { enum := descriptor, index }

def EnumDescriptor.findValueByName
    (descriptor : EnumDescriptor) (name : String) :
    IO (Option EnumValueDescriptor) := do
  let some data ← getEnumData descriptor | return none
  let some index := data.proto.value.findIdx? fun value => value.name == some name
    | return none
  return some { enum := descriptor, index }

def EnumDescriptor.findValueByNumber
    (descriptor : EnumDescriptor) (number : Int32) :
    IO (Option EnumValueDescriptor) := do
  let some data ← getEnumData descriptor | return none
  let some index := data.proto.value.findIdx? fun value => value.number == some number
    | return none
  return some { enum := descriptor, index }

def EnumValueDescriptor.toProto (descriptor : EnumValueDescriptor) :
    IO (Option EnumValueDescriptorProto) := do
  let some data ← getEnumData descriptor.enum | return none
  return data.proto.value[descriptor.index]?

def EnumValueDescriptor.fullName (descriptor : EnumValueDescriptor) :
    IO (Option String) := do
  let some proto ← descriptor.toProto | return none
  let some name := proto.name | return none
  let scope :=
    String.intercalate "."
      (descriptor.enum.fullName.splitOn "." |>.dropLast)
  return some (qualify scope name)

def EnumValueDescriptor.name
    (descriptor : EnumValueDescriptor) : IO (Option String) := do
  return (← descriptor.toProto).bind (·.name)

def EnumValueDescriptor.number
    (descriptor : EnumValueDescriptor) : IO (Option Int32) := do
  return (← descriptor.toProto).bind (·.number)

def FieldDescriptor.toProto (descriptor : FieldDescriptor) :
    IO (Option FieldDescriptorProto) := do
  return (← getFieldData descriptor).map (·.proto)

def FieldDescriptor.name (descriptor : FieldDescriptor) : IO (Option String) := do
  return (← getFieldData descriptor).bind (·.proto.name)

/--
The canonical ProtoJSON name of an ordinary field.

Descriptors produced by `protoc` always carry `json_name`. The fallback keeps
hand-built descriptor pools useful without making the JSON layer depend on
source-level parser machinery.
-/
def FieldDescriptor.jsonName
    (descriptor : FieldDescriptor) : IO (Option String) := do
  let some proto ← descriptor.toProto | return none
  if let some name := proto.json_name then
    return some name
  let some name := proto.name | return none
  let mut out := ""
  let mut upperNext := false
  for c in name.toList do
    if c == '_' then
      upperNext := true
    else if upperNext then
      out := out.push c.toUpper
      upperNext := false
    else
      out := out.push c
  return some out

def FieldDescriptor.number (descriptor : FieldDescriptor) : IO (Option Int32) := do
  return (← getFieldData descriptor).bind (·.proto.number)

/--
The field type after applying Editions `message_encoding`.

For an Editions message field with effective `DELIMITED` encoding this is
`TYPE_GROUP`, while `toProto` still returns the original `TYPE_MESSAGE`.
-/
def FieldDescriptor.effectiveWireType (descriptor : FieldDescriptor) :
    IO (Option FieldDescriptorProto.Type) := do
  return (← getFieldData descriptor).bind (·.effectiveType)

def FieldDescriptor.isExtension (descriptor : FieldDescriptor) :
    IO (Option Bool) := do
  return (← getFieldData descriptor).map (·.isExtension)

def FieldDescriptor.isRepeated
    (descriptor : FieldDescriptor) : IO (Option Bool) := do
  return (← getFieldData descriptor).map fun data =>
    data.proto.label == some .LABEL_REPEATED

private def editionsFieldPresence
    (file : FileDescriptorProto) (field : FieldDescriptorProto) :
    FeatureSet.FieldPresence :=
  (field.options.bind (·.features) |>.bind (·.field_presence)).orElse
    (fun _ =>
      file.options.bind (·.features) |>.bind (·.field_presence))
    |>.getD .EXPLICIT

/--
The protobuf semantic presence of this field after applying syntax and
Editions features.
-/
def FieldDescriptor.hasPresence
    (descriptor : FieldDescriptor) : IO (Option Bool) := do
  let some data ← getFieldData descriptor | return none
  if data.proto.label == some .LABEL_REPEATED then
    return some false
  if data.isExtension || data.proto.oneof_index.isSome then
    return some true
  let some fileData ←
      getFileData { pool := descriptor.pool, name := data.fileName }
    | return none
  match fileData.proto.syntax.getD "proto2" with
  | "proto2" => return some true
  | "proto3" =>
      return some <|
        data.proto.proto3_optional.getD false ||
        data.effectiveType == some .TYPE_MESSAGE ||
        data.effectiveType == some .TYPE_GROUP
  | "editions" =>
      return some <|
        editionsFieldPresence fileData.proto data.proto != .IMPLICIT
  | _ => return none

/-- Whether the field is required by proto2 or Editions legacy presence. -/
def FieldDescriptor.isRequired
    (descriptor : FieldDescriptor) : IO (Option Bool) := do
  let some data ← getFieldData descriptor | return none
  if data.isExtension || data.proto.label == some .LABEL_REPEATED then
    return some false
  let some fileData ←
      getFileData { pool := descriptor.pool, name := data.fileName }
    | return none
  match fileData.proto.syntax.getD "proto2" with
  | "proto2" =>
      return some (data.proto.label == some .LABEL_REQUIRED)
  | "proto3" => return some false
  | "editions" =>
      return some <|
        editionsFieldPresence fileData.proto data.proto == .LEGACY_REQUIRED
  | _ => return none

def FieldDescriptor.messageType
    (descriptor : FieldDescriptor) : IO (Option MessageDescriptor) := do
  let some data ← getFieldData descriptor | return none
  unless data.effectiveType == some .TYPE_MESSAGE ||
      data.effectiveType == some .TYPE_GROUP do
    return none
  let some name := data.proto.type_name | return none
  descriptor.pool.findMessageByName (normalizeFullName name)

def FieldDescriptor.enumType
    (descriptor : FieldDescriptor) : IO (Option EnumDescriptor) := do
  let some data ← getFieldData descriptor | return none
  unless data.effectiveType == some .TYPE_ENUM do
    return none
  let some name := data.proto.type_name | return none
  descriptor.pool.findEnumByName (normalizeFullName name)

def FieldDescriptor.isMap
    (descriptor : FieldDescriptor) : IO (Option Bool) := do
  let some data ← getFieldData descriptor | return none
  unless data.proto.label == some .LABEL_REPEATED &&
      data.effectiveType == some .TYPE_MESSAGE do
    return some false
  let some message ← descriptor.messageType | return some false
  return (← message.isMapEntry).map (· == true)

def FieldDescriptor.containingMessage (descriptor : FieldDescriptor) :
    IO (Option MessageDescriptor) := do
  let some data ← getFieldData descriptor | return none
  if data.isExtension then
    let some raw := data.proto.extendee | return none
    descriptor.pool.findMessageByName (normalizeFullName raw)
  else
    return data.containingMessage.map fun fullName =>
      { pool := descriptor.pool, fullName }

def FieldDescriptor.extensionScope (descriptor : FieldDescriptor) :
    IO (Option MessageDescriptor) := do
  return (← getFieldData descriptor).bind (·.extensionScope) |>.map fun fullName =>
    { pool := descriptor.pool, fullName }

def FieldDescriptor.extendee (descriptor : FieldDescriptor) :
    IO (Option MessageDescriptor) := do
  let some raw := (← getFieldData descriptor).bind (·.proto.extendee)
    | return none
  descriptor.pool.findMessageByName (normalizeFullName raw)

def FieldDescriptor.file (descriptor : FieldDescriptor) :
    IO (Option FileDescriptor) := do
  return (← getFieldData descriptor).map fun data =>
    { pool := descriptor.pool, name := data.fileName }

def OneofDescriptor.toProto (descriptor : OneofDescriptor) :
    IO (Option OneofDescriptorProto) := do
  return (← getOneofData descriptor).map (·.proto)

def OneofDescriptor.containingMessage (descriptor : OneofDescriptor) :
    IO (Option MessageDescriptor) := do
  return (← getOneofData descriptor).map fun data =>
    { pool := descriptor.pool, fullName := data.containingMessage }

def OneofDescriptor.index (descriptor : OneofDescriptor) : IO (Option Nat) := do
  return (← getOneofData descriptor).map (·.index)

def ServiceDescriptor.toProto (descriptor : ServiceDescriptor) :
    IO (Option ServiceDescriptorProto) := do
  return (← getServiceData descriptor).map (·.proto)

def ServiceDescriptor.methods (descriptor : ServiceDescriptor) :
    IO (Array MethodDescriptor) := do
  let some data ← getServiceData descriptor | return #[]
  return data.proto.method.filterMap fun method =>
    method.name.map fun name =>
      { pool := descriptor.pool, fullName := qualify descriptor.fullName name }

def ServiceDescriptor.file (descriptor : ServiceDescriptor) :
    IO (Option FileDescriptor) := do
  return (← getServiceData descriptor).map fun data =>
    { pool := descriptor.pool, name := data.fileName }

def MethodDescriptor.toProto (descriptor : MethodDescriptor) :
    IO (Option MethodDescriptorProto) := do
  return (← getMethodData descriptor).map (·.proto)

def MethodDescriptor.service (descriptor : MethodDescriptor) :
    IO (Option ServiceDescriptor) := do
  return (← getMethodData descriptor).map fun data =>
    { pool := descriptor.pool, fullName := data.service }

def MethodDescriptor.index (descriptor : MethodDescriptor) : IO (Option Nat) := do
  return (← getMethodData descriptor).map (·.index)

def MethodDescriptor.inputType (descriptor : MethodDescriptor) :
    IO (Option MessageDescriptor) := do
  let some raw := (← getMethodData descriptor).bind (·.proto.input_type)
    | return none
  descriptor.pool.findMessageByName (normalizeFullName raw)

def MethodDescriptor.outputType (descriptor : MethodDescriptor) :
    IO (Option MessageDescriptor) := do
  let some raw := (← getMethodData descriptor).bind (·.proto.output_type)
    | return none
  descriptor.pool.findMessageByName (normalizeFullName raw)

end Protobuf.Reflection
