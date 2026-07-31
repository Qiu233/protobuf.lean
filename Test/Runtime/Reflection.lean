module

import Protobuf

open Protobuf Encoding
open Protobuf.Reflection
open google.protobuf
open scoped Protobuf.Notation

#load_proto_file "Test/Fixtures/Schemas/Proto3.proto"
#load_proto_file "Test/Fixtures/Schemas/ClosedEnumProto2.proto"
#load_proto_file "Test/Fixtures/Schemas/ClosedEnumEditions.proto"
#load_proto_file "Test/Fixtures/Schemas/GroupEditions.proto"
#load_proto_file "Test/Fixtures/Schemas/RequiredMergeProto2.proto"

private def assert (condition : Bool) (failure : String) : IO Unit := do
  unless condition do
    throw (IO.userError failure)

private def ofExcept [ToString ε] (result : Except ε α) : IO α :=
  IO.ofExcept result

private def ofIOExcept [ToString ε] (result : IO (Except ε α)) : IO α :=
  result >>= ofExcept

private def testGeneratedPool : IO Unit := do
  let some _ ←
      generatedPool.findFileByName "google/protobuf/descriptor.proto"
    | throw (IO.userError "descriptor.proto bootstrap schema is absent")
  let some file ← generatedPool.findFileByName "Proto3.proto"
    | throw (IO.userError "generated file was not registered")
  let some proto ← file.toProto
    | throw (IO.userError "registered file descriptor became stale")
  assert (proto.package == some "test.proto3")
    "registered FileDescriptorProto lost its package"

  let allDescriptor := messageDescriptor test.proto3.All
  let some found ← generatedPool.findMessageByName "test.proto3.All"
    | throw (IO.userError "generated message symbol is absent")
  assert (found == allDescriptor)
    "static and pool message descriptors have different identity"

  let colorDescriptor := enumDescriptor test.proto3.Color
  assert ((← colorDescriptor.isClosed) == some false)
    "proto3 enum was not reflected as open"
  let fields ← allDescriptor.fields
  assert (fields.size == 25)
    "message reflection returned the wrong number of fields"

private def testDescriptorIndexes : IO Unit := do
  let pool ← DescriptorPool.new
  let file : FileDescriptorProto := {
    name := some "indexed-lookups.proto"
    «syntax» := some "proto3"
    package := some "indexed"
    message_type := #[{
      name := some "Message"
      field := #[
        {
          name := some "first"
          number := some 1
          label := some .LABEL_OPTIONAL
          type := some .TYPE_INT32
        },
        {
          name := some "second"
          number := some 2
          label := some .LABEL_OPTIONAL
          type := some .TYPE_STRING
        }
      ]
    }]
    enum_type := #[{
      name := some "Alias"
      options := some { allow_alias := some true }
      value := #[
        { name := some "ALIAS_ZERO", number := some 0 },
        { name := some "ALSO_ZERO", number := some 0 },
        { name := some "ALIAS_ONE", number := some 1 }
      ]
    }]
  }
  let _ ← ofIOExcept (pool.registerFile file)
  let some descriptor ← pool.findMessageByName "indexed.Message"
    | throw (IO.userError "indexed message descriptor is absent")
  let some second ← descriptor.findFieldByNumber 2
    | throw (IO.userError "field-number index missed a declared field")
  assert ((← second.name) == some "second")
    "field-number index returned the wrong field"
  assert ((← descriptor.findFieldByNumber 3).isNone)
    "field-number index returned an undeclared field"
  let some alias ← pool.findEnumByName "indexed.Alias"
    | throw (IO.userError "indexed enum descriptor is absent")
  let some alsoZero ← alias.findValueByName "ALSO_ZERO"
    | throw (IO.userError "enum-name index missed an alias")
  assert ((← alsoZero.number) == some 0)
    "enum-name index returned the wrong value"
  let some firstZero ← alias.findValueByNumber 0
    | throw (IO.userError "enum-number index missed an alias")
  assert ((← firstZero.name) == some "ALIAS_ZERO")
    "enum-number index did not preserve first-declared alias lookup"

private def testPoolIdentityAndLateDependencies : IO Unit := do
  let dependency : FileDescriptorProto := {
    name := some "dependency.proto"
    «syntax» := some "proto3"
    package := some "local"
    message_type := #[{ name := some "Dependency" }]
  }
  let dependent : FileDescriptorProto := {
    name := some "dependent.proto"
    «syntax» := some "proto3"
    package := some "local"
    dependency := #["dependency.proto"]
    message_type := #[{ name := some "Dependent" }]
  }
  let first ← DescriptorPool.new
  let second ← DescriptorPool.new
  let dependentDescriptor ← ofIOExcept (first.registerFile dependent)
  let unresolved ← dependentDescriptor.dependencies
  assert (unresolved.size == 1 && unresolved[0]!.isNone)
    "an unregistered late dependency appeared resolved"
  let _ ← ofIOExcept (first.registerFile dependency)
  let resolved ← dependentDescriptor.dependencies
  assert (resolved.size == 1 && resolved[0]!.isSome)
    "late dependency registration did not update descriptor resolution"
  let _ ← ofIOExcept (second.registerFile dependent)
  let some firstMessage ← first.findMessageByName "local.Dependent"
    | throw (IO.userError "first local pool lost its message")
  let some secondMessage ← second.findMessageByName "local.Dependent"
    | throw (IO.userError "second local pool lost its message")
  assert (firstMessage != secondMessage)
    "same-name descriptors from independent pools compared equal"

  let overlay ← DescriptorPool.newWithUnderlay first
  let some inherited ← overlay.findMessageByName "local.Dependent"
    | throw (IO.userError "overlay did not resolve its underlay message")
  assert (inherited == firstMessage)
    "underlay lookup changed descriptor identity"
  match ← overlay.registerFile dependency with
  | .error (.duplicateFile "dependency.proto") => pure ()
  | _ => throw (IO.userError "overlay redefined an underlay file")
  let extensionFile : FileDescriptorProto := {
    name := some "extension.proto"
    «syntax» := some "proto2"
    package := some "local.ext"
    dependency := #["dependent.proto"]
    extension := #[{
      name := some "extra"
      number := some 100
      label := some .LABEL_OPTIONAL
      type := some .TYPE_INT32
      extendee := some ".local.Dependent"
    }]
  }
  let _ ← ofIOExcept (overlay.registerFile extensionFile)
  let some inheritedExtension ← overlay.findExtensionByNumber firstMessage 100
    | throw (IO.userError "overlay extension did not resolve against underlay")
  let extended ← ofIOExcept <|
    ({ descriptor := firstMessage } : DynamicMessage).setSingular
      inheritedExtension (.int32 9)
  assert ((← ofIOExcept
      (extended.getSingular? inheritedExtension)).isSome)
    "overlay extension was incompatible with its underlay extendee"

  let conflicting : FileDescriptorProto := {
    dependent with
    package := some "other"
  }
  match ← first.registerFile conflicting with
  | .error (.duplicateFile "dependent.proto") => pure ()
  | _ => throw (IO.userError "different same-name file was not rejected")

private def testEditionsFeatureInheritance : IO Unit := do
  let pool ← DescriptorPool.new
  let file : FileDescriptorProto := {
    name := some "nested-closed.proto"
    «syntax» := some "editions"
    edition := some .EDITION_2023
    package := some "feature.inheritance"
    message_type := #[{
      name := some "Outer"
      options := some {
        features := some {
          enum_type := some .CLOSED
        }
      }
      enum_type := #[{
        name := some "Nested"
        value := #[{
          name := some "NESTED_ZERO"
          number := some 0
        }]
      }]
    }]
  }
  let _ ← ofIOExcept (pool.registerFile file)
  let some nested ←
      pool.findEnumByName "feature.inheritance.Outer.Nested"
    | throw (IO.userError "nested Editions enum was not registered")
  assert ((← nested.isClosed) == some true)
    "nested Editions enum did not inherit CLOSED from its message"
  let some value ←
      pool.findEnumValueByName "feature.inheritance.Outer.NESTED_ZERO"
    | throw (IO.userError
        "enum value was not registered in the enum's containing scope")
  assert ((← value.fullName) ==
      some "feature.inheritance.Outer.NESTED_ZERO")
    "enum value full_name was incorrectly nested below its enum type"
  assert ((← pool.findEnumValueByName
      "feature.inheritance.Outer.Nested.NESTED_ZERO").isNone)
    "pool accepted the non-protobuf Enum.VALUE full-name spelling"

private def testEditionsDelimitedDynamicField : IO Unit := do
  let owner :=
    messageDescriptor group_support.editions.InheritedDelimited
  let child :=
    messageDescriptor group_support.editions.Payload
  let some field ← owner.findFieldByName "payload"
    | throw (IO.userError "inherited DELIMITED field is absent")
  let some proto ← field.toProto
    | throw (IO.userError "inherited DELIMITED field became stale")
  assert (proto.type == some .TYPE_MESSAGE)
    "runtime descriptor rewrote the source TYPE_MESSAGE"
  assert ((← field.effectiveWireType) == some .TYPE_GROUP)
    "file-level DELIMITED feature was not reflected as GROUPED wire data"
  let childWire : Encoding.Message := .mk #[⟨1, .VARINT 7⟩]
  let dynamic : DynamicMessage := {
    descriptor := owner
    wire := .mk #[⟨2, .GROUPED childWire⟩]
  }
  let some (.message decodedDescriptor decodedWire) ←
      ofIOExcept (dynamic.getSingular? field)
    | throw (IO.userError
        "dynamic reflection did not decode an Editions delimited field")
  assert (decodedDescriptor == child && decodedWire.records.size == 1)
    "dynamic reflection decoded the wrong delimited message"
  let changed ← ofIOExcept <|
    ({ descriptor := owner } : DynamicMessage).setSingular
      field (.message child childWire)
  assert ((changed.wire.getValuesOf 2).any (·.isGROUPED))
    "dynamic reflection encoded an Editions delimited field as LEN"
  let mapOwner :=
    messageDescriptor group_support.editions.InheritedMap
  let some mapField ← mapOwner.findFieldByName "items"
    | throw (IO.userError "inherited Editions map field is absent")
  assert ((← mapField.effectiveWireType) == some .TYPE_MESSAGE)
    "file-level DELIMITED incorrectly changed a map entry to GROUPED"

private def testDynamicOneofSelection : IO Unit := do
  let owner := messageDescriptor test.proto3.All
  let some intField ← owner.findFieldByName "oneof_int32"
    | throw (IO.userError "oneof int field is absent")
  let some stringField ← owner.findFieldByName "oneof_string"
    | throw (IO.userError "oneof string field is absent")
  let some messageField ← owner.findFieldByName "oneof_sub"
    | throw (IO.userError "oneof message field is absent")
  let stringWire ← ofExcept
    (ProtoVal.ofUnvalidatedString
      (Protobuf.UnvalidatedString.ofString "selected"))
  let selected : DynamicMessage := {
    descriptor := owner
    wire := .mk #[
      ⟨22, .VARINT 7⟩,
      ⟨23, stringWire⟩
    ]
  }
  assert ((← ofIOExcept (selected.getSingular? intField)).isNone)
    "an earlier oneof member remained reflected after a later sibling"
  assert ((← ofIOExcept (selected.getSingular? stringField)).isSome)
    "the active oneof member was not reflected"

  let firstChild : Encoding.Message := .mk #[⟨1, .VARINT 1⟩]
  let lastChild : Encoding.Message := .mk #[⟨2, stringWire⟩]
  let firstChildValue ← ofExcept (ProtoVal.ofMessage firstChild)
  let lastChildValue ← ofExcept (ProtoVal.ofMessage lastChild)
  let reset : DynamicMessage := {
    descriptor := owner
    wire := .mk #[
      ⟨24, firstChildValue⟩,
      ⟨22, .VARINT 9⟩,
      ⟨24, lastChildValue⟩
    ]
  }
  let some (.message _ childWire) ←
      ofIOExcept (reset.getSingular? messageField)
    | throw (IO.userError "active oneof message was not reflected")
  assert ((childWire.getValuesOf 1).isEmpty &&
      !(childWire.getValuesOf 2).isEmpty)
    "oneof message reflection merged data from before a sibling reset"

private def testStaticDynamicBridge : IO Unit := do
  let original : test.proto3.All := { int32_field := 42 }
  let dynamic ← ofExcept (DynamicMessage.ofStatic original)
  let some field ← dynamic.descriptor.findFieldByName "int32_field"
    | throw (IO.userError "int32_field descriptor is absent")
  let some (.int32 value) ← ofIOExcept (dynamic.getSingular? field)
    | throw (IO.userError "dynamic scalar field had the wrong value kind")
  assert (value == 42) "static-to-dynamic conversion lost a scalar"
  let changed ← ofIOExcept (dynamic.setSingular field (.int32 7))
  let static ← ofExcept (changed.toStatic test.proto3.All)
  assert (static.int32_field == 7)
    "dynamic-to-static conversion lost a reflected mutation"
  let mixed : DynamicMessage := {
    descriptor := dynamic.descriptor
    wire := .mk #[
      ⟨1, .I32 (0xdeadbeef : UInt32).toBitVec⟩,
      ⟨1, .VARINT 42⟩
    ]
  }
  let some (.int32 mixedValue) ← ofIOExcept (mixed.getSingular? field)
    | throw (IO.userError "wrong-wire unknown hid a valid dynamic value")
  assert (mixedValue == 42)
    "wrong-wire unknown changed a reflected scalar"
  let mixedChanged ← ofIOExcept (mixed.setSingular field (.int32 7))
  assert ((mixedChanged.wire.getValuesOf 1).any (·.isI32))
    "dynamic setter discarded a wrong-wire unknown with the same tag"

  let incomplete : test.required_merge.proto2.Child := default
  let dynamicPartial ← ofExcept (DynamicMessage.ofStatic incomplete)
  assert (dynamicPartial.wire.records.isEmpty)
    "partial static reflection manufactured required fields"
  match dynamicPartial.toStatic test.required_merge.proto2.Child with
  | .error (.wire (.missingRequiredField _)) => pure ()
  | _ => throw (IO.userError
      "dynamic-to-static conversion did not validate required fields")
  let nestedIncomplete :
      test.required_merge.proto2.OptionalOuter := {
    child := some incomplete
  }
  let nestedDynamic ← ofExcept (DynamicMessage.ofStatic nestedIncomplete)
  assert (nestedDynamic.wire.records.size == 1)
    "partial static reflection rejected an incomplete nested message"

private def testClosedEnumAndExtensions : IO Unit := do
  let messageDescriptor :=
    messageDescriptor test.closed.proto2.ClosedMessage
  let enumDescriptor :=
    enumDescriptor test.closed.proto2.ClosedEnum
  assert ((← enumDescriptor.isClosed) == some true)
    "proto2 enum was not reflected as closed"
  let some field ← messageDescriptor.findFieldByName "singular"
    | throw (IO.userError "closed enum field descriptor is absent")
  let dynamic : DynamicMessage := {
    descriptor := messageDescriptor
    wire := .mk #[⟨1, .VARINT 123⟩]
  }
  assert ((← ofIOExcept (dynamic.presentValues field)).isEmpty)
    "unknown closed enum number appeared as a reflected field value"
  let changed ← ofIOExcept <|
    dynamic.setSingular field (.enum enumDescriptor 1)
  let values ← ofIOExcept (changed.presentValues field)
  assert (values.size == 1)
    "known closed enum value was not installed"
  let raw := changed.wire.getValuesOf 1
  assert (raw.any fun value => value.isVARINT? == some 123)
    "setting a closed enum discarded its unknown numeric value"
  let knownThenUnknown : DynamicMessage := {
    descriptor := messageDescriptor
    wire := .mk #[⟨1, .VARINT 1⟩, ⟨1, .VARINT 123⟩]
  }
  let some (.enum _ known) ←
      ofIOExcept (knownThenUnknown.getSingular? field)
    | throw (IO.userError
        "unknown closed-enum occurrence hid an earlier known value")
  assert (known == 1)
    "dynamic closed-enum singular selection did not use the last known value"

  let some extension ←
      generatedPool.findExtensionByNumber messageDescriptor 100
    | throw (IO.userError "generated extension number was not registered")
  assert (extension.fullName == "test.closed.proto2.singular_ext")
    "extension resolver returned the wrong declaration"
  assert ((← extension.containingMessage) == some messageDescriptor)
    "extension containingMessage did not return its extendee"
  let extensionMessage : DynamicMessage := {
    descriptor := messageDescriptor
    wire := .mk #[⟨100, .VARINT 123⟩]
  }
  let changedExtension ← ofIOExcept <|
    extensionMessage.setSingular extension (.enum enumDescriptor 1)
  assert ((← ofIOExcept
      (changedExtension.getSingular? extension)).isSome)
    "dynamic extension setter did not expose the known value"
  assert ((changedExtension.wire.getValuesOf 100).any fun value =>
      value.isVARINT? == some 123)
    "dynamic extension setter discarded its closed-enum unknown value"

public def main : IO Unit := do
  testGeneratedPool
  testDescriptorIndexes
  testPoolIdentityAndLateDependencies
  testEditionsFeatureInheritance
  testEditionsDelimitedDynamicField
  testDynamicOneofSelection
  testStaticDynamicBridge
  testClosedEnumAndExtensions
