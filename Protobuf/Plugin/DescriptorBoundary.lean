module

public import Protobuf.Internal.Desc

public section

namespace Protobuf.Plugin.DescriptorBoundary

open google.protobuf

/-
`protoc` supplies two representations of every requested source file:

* `proto_file` is authoritative for the schema and all runtime-retention
  options.
* `source_file_descriptors` has the same schema, with source-retention options
  added back.

The plugin only needs the built-in source-retention fields below.  Custom
options are stored as unknown fields by the bootstrap descriptor types, so
they are deliberately ignored when comparing the two representations and are
never copied from the source descriptor.  Runtime custom options remain on
the authoritative `proto_file` value.
-/

private def keepIfEncodedNonempty {α ε : Type}
    (encode : α → Except ε ByteArray) (value : α) : Option α :=
  match encode value with
  | .ok bytes => if bytes.isEmpty then none else some value
  | .error _ => some value

private def normalizeFeatures (features : FeatureSet) : FeatureSet :=
  { features with
    enforce_naming_style := none
    default_symbol_visibility := none
    enforce_proto_limits := none
    «Unknown.Fields» := {}
  }

private def normalizeFeatures? (features : Option FeatureSet) :
    Option FeatureSet :=
  features.bind fun value =>
    keepIfEncodedNonempty FeatureSet.«protobuf.internal».encode
      (normalizeFeatures value)

private def normalizeFileOptions (options : FileOptions) : FileOptions :=
  { options with
    features := normalizeFeatures? options.features
    «Unknown.Fields» := {}
  }

private def normalizeFileOptions? (options : Option FileOptions) :
    Option FileOptions :=
  options.bind fun value =>
    keepIfEncodedNonempty FileOptions.«protobuf.internal».encode
      (normalizeFileOptions value)

private def normalizeMessageOptions
    (options : MessageOptions) : MessageOptions :=
  { options with
    features := normalizeFeatures? options.features
    «Unknown.Fields» := {}
  }

private def normalizeMessageOptions? (options : Option MessageOptions) :
    Option MessageOptions :=
  options.bind fun value =>
    keepIfEncodedNonempty MessageOptions.«protobuf.internal».encode
      (normalizeMessageOptions value)

private def normalizeFieldOptions (options : FieldOptions) : FieldOptions :=
  { options with
    features := normalizeFeatures? options.features
    «Unknown.Fields» := {}
  }

private def normalizeFieldOptions? (options : Option FieldOptions) :
    Option FieldOptions :=
  options.bind fun value =>
    keepIfEncodedNonempty FieldOptions.«protobuf.internal».encode
      (normalizeFieldOptions value)

private def normalizeOneofOptions (options : OneofOptions) : OneofOptions :=
  { options with
    features := normalizeFeatures? options.features
    «Unknown.Fields» := {}
  }

private def normalizeOneofOptions? (options : Option OneofOptions) :
    Option OneofOptions :=
  options.bind fun value =>
    keepIfEncodedNonempty OneofOptions.«protobuf.internal».encode
      (normalizeOneofOptions value)

private def normalizeEnumOptions (options : EnumOptions) : EnumOptions :=
  { options with
    features := normalizeFeatures? options.features
    «Unknown.Fields» := {}
  }

private def normalizeEnumOptions? (options : Option EnumOptions) :
    Option EnumOptions :=
  options.bind fun value =>
    keepIfEncodedNonempty EnumOptions.«protobuf.internal».encode
      (normalizeEnumOptions value)

private def normalizeEnumValueOptions
    (options : EnumValueOptions) : EnumValueOptions :=
  { options with
    features := normalizeFeatures? options.features
    «Unknown.Fields» := {}
  }

private def normalizeEnumValueOptions?
    (options : Option EnumValueOptions) : Option EnumValueOptions :=
  options.bind fun value =>
    keepIfEncodedNonempty EnumValueOptions.«protobuf.internal».encode
      (normalizeEnumValueOptions value)

private def normalizeServiceOptions
    (options : ServiceOptions) : ServiceOptions :=
  { options with
    features := normalizeFeatures? options.features
    «Unknown.Fields» := {}
  }

private def normalizeServiceOptions? (options : Option ServiceOptions) :
    Option ServiceOptions :=
  options.bind fun value =>
    keepIfEncodedNonempty ServiceOptions.«protobuf.internal».encode
      (normalizeServiceOptions value)

private def normalizeMethodOptions
    (options : MethodOptions) : MethodOptions :=
  { options with
    features := normalizeFeatures? options.features
    «Unknown.Fields» := {}
  }

private def normalizeMethodOptions? (options : Option MethodOptions) :
    Option MethodOptions :=
  options.bind fun value =>
    keepIfEncodedNonempty MethodOptions.«protobuf.internal».encode
      (normalizeMethodOptions value)

private def normalizeExtensionRangeOptions
    (options : ExtensionRangeOptions) : ExtensionRangeOptions :=
  { options with
    declaration := #[]
    verification := none
    features := normalizeFeatures? options.features
    «Unknown.Fields» := {}
  }

private def normalizeExtensionRangeOptions?
    (options : Option ExtensionRangeOptions) : Option ExtensionRangeOptions :=
  options.bind fun value =>
    keepIfEncodedNonempty ExtensionRangeOptions.«protobuf.internal».encode
      (normalizeExtensionRangeOptions value)

private def normalizeField
    (field : FieldDescriptorProto) : FieldDescriptorProto :=
  { field with options := normalizeFieldOptions? field.options }

private def normalizeOneof
    (oneof : OneofDescriptorProto) : OneofDescriptorProto :=
  { oneof with options := normalizeOneofOptions? oneof.options }

private def normalizeEnumValue
    (value : EnumValueDescriptorProto) : EnumValueDescriptorProto :=
  { value with options := normalizeEnumValueOptions? value.options }

private def normalizeEnum
    (enumeration : EnumDescriptorProto) : EnumDescriptorProto :=
  { enumeration with
    value := enumeration.value.map normalizeEnumValue
    options := normalizeEnumOptions? enumeration.options
  }

private def normalizeMethod
    (method : MethodDescriptorProto) : MethodDescriptorProto :=
  { method with options := normalizeMethodOptions? method.options }

private def normalizeService
    (service : ServiceDescriptorProto) : ServiceDescriptorProto :=
  { service with
    method := service.method.map normalizeMethod
    options := normalizeServiceOptions? service.options
  }

private def normalizeExtensionRange
    (range : DescriptorProto.ExtensionRange) :
    DescriptorProto.ExtensionRange :=
  { range with options := normalizeExtensionRangeOptions? range.options }

private partial def normalizeMessage
    (message : DescriptorProto) : DescriptorProto :=
  { message with
    field := message.field.map normalizeField
    extension := message.extension.map normalizeField
    nested_type := message.nested_type.map normalizeMessage
    enum_type := message.enum_type.map normalizeEnum
    extension_range := message.extension_range.map normalizeExtensionRange
    oneof_decl := message.oneof_decl.map normalizeOneof
    options := normalizeMessageOptions? message.options
  }

/--
Erase source information, built-in source-retention options, and custom
options from the comparison view of a file descriptor.

Custom option values are ignored only in this comparison view.  The merged
descriptor below keeps the values from `proto_file`, never the values from the
untrusted source descriptor.
-/
def normalizeForRuntimeComparison
    (file : FileDescriptorProto) : FileDescriptorProto :=
  { file with
    message_type := file.message_type.map normalizeMessage
    enum_type := file.enum_type.map normalizeEnum
    service := file.service.map normalizeService
    extension := file.extension.map normalizeField
    options := normalizeFileOptions? file.options
    source_code_info := none
  }

private def mergeSourceFeatures
    (runtime source : Option FeatureSet) : Option FeatureSet :=
  let sourceValue := source.getD {}
  let merged : FeatureSet :=
    { runtime.getD {} with
      enforce_naming_style := sourceValue.enforce_naming_style
      default_symbol_visibility := sourceValue.default_symbol_visibility
      enforce_proto_limits := sourceValue.enforce_proto_limits
    }
  keepIfEncodedNonempty FeatureSet.«protobuf.internal».encode merged

private def mergeFileOptions
    (runtime source : Option FileOptions) : Option FileOptions :=
  let sourceFeatures := source >>= (·.features)
  let merged :=
    { runtime.getD {} with
      features := mergeSourceFeatures (runtime >>= (·.features)) sourceFeatures
    }
  keepIfEncodedNonempty FileOptions.«protobuf.internal».encode merged

private def mergeMessageOptions
    (runtime source : Option MessageOptions) : Option MessageOptions :=
  let sourceFeatures := source >>= (·.features)
  let merged :=
    { runtime.getD {} with
      features := mergeSourceFeatures (runtime >>= (·.features)) sourceFeatures
    }
  keepIfEncodedNonempty MessageOptions.«protobuf.internal».encode merged

private def mergeFieldOptions
    (runtime source : Option FieldOptions) : Option FieldOptions :=
  let sourceFeatures := source >>= (·.features)
  let merged :=
    { runtime.getD {} with
      features := mergeSourceFeatures (runtime >>= (·.features)) sourceFeatures
    }
  keepIfEncodedNonempty FieldOptions.«protobuf.internal».encode merged

private def mergeOneofOptions
    (runtime source : Option OneofOptions) : Option OneofOptions :=
  let sourceFeatures := source >>= (·.features)
  let merged :=
    { runtime.getD {} with
      features := mergeSourceFeatures (runtime >>= (·.features)) sourceFeatures
    }
  keepIfEncodedNonempty OneofOptions.«protobuf.internal».encode merged

private def mergeEnumOptions
    (runtime source : Option EnumOptions) : Option EnumOptions :=
  let sourceFeatures := source >>= (·.features)
  let merged :=
    { runtime.getD {} with
      features := mergeSourceFeatures (runtime >>= (·.features)) sourceFeatures
    }
  keepIfEncodedNonempty EnumOptions.«protobuf.internal».encode merged

private def mergeEnumValueOptions
    (runtime source : Option EnumValueOptions) : Option EnumValueOptions :=
  let sourceFeatures := source >>= (·.features)
  let merged :=
    { runtime.getD {} with
      features := mergeSourceFeatures (runtime >>= (·.features)) sourceFeatures
    }
  keepIfEncodedNonempty EnumValueOptions.«protobuf.internal».encode merged

private def mergeServiceOptions
    (runtime source : Option ServiceOptions) : Option ServiceOptions :=
  let sourceFeatures := source >>= (·.features)
  let merged :=
    { runtime.getD {} with
      features := mergeSourceFeatures (runtime >>= (·.features)) sourceFeatures
    }
  keepIfEncodedNonempty ServiceOptions.«protobuf.internal».encode merged

private def mergeMethodOptions
    (runtime source : Option MethodOptions) : Option MethodOptions :=
  let sourceFeatures := source >>= (·.features)
  let merged :=
    { runtime.getD {} with
      features := mergeSourceFeatures (runtime >>= (·.features)) sourceFeatures
    }
  keepIfEncodedNonempty MethodOptions.«protobuf.internal».encode merged

private def mergeExtensionRangeOptions
    (runtime source : Option ExtensionRangeOptions) :
    Option ExtensionRangeOptions :=
  let sourceValue := source.getD {}
  let merged :=
    { runtime.getD {} with
      declaration := sourceValue.declaration
      verification := sourceValue.verification
      features :=
        mergeSourceFeatures
          (runtime >>= (·.features)) (source >>= (·.features))
    }
  keepIfEncodedNonempty
    ExtensionRangeOptions.«protobuf.internal».encode merged

private def mergeField
    (runtime source : FieldDescriptorProto) : FieldDescriptorProto :=
  { runtime with options := mergeFieldOptions runtime.options source.options }

private def mergeOneof
    (runtime source : OneofDescriptorProto) : OneofDescriptorProto :=
  { runtime with options := mergeOneofOptions runtime.options source.options }

private def mergeEnumValue
    (runtime source : EnumValueDescriptorProto) : EnumValueDescriptorProto :=
  { runtime with
    options := mergeEnumValueOptions runtime.options source.options
  }

private def mergeEnum
    (runtime source : EnumDescriptorProto) : EnumDescriptorProto :=
  { runtime with
    value := Array.zipWith mergeEnumValue runtime.value source.value
    options := mergeEnumOptions runtime.options source.options
  }

private def mergeMethod
    (runtime source : MethodDescriptorProto) : MethodDescriptorProto :=
  { runtime with
    options := mergeMethodOptions runtime.options source.options
  }

private def mergeService
    (runtime source : ServiceDescriptorProto) : ServiceDescriptorProto :=
  { runtime with
    method := Array.zipWith mergeMethod runtime.method source.method
    options := mergeServiceOptions runtime.options source.options
  }

private def mergeExtensionRange
    (runtime source : DescriptorProto.ExtensionRange) :
    DescriptorProto.ExtensionRange :=
  { runtime with
    options := mergeExtensionRangeOptions runtime.options source.options
  }

private partial def mergeMessage
    (runtime source : DescriptorProto) : DescriptorProto :=
  { runtime with
    field := Array.zipWith mergeField runtime.field source.field
    extension := Array.zipWith mergeField runtime.extension source.extension
    nested_type :=
      Array.zipWith mergeMessage runtime.nested_type source.nested_type
    enum_type := Array.zipWith mergeEnum runtime.enum_type source.enum_type
    extension_range :=
      Array.zipWith mergeExtensionRange
        runtime.extension_range source.extension_range
    oneof_decl :=
      Array.zipWith mergeOneof runtime.oneof_decl source.oneof_decl
    options := mergeMessageOptions runtime.options source.options
  }

/--
Copy only the built-in source-retention fields understood by this compiler
onto the authoritative runtime descriptor.

Callers must first establish `runtimeEquivalent`; the positional `zipWith`
operations are then over structurally identical descriptor arrays.
-/
def mergeSourceOnlyFields
    (runtime source : FileDescriptorProto) : FileDescriptorProto :=
  { runtime with
    message_type :=
      Array.zipWith mergeMessage runtime.message_type source.message_type
    enum_type := Array.zipWith mergeEnum runtime.enum_type source.enum_type
    service := Array.zipWith mergeService runtime.service source.service
    extension := Array.zipWith mergeField runtime.extension source.extension
    options := mergeFileOptions runtime.options source.options
  }

/--
Check that a source descriptor and its stripped runtime descriptor describe
the same schema and the same known runtime-retention options.
-/
def runtimeEquivalent
    (runtime source : FileDescriptorProto) : Except String Bool := do
  let runtimeBytes ←
    match
      FileDescriptorProto.«protobuf.internal».encode
        (normalizeForRuntimeComparison runtime) with
    | .ok bytes => pure bytes
    | .error err =>
        throw s!"cannot encode normalized proto_file descriptor: {err}"
  let sourceBytes ←
    match
      FileDescriptorProto.«protobuf.internal».encode
        (normalizeForRuntimeComparison source) with
    | .ok bytes => pure bytes
    | .error err =>
        throw
          s!"cannot encode normalized source_file_descriptors entry: {err}"
  return runtimeBytes == sourceBytes

end Protobuf.Plugin.DescriptorBoundary
