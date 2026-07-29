module

import Protobuf.Versions

open google.protobuf
open Protobuf.Versions
open Protobuf.Encoding

private def scalarField (name : String) (number : Int32) : FieldDescriptorProto := {
  name := some name
  number := some number
  label := some .LABEL_OPTIONAL
  type := some .TYPE_INT32
}

private def fileWithField (syntaxName : String) (field : FieldDescriptorProto) :
    FileDescriptorProto := {
  name := some s!"{syntaxName}.proto"
  «syntax» := some syntaxName
  message_type := #[{
    name := some "M"
    field := #[field]
  }]
}

private def editionsFileWithField (field : FieldDescriptorProto) : FileDescriptorProto := {
  fileWithField "editions" field with
  edition := some .EDITION_2023
}

private def compileResult (file : FileDescriptorProto) :=
  compile_proto { file := #[file] } |>.run

private def compileSetResult (files : Array FileDescriptorProto) :=
  compile_proto { file := files } |>.run

private def expectErrorContains (result : Except String α) (needle : String) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"expected error containing '{needle}'")
  | .error err =>
      unless err.contains needle do
        throw (IO.userError s!"expected error containing '{needle}', got '{err}'")

private def expectCompileSucceeds
    (file : FileDescriptorProto) (context : String) : IO Unit := do
  match compileResult file with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError s!"{context}: {err}")

private def testProto2PackedValidation : IO Unit := do
  let field := {
    scalarField "value" 1 with
    options := some { packed := some true }
  }
  expectErrorContains (compileResult (fileWithField "proto2" field))
    "packed is only valid on repeated fields"

private def testProto3RequiredValidation : IO Unit := do
  let field := { scalarField "value" 1 with label := some .LABEL_REQUIRED }
  expectErrorContains (compileResult (fileWithField "proto3" field))
    "LABEL_REQUIRED is not valid in proto3"

private def testProto3OptionalValidation : IO Unit := do
  let field := { scalarField "value" 1 with proto3_optional := some true }
  expectErrorContains (compileResult (fileWithField "proto3" field))
    "missing its synthetic oneof"

private def testOneofDescriptorValidation : IO Unit := do
  let emptyOneof : FileDescriptorProto := {
    name := some "empty-oneof.proto"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "M"
      oneof_decl := #[{ name := some "empty" }]
    }]
  }
  expectErrorContains (compileResult emptyOneof)
    "oneof `empty` has no fields"

  let invalidIndex : FileDescriptorProto := {
    emptyOneof with
    name := some "invalid-oneof-index.proto"
    message_type := #[{
      name := some "M"
      field := #[{ scalarField "value" 1 with oneof_index := some 1 }]
      oneof_decl := #[{ name := some "choice" }]
    }]
  }
  expectErrorContains (compileResult invalidIndex)
    "oneof_index 1 is out of bounds"

  let negativeIndex : FileDescriptorProto := {
    invalidIndex with
    name := some "negative-oneof-index.proto"
    message_type := #[{
      invalidIndex.message_type[0]! with
      field := #[{ scalarField "value" 1 with oneof_index := some (-1) }]
    }]
  }
  expectErrorContains (compileResult negativeIndex)
    "oneof_index -1 is out of bounds"

  let syntheticBeforeReal : FileDescriptorProto := {
    name := some "synthetic-oneof-order.proto"
    «syntax» := some "proto3"
    message_type := #[{
      name := some "M"
      field := #[
        {
          scalarField "optional_value" 1 with
          oneof_index := some 0
          proto3_optional := some true
        },
        { scalarField "real_value" 2 with oneof_index := some 1 }
      ]
      oneof_decl := #[
        { name := some "_optional_value" },
        { name := some "choice" }
      ]
    }]
  }
  expectErrorContains (compileResult syntheticBeforeReal)
    "synthetic oneofs must be ordered after all real oneofs"

  let validOrder : FileDescriptorProto := {
    syntheticBeforeReal with
    name := some "valid-oneof-order.proto"
    message_type := #[{
      name := some "M"
      field := #[
        { scalarField "real_value" 1 with oneof_index := some 0 },
        {
          scalarField "optional_value" 2 with
          oneof_index := some 1
          proto3_optional := some true
        }
      ]
      oneof_decl := #[
        { name := some "choice" },
        { name := some "_optional_value" }
      ]
    }]
  }
  expectCompileSucceeds validOrder "valid real/synthetic oneof ordering"

private def testStaticFieldNumberValidation : IO Unit := do
  expectErrorContains
    (compileResult (fileWithField "proto2" (scalarField "zero" 0)))
    "outside 1..536870911"
  expectErrorContains
    (compileResult (fileWithField "proto3" (scalarField "reserved" 19000)))
    "reserved range 19000..19999"
  let file : FileDescriptorProto := {
    name := some "duplicate.proto"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "M"
      field := #[scalarField "first" 1, scalarField "second" 1]
    }]
  }
  expectErrorContains (compileResult file) "field number 1 is declared more than once"

private def testProto3FirstEnumValueValidation : IO Unit := do
  let file : FileDescriptorProto := {
    name := some "enum.proto"
    «syntax» := some "proto3"
    enum_type := #[{
      name := some "E"
      value := #[{ name := some "NOT_ZERO", number := some 1 }]
    }]
  }
  expectErrorContains (compileResult file)
    "the first value of an open enum must be zero"

private def testEnumAliasAndReservedValidation : IO Unit := do
  let aliasFile : FileDescriptorProto := {
    name := some "enum-alias.proto"
    «syntax» := some "proto2"
    enum_type := #[{
      name := some "Alias"
      value := #[
        { name := some "FIRST", number := some 1 },
        { name := some "SECOND", number := some 1 }
      ]
    }]
  }
  expectErrorContains (compileResult aliasFile)
    "declared more than once without allow_alias"

  let reservedNumberFile : FileDescriptorProto := {
    name := some "enum-reserved-number.proto"
    «syntax» := some "proto2"
    enum_type := #[{
      name := some "ReservedNumber"
      value := #[{ name := some "VALUE", number := some 7 }]
      reserved_range := #[{ start := some 7, «end» := some 9 }]
    }]
  }
  expectErrorContains (compileResult reservedNumberFile)
    "enum numeric value 7 is reserved"

  let reservedNameFile : FileDescriptorProto := {
    name := some "enum-reserved-name.proto"
    «syntax» := some "proto2"
    enum_type := #[{
      name := some "ReservedName"
      value := #[{ name := some "VALUE", number := some 0 }]
      reserved_name := #["VALUE"]
    }]
  }
  expectErrorContains (compileResult reservedNameFile)
    "enum value name `VALUE` is reserved"

private def testDefaultTargetValidation : IO Unit := do
  let proto3Default := {
    scalarField "value" 1 with
    default_value := some "7"
  }
  expectErrorContains (compileResult (fileWithField "proto3" proto3Default))
    "explicit default values are not valid in proto3"

  let proto2RepeatedDefault := {
    scalarField "value" 1 with
    label := some .LABEL_REPEATED
    default_value := some "7"
  }
  expectErrorContains (compileResult (fileWithField "proto2" proto2RepeatedDefault))
    "default value is not valid on repeated fields"

  let proto2OneofDefault := {
    scalarField "value" 1 with
    oneof_index := some 0
    default_value := some "7"
  }
  let oneofFile : FileDescriptorProto := {
    name := some "oneof-default.proto"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "M"
      field := #[proto2OneofDefault]
      oneof_decl := #[{ name := some "choice" }]
    }]
  }
  expectErrorContains (compileResult oneofFile)
    "default value is not valid on oneof fields"

private def testIntegerDefaultRangeValidation : IO Unit := do
  let withDefault
      (fieldType : FieldDescriptorProto.Type) (raw : String) :
      FieldDescriptorProto := {
    scalarField "value" 1 with
    type := some fieldType
    default_value := some raw
  }
  expectErrorContains
    (compileResult
      (fileWithField "proto2" (withDefault .TYPE_INT32 "2147483648")))
    "outside the int32 range"
  expectErrorContains
    (compileResult
      (fileWithField "proto2" (withDefault .TYPE_UINT32 "-1")))
    "outside the uint32 range"
  expectErrorContains
    (compileResult
      (fileWithField "proto2"
        (withDefault .TYPE_INT64 "-9223372036854775809")))
    "outside the int64 range"
  expectErrorContains
    (compileResult
      (fileWithField "proto2"
        (withDefault .TYPE_UINT64 "18446744073709551616")))
    "outside the uint64 range"
  expectErrorContains
    (compileResult
      (fileWithField "proto2" (withDefault .TYPE_FIXED32 "08")))
    "invalid integer default value"

private def testDescriptorDefaultLexicalValidation : IO Unit := do
  let withDefault
      (fieldType : FieldDescriptorProto.Type) (raw : String) :
      FieldDescriptorProto := {
    scalarField "value" 1 with
    type := some fieldType
    default_value := some raw
  }
  -- C++ DescriptorPool's base-0 integer conversion accepts leading
  -- whitespace, but its end-pointer check rejects trailing whitespace.
  expectCompileSucceeds
    (fileWithField "proto2" (withDefault .TYPE_INT32 " 077"))
    "leading whitespace in a descriptor integer default"
  expectErrorContains
    (compileResult
      (fileWithField "proto2" (withDefault .TYPE_INT32 "077 ")))
    "invalid integer default value"
  for raw in #[" 1", "1 ", "+1"] do
    expectErrorContains
      (compileResult
        (fileWithField "proto2" (withDefault .TYPE_DOUBLE raw)))
      "invalid floating-point default value"
  for raw in #[" true", "true ", "\tfalse"] do
    expectErrorContains
      (compileResult
        (fileWithField "proto2" (withDefault .TYPE_BOOL raw)))
      "invalid boolean default value"

private def testReservedRangeLowerBound : IO Unit := do
  let file : FileDescriptorProto := {
    name := some "reserved-zero.proto"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "M"
      reserved_range := #[{ start := some 0, «end» := some 1 }]
    }]
  }
  expectErrorContains (compileResult file)
    "invalid reserved field range [0, 1)"

private def testReservedNameSurvivesSanitizing : IO Unit := do
  let file : FileDescriptorProto := {
    name := some "reserved-helper-name.proto"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "M"
      field := #[scalarField "builder" 1]
      reserved_name := #["builder"]
    }]
  }
  expectErrorContains (compileResult file)
    "field name `builder` is reserved"

private def testReservedSetValidation : IO Unit := do
  let duplicateMessageName : FileDescriptorProto := {
    name := some "duplicate-message-reserved-name.proto"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "M"
      reserved_name := #["value", "value"]
    }]
  }
  expectErrorContains (compileResult duplicateMessageName)
    "field name `value` is reserved more than once"

  let overlappingMessageRanges : FileDescriptorProto := {
    duplicateMessageName with
    name := some "overlapping-message-reserved-ranges.proto"
    message_type := #[{
      name := some "M"
      reserved_range := #[
        { start := some 1, «end» := some 4 },
        { start := some 3, «end» := some 6 }
      ]
    }]
  }
  expectErrorContains (compileResult overlappingMessageRanges)
    "reserved field ranges [3, 6) and [1, 4) overlap"

  let duplicateEnumName : FileDescriptorProto := {
    name := some "duplicate-enum-reserved-name.proto"
    «syntax» := some "proto2"
    enum_type := #[{
      name := some "E"
      value := #[{ name := some "X", number := some 0 }]
      reserved_name := #["Y", "Y"]
    }]
  }
  expectErrorContains (compileResult duplicateEnumName)
    "enum value name `Y` is reserved more than once"

  let overlappingEnumRanges : FileDescriptorProto := {
    duplicateEnumName with
    name := some "overlapping-enum-reserved-ranges.proto"
    enum_type := #[{
      name := some "E"
      value := #[{ name := some "X", number := some 0 }]
      reserved_range := #[
        { start := some 1, «end» := some 3 },
        { start := some 3, «end» := some 5 }
      ]
    }]
  }
  expectErrorContains (compileResult overlappingEnumRanges)
    "reserved enum ranges [3, 5] and [1, 3] overlap"

  let adjacentPositive : FileDescriptorProto := {
    name := some "adjacent-reserved-ranges.proto"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "M"
      reserved_range := #[
        { start := some 1, «end» := some 3 },
        { start := some 3, «end» := some 5 }
      ]
      reserved_name := #["first", "second"]
    }]
    enum_type := #[{
      name := some "E"
      value := #[{ name := some "X", number := some 0 }]
      reserved_range := #[
        { start := some 1, «end» := some 2 },
        { start := some 3, «end» := some 4 }
      ]
      reserved_name := #["Y", "Z"]
    }]
  }
  expectCompileSucceeds adjacentPositive
    "adjacent reserved ranges and distinct reserved names"

private def testEditionsOpenEnumFirstZeroValidation : IO Unit := do
  let file : FileDescriptorProto := {
    name := some "editions-open-enum.proto"
    «syntax» := some "editions"
    edition := some .EDITION_2023
    enum_type := #[{
      name := some "Open"
      value := #[{ name := some "NOT_ZERO", number := some 1 }]
    }]
  }
  expectErrorContains (compileResult file)
    "the first value of an open enum must be zero"

private def testEditionsLegacyPackedValidation : IO Unit := do
  let field := {
    scalarField "value" 1 with
    label := some .LABEL_REPEATED
    options := some { packed := some true }
  }
  expectErrorContains (compileResult (editionsFileWithField field))
    "legacy packed option is not valid in editions"

private def testEditionsImplicitDefaultValidation : IO Unit := do
  let field := {
    scalarField "value" 1 with
    default_value := some "7"
    options := some {
      features := some {
        field_presence := some .IMPLICIT
      }
    }
  }
  expectErrorContains (compileResult (editionsFileWithField field))
    "explicit default value requires explicit field presence"

private def testEditionsExtensionPresence : IO Unit := do
  let extensionField : FieldDescriptorProto := {
    scalarField "ext" 100 with
    extendee := some ".Host"
    default_value := some "7"
  }
  let base : FileDescriptorProto := {
    name := some "editions-extension-presence.proto"
    «syntax» := some "editions"
    edition := some .EDITION_2023
    options := some {
      features := some { field_presence := some .IMPLICIT }
    }
    message_type := #[{
      name := some "Host"
      extension_range := #[{ start := some 100, «end» := some 200 }]
    }]
    extension := #[extensionField]
  }
  /-
  This is the descriptor shape emitted by protoc 35: the file carries the
  implicit-presence feature, while the extension has `default_value` and no
  field-level feature override. Extensions retain explicit presence.
  -/
  expectCompileSucceeds base
    "extension default inherited the file's implicit field presence"

  let withExtensionPresence
      (presence : FeatureSet.FieldPresence) : FileDescriptorProto := {
    base with
    extension := #[{
      extensionField with
      options := some {
        features := some { field_presence := some presence }
      }
    }]
  }
  for presence in
      (#[FeatureSet.FieldPresence.EXPLICIT, .IMPLICIT] :
        Array FeatureSet.FieldPresence) do
    expectErrorContains
      (compileResult (withExtensionPresence presence))
      "extension fields cannot specify field_presence"
  expectErrorContains
    (compileResult (withExtensionPresence .LEGACY_REQUIRED))
    "extension fields cannot be required"

private def testGroupDescriptorValidation : IO Unit := do
  let groupField : FieldDescriptorProto := {
    name := some "child"
    number := some 1
    label := some .LABEL_OPTIONAL
    type := some .TYPE_GROUP
    type_name := some ".p.Parent.Child"
  }
  let proto2Group : FileDescriptorProto := {
    name := some "valid-group.proto"
    package := some "p"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "Parent"
      field := #[groupField]
      nested_type := #[{
        name := some "Child"
        field := #[scalarField "value" 1]
      }]
    }]
  }
  expectCompileSucceeds proto2Group
    "valid proto2 group descriptor was rejected"

  expectErrorContains
    (compileResult {
      proto2Group with
      «syntax» := some "proto3"
    })
    "groups are not supported"
  expectErrorContains
    (compileResult {
      proto2Group with
      «syntax» := some "editions"
      edition := some .EDITION_2023
    })
    "groups are not supported"

  let groupInOneof : FileDescriptorProto := {
    proto2Group with
    message_type := #[{
      proto2Group.message_type[0]! with
      field := #[{ groupField with oneof_index := some 0 }]
      oneof_decl := #[{ name := some "choice" }]
    }]
  }
  expectErrorContains (compileResult groupInOneof)
    "group fields cannot appear in oneofs"

  let packedGroup : FileDescriptorProto := {
    proto2Group with
    message_type := #[{
      proto2Group.message_type[0]! with
      field := #[{
        groupField with
        label := some .LABEL_REPEATED
        options := some { packed := some true }
      }]
    }]
  }
  expectErrorContains (compileResult packedGroup)
    "packed is not valid for this field type"

  let defaultGroup : FileDescriptorProto := {
    proto2Group with
    message_type := #[{
      proto2Group.message_type[0]! with
      field := #[{ groupField with default_value := some "value" }]
    }]
  }
  expectErrorContains (compileResult defaultGroup)
    "default option is not supported for group fields"

private def testEditionsMessageEncodingValidation : IO Unit := do
  let explicitDelimited : FeatureSet := {
    message_encoding := some .DELIMITED
  }
  let scalar := {
    scalarField "value" 1 with
    options := some { features := some explicitDelimited }
  }
  expectErrorContains (compileResult (editionsFileWithField scalar))
    "only message fields can specify message_encoding"

  let messageScoped : FileDescriptorProto := {
    name := some "message-scoped-delimited.proto"
    «syntax» := some "editions"
    edition := some .EDITION_2023
    message_type := #[{
      name := some "M"
      options := some { features := some explicitDelimited }
      field := #[scalarField "value" 1]
    }]
  }
  expectErrorContains (compileResult messageScoped)
    "message_encoding can only be set on files or message fields"

  let oneofScoped : FileDescriptorProto := {
    name := some "oneof-scoped-delimited.proto"
    «syntax» := some "editions"
    edition := some .EDITION_2023
    message_type := #[{
      name := some "M"
      field := #[{
        scalarField "value" 1 with
        oneof_index := some 0
      }]
      oneof_decl := #[{
        name := some "choice"
        options := some { features := some explicitDelimited }
      }]
    }]
  }
  expectErrorContains (compileResult oneofScoped)
    "message_encoding can only be set on files or message fields"

  let mapFile : FileDescriptorProto := {
    name := some "delimited-map.proto"
    package := some "p"
    «syntax» := some "editions"
    edition := some .EDITION_2023
    message_type := #[{
      name := some "M"
      field := #[{
        name := some "items"
        number := some 1
        label := some .LABEL_REPEATED
        type := some .TYPE_MESSAGE
        type_name := some ".p.M.ItemsEntry"
        options := some { features := some explicitDelimited }
      }]
      nested_type := #[{
        name := some "ItemsEntry"
        field := #[
          {
            name := some "key"
            number := some 1
            label := some .LABEL_OPTIONAL
            type := some .TYPE_STRING
          },
          {
            name := some "value"
            number := some 2
            label := some .LABEL_OPTIONAL
            type := some .TYPE_INT32
          }
        ]
        options := some { map_entry := some true }
      }]
    }]
  }
  expectErrorContains
    (compileResult mapFile)
    "map fields cannot specify message_encoding"

  /-
  Official protoc permits file-level DELIMITED.  It applies to message-valued
  fields and is ignored for scalars inherited through the same scope.
  -/
  let inherited : FileDescriptorProto := {
    name := some "file-delimited.proto"
    package := some "p"
    «syntax» := some "editions"
    edition := some .EDITION_2023
    options := some { features := some explicitDelimited }
    message_type := #[
      {
        name := some "Payload"
        field := #[scalarField "value" 1]
      },
      {
        name := some "Fields"
        field := #[
          scalarField "scalar" 1,
          {
            name := some "payload"
            number := some 2
            label := some .LABEL_OPTIONAL
            type := some .TYPE_MESSAGE
            type_name := some ".p.Payload"
          }
        ]
      }
    ]
  }
  expectCompileSucceeds inherited
    "valid inherited file-level message_encoding was rejected"

private def testBuiltinFeatureTargetValidation : IO Unit := do
  let editionsFile
      (fileName : String) (edition : Edition := .EDITION_2024) :
      FileDescriptorProto := {
    name := some fileName
    «syntax» := some "editions"
    edition := some edition
  }
  let featureOptions (features : FeatureSet) : FileOptions :=
    { features := some features }
  let expectWrongTarget
      (file : FileDescriptorProto) (target : String) : IO Unit :=
    expectErrorContains (compileResult file) s!"not {target}"

  -- Exercise every descriptor options container with a built-in feature that
  -- does not target that container.
  expectWrongTarget {
    editionsFile "feature-file-target.proto" .EDITION_2026 with
    options := some (featureOptions {
      enforce_proto_limits := some .PROTO_LIMITS2026
    })
  } "file"
  expectWrongTarget {
    editionsFile "feature-extension-range-target.proto" with
    message_type := #[{
      name := some "M"
      extension_range := #[{
        start := some 100
        «end» := some 200
        options := some {
          features := some { field_presence := some .EXPLICIT }
        }
      }]
    }]
  } "extension range"
  expectWrongTarget {
    editionsFile "feature-message-target.proto" with
    message_type := #[{
      name := some "M"
      options := some {
        features := some {
          default_symbol_visibility := some .EXPORT_ALL
        }
      }
    }]
  } "message"
  expectWrongTarget {
    editionsFile "feature-field-target.proto" with
    message_type := #[{
      name := some "M"
      field := #[{
        scalarField "value" 1 with
        options := some {
          features := some { enum_type := some .OPEN }
        }
      }]
    }]
  } "field"
  expectWrongTarget {
    editionsFile "feature-oneof-target.proto" with
    message_type := #[{
      name := some "M"
      field := #[{
        scalarField "value" 1 with oneof_index := some 0
      }]
      oneof_decl := #[{
        name := some "choice"
        options := some {
          features := some { json_format := some .ALLOW }
        }
      }]
    }]
  } "oneof"
  expectWrongTarget {
    editionsFile "feature-enum-target.proto" with
    enum_type := #[{
      name := some "E"
      value := #[{ name := some "ZERO", number := some 0 }]
      options := some {
        features := some {
          repeated_field_encoding := some .PACKED
        }
      }
    }]
  } "enum"
  expectWrongTarget {
    editionsFile "feature-enum-entry-target.proto" with
    enum_type := #[{
      name := some "E"
      value := #[{
        name := some "ZERO"
        number := some 0
        options := some {
          features := some { utf8_validation := some .VERIFY }
        }
      }]
    }]
  } "enum entry"
  expectWrongTarget {
    editionsFile "feature-service-target.proto" with
    service := #[{
      name := some "Api"
      options := some {
        features := some {
          message_encoding := some .LENGTH_PREFIXED
        }
      }
    }]
  } "service"
  expectWrongTarget {
    editionsFile "feature-method-target.proto" with
    message_type := #[{ name := some "Request" }]
    service := #[{
      name := some "Api"
      method := #[{
        name := some "Call"
        input_type := some ".Request"
        output_type := some ".Request"
        options := some {
          features := some { field_presence := some .EXPLICIT }
        }
      }]
    }]
  } "method"

  let naming : FeatureSet := {
    enforce_naming_style := some .STYLE_LEGACY
  }
  let validAllTargets : FileDescriptorProto := {
    editionsFile "feature-valid-targets.proto" with
    options := some (featureOptions {
      field_presence := some .EXPLICIT
      enum_type := some .OPEN
      repeated_field_encoding := some .PACKED
      utf8_validation := some .VERIFY
      message_encoding := some .LENGTH_PREFIXED
      json_format := some .ALLOW
      enforce_naming_style := some .STYLE_LEGACY
      default_symbol_visibility := some .EXPORT_TOP_LEVEL
    })
    message_type := #[
      { name := some "Payload" },
      {
        name := some "M"
        options := some {
          features := some {
            json_format := some .ALLOW
            enforce_naming_style := some .STYLE_LEGACY
          }
        }
        field := #[
          {
            name := some "payload"
            number := some 1
            label := some .LABEL_OPTIONAL
            type := some .TYPE_MESSAGE
            type_name := some ".Payload"
            options := some {
              features := some {
                field_presence := some .EXPLICIT
                repeated_field_encoding := some .PACKED
                utf8_validation := some .VERIFY
                message_encoding := some .LENGTH_PREFIXED
                enforce_naming_style := some .STYLE_LEGACY
              }
            }
          },
          {
            scalarField "choice_value" 2 with
            oneof_index := some 0
          }
        ]
        extension_range := #[{
          start := some 100
          «end» := some 200
          options := some { features := some naming }
        }]
        oneof_decl := #[{
          name := some "choice"
          options := some { features := some naming }
        }]
      }
    ]
    enum_type := #[{
      name := some "E"
      value := #[{
        name := some "ZERO"
        number := some 0
        options := some { features := some naming }
      }]
      options := some {
        features := some {
          enum_type := some .OPEN
          json_format := some .ALLOW
          enforce_naming_style := some .STYLE_LEGACY
        }
      }
    }]
    service := #[{
      name := some "Api"
      options := some { features := some naming }
      method := #[{
        name := some "Call"
        input_type := some ".Payload"
        output_type := some ".Payload"
        options := some { features := some naming }
      }]
    }]
  }
  expectCompileSucceeds validAllTargets
    "valid built-in feature targets"

  -- Edition 2026 is not yet a code-generation frontend, so exercise the four
  -- valid enforce_proto_limits targets through descriptor normalization.
  let limits : FeatureSet := {
    enforce_proto_limits := some .PROTO_LIMITS2026
  }
  let validLimits : FileDescriptorProto := {
    editionsFile "feature-valid-proto-limits.proto" .EDITION_2026 with
    message_type := #[{
      name := some "M"
      options := some { features := some limits }
      field := #[{
        scalarField "value" 1 with
        oneof_index := some 0
        options := some { features := some limits }
      }]
      oneof_decl := #[{
        name := some "choice"
        options := some { features := some limits }
      }]
    }]
    enum_type := #[{
      name := some "E"
      value := #[{ name := some "ZERO", number := some 0 }]
      options := some { features := some limits }
    }]
  }
  match normalizeFileDescriptorSet { file := #[validLimits] } |>.run with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"valid Edition 2026 enforce_proto_limits targets were rejected: {err}")

  let unknownFileFeatures : Array FeatureSet := #[
    { field_presence := some .FIELD_PRESENCE_UNKNOWN },
    {
      field_presence :=
        some (FeatureSet.FieldPresence.«Unknown.Value» 12345)
    },
    { enum_type := some .ENUM_TYPE_UNKNOWN },
    {
      enum_type :=
        some (FeatureSet.EnumType.«Unknown.Value» 12345)
    },
    {
      repeated_field_encoding :=
        some .REPEATED_FIELD_ENCODING_UNKNOWN
    },
    {
      repeated_field_encoding :=
        some (FeatureSet.RepeatedFieldEncoding.«Unknown.Value» 12345)
    },
    { utf8_validation := some .UTF8_VALIDATION_UNKNOWN },
    {
      utf8_validation :=
        some (FeatureSet.Utf8Validation.«Unknown.Value» 12345)
    },
    { message_encoding := some .MESSAGE_ENCODING_UNKNOWN },
    {
      message_encoding :=
        some (FeatureSet.MessageEncoding.«Unknown.Value» 12345)
    },
    { json_format := some .JSON_FORMAT_UNKNOWN },
    {
      json_format :=
        some (FeatureSet.JsonFormat.«Unknown.Value» 12345)
    },
    {
      enforce_naming_style :=
        some .ENFORCE_NAMING_STYLE_UNKNOWN
    },
    {
      enforce_naming_style :=
        some (FeatureSet.EnforceNamingStyle.«Unknown.Value» 12345)
    },
    {
      default_symbol_visibility :=
        some .DEFAULT_SYMBOL_VISIBILITY_UNKNOWN
    },
    {
      default_symbol_visibility :=
        some
          (FeatureSet.VisibilityFeature.DefaultSymbolVisibility.«Unknown.Value»
            12345)
    }
  ]
  for features in unknownFileFeatures do
    expectErrorContains
      (compileResult {
        editionsFile "feature-unknown-file-value.proto" with
        options := some (featureOptions features)
      })
      "must have a known nonzero value"
  let unknownLimitFeatures : Array FeatureSet := #[
    { enforce_proto_limits := some .PROTO_LIMITS_UNKNOWN },
    {
      enforce_proto_limits :=
        some
          (FeatureSet.ProtoLimitsFeature.EnforceProtoLimits.«Unknown.Value»
            12345)
    }
  ]
  for features in unknownLimitFeatures do
    expectErrorContains
      (compileResult {
        editionsFile "feature-unknown-limit-value.proto"
          .EDITION_2026 with
        message_type := #[{
          name := some "M"
          options := some { features := some features }
        }]
      })
      "must have a known nonzero value"

  expectErrorContains
    (compileResult {
      editionsFile "feature-naming-before-2024.proto" .EDITION_2023 with
      options := some (featureOptions {
        enforce_naming_style := some .STYLE2024
      })
    })
    "enforce_naming_style is not supported before Edition 2024"
  expectErrorContains
    (compileResult {
      editionsFile "feature-limits-before-2026.proto" with
      message_type := #[{
        name := some "M"
        options := some { features := some limits }
      }]
    })
    "enforce_proto_limits is not supported before Edition 2026"
  for syntaxName in #["proto2", "proto3"] do
    expectErrorContains
      (compileResult {
        name := some s!"feature-{syntaxName}.proto"
        «syntax» := some syntaxName
        options := some (featureOptions {
          field_presence := some .EXPLICIT
        })
      })
      "built-in feature `field_presence` is only valid under editions syntax"

  let customOnly : FeatureSet := {
    «Unknown.Fields» :=
      ({} : Std.HashMap Nat (Array ProtoVal)).insert 1000
        #[.LEN ByteArray.empty]
  }
  let customFeatureFile : FileDescriptorProto := {
    name := some "feature-custom-only.proto"
    «syntax» := some "proto2"
    options := some (featureOptions customOnly)
    message_type := #[{
      name := some "M"
      options := some { features := some customOnly }
    }]
  }
  expectCompileSucceeds customFeatureFile
    "unknown/custom FeatureSet fields must not be rejected"
  expectCompileSucceeds {
    customFeatureFile with
    name := some "feature-empty-set.proto"
    options := some (featureOptions {})
    message_type := #[{
      name := some "M"
      options := some { features := some {} }
    }]
  } "empty FeatureSet containers must not be rejected"

private def testEditionsClosedEnumSupport : IO Unit := do
  let file : FileDescriptorProto := {
    name := some "closed.proto"
    «syntax» := some "editions"
    edition := some .EDITION_2023
    options := some {
      features := some {
        enum_type := some .CLOSED
      }
    }
    enum_type := #[{
      name := some "E"
      value := #[{
        name := some "E_ZERO"
        number := some 0
      }]
    }]
  }
  match compileResult file with
  | .ok commands =>
      unless commands.size == 1 do
        throw (IO.userError "Editions CLOSED enum did not produce one declaration")
  | .error err =>
      throw (IO.userError s!"Editions CLOSED enum was rejected: {err}")

private def syntheticMapKey : FieldDescriptorProto := {
  name := some "key"
  number := some 1
  label := some .LABEL_OPTIONAL
  type := some .TYPE_STRING
}

private def syntheticMapValue : FieldDescriptorProto := {
  name := some "value"
  number := some 2
  label := some .LABEL_OPTIONAL
  type := some .TYPE_INT32
}

private def syntheticMapEntry
    (name : String := "ItemsEntry")
    (fields : Array FieldDescriptorProto := #[syntheticMapKey, syntheticMapValue]) :
    DescriptorProto := {
  name := some name
  field := fields
  options := some { map_entry := some true }
}

private def syntheticMapOwner
    (name : String := "items") (typeName : String := ".p.M.ItemsEntry") :
    FieldDescriptorProto := {
  name := some name
  number := some 1
  label := some .LABEL_REPEATED
  type := some .TYPE_MESSAGE
  type_name := some typeName
}

private def syntheticMapFile
    (syntaxName : String) (entry : DescriptorProto := syntheticMapEntry)
    (owner : FieldDescriptorProto := syntheticMapOwner) : FileDescriptorProto := {
  name := some s!"map-entry-{syntaxName}.proto"
  package := some "p"
  «syntax» := some syntaxName
  edition := if syntaxName == "editions" then some .EDITION_2023 else none
  message_type := #[{
    name := some "M"
    field := #[owner]
    nested_type := #[entry]
  }]
}

private def expectCompileOk (file : FileDescriptorProto) : IO Unit := do
  match compileResult file with
  | .ok _ => pure ()
  | .error err => throw (IO.userError s!"valid synthetic map descriptor was rejected: {err}")

private def testSyntheticMapEntryValidation : IO Unit := do
  -- The shared validator is used by all three descriptor dialect frontends.
  expectCompileOk (syntheticMapFile "proto2")
  expectCompileOk (syntheticMapFile "proto3")
  expectCompileOk (syntheticMapFile "editions")
  -- Helper-name sanitization must not change protoc's synthetic type spelling.
  expectCompileOk
    (syntheticMapFile "proto3"
      (syntheticMapEntry "BuilderEntry")
      (syntheticMapOwner "builder" ".p.M.BuilderEntry"))
  -- FieldDescriptorProto permits C++-style relative type names.  DescriptorPool
  -- accepts all three spellings below for the same nested synthetic entry.
  for typeName in #["ItemsEntry", "M.ItemsEntry", "p.M.ItemsEntry"] do
    expectCompileOk
      (syntheticMapFile "proto3" (owner := syntheticMapOwner (typeName := typeName)))

  expectErrorContains
    (compileResult
      (syntheticMapFile "proto3"
        (syntheticMapEntry (fields :=
          #[syntheticMapKey, syntheticMapValue, scalarField "extra" 3]))))
    "exactly two fields"
  expectErrorContains
    (compileResult
      (syntheticMapFile "proto3"
        (syntheticMapEntry (fields := #[syntheticMapValue, syntheticMapKey]))))
    "map key field must be named `key`"
  expectErrorContains
    (compileResult
      (syntheticMapFile "proto3"
        (syntheticMapEntry (fields :=
          #[{ syntheticMapKey with number := some 7 }, syntheticMapValue]))))
    "map key field must have number 1"
  expectErrorContains
    (compileResult
      (syntheticMapFile "proto3"
        (syntheticMapEntry (fields :=
          #[syntheticMapKey, { syntheticMapValue with label := some .LABEL_REPEATED }]))))
    "map value field must have label LABEL_OPTIONAL"
  expectErrorContains
    (compileResult
      (syntheticMapFile "proto3"
        (syntheticMapEntry (fields :=
          #[{ syntheticMapKey with type := some .TYPE_BYTES }, syntheticMapValue]))))
    "illegal map key type"
  expectErrorContains
    (compileResult
      (syntheticMapFile "proto3"
        (syntheticMapEntry (fields :=
          #[{ syntheticMapKey with extendee := some ".p.M" }, syntheticMapValue]))))
    "synthetic map fields cannot set extendee"
  expectErrorContains
    (compileResult
      (syntheticMapFile "proto3"
        { syntheticMapEntry with oneof_decl := #[{ name := some "choice" }] }))
    "map entry cannot declare oneofs"
  expectErrorContains
    (compileResult
      (syntheticMapFile "proto2"
        (syntheticMapEntry (fields :=
          #[syntheticMapKey, { syntheticMapValue with default_value := some "0" }]))))
    "synthetic map fields cannot have explicit defaults"
  expectErrorContains
    (compileResult
      (syntheticMapFile "proto3"
        { syntheticMapEntry with nested_type := #[{ name := some "Nested" }] }))
    "map entry cannot declare nested messages or enums"
  expectErrorContains
    (compileResult
      (syntheticMapFile "proto3"
        (syntheticMapEntry "WrongEntry")
        (syntheticMapOwner (typeName := ".p.M.WrongEntry"))))
    "map entry name must be `ItemsEntry`"
  expectErrorContains
    (compileResult
      (syntheticMapFile "proto3" (owner :=
        { syntheticMapOwner with label := some .LABEL_OPTIONAL })))
    "map field must have label LABEL_REPEATED"
  expectErrorContains
    (compileResult
      (syntheticMapFile "proto3" (owner :=
        { syntheticMapOwner with oneof_index := some 0 })))
    "map field cannot be an extension, oneof member, defaulted, or proto3_optional"

  let nonzeroEnumFile : FileDescriptorProto := {
    name := some "nonzero-enum.proto"
    package := some "enum_pkg"
    «syntax» := some "proto2"
    enum_type := #[{
      name := some "Nonzero"
      value := #[{ name := some "ONE", number := some 1 }]
    }]
  }
  let enumMapFile : FileDescriptorProto := {
    syntheticMapFile "proto2"
      (syntheticMapEntry (fields := #[
        syntheticMapKey,
        {
          syntheticMapValue with
          type := some .TYPE_ENUM
          type_name := some ".enum_pkg.Nonzero"
        }
      ])) with
    name := some "enum-map.proto"
    dependency := #["nonzero-enum.proto"]
  }
  expectErrorContains
    (compile_proto { file := #[nonzeroEnumFile, enumMapFile] } |>.run)
    "must define numeric value 0 as its first value"

  let nestedMapValueFile : FileDescriptorProto := {
    name := some "nested-map-value.proto"
    package := some "p"
    «syntax» := some "proto3"
    message_type := #[
      {
        name := some "M"
        field := #[syntheticMapOwner]
        nested_type := #[
          syntheticMapEntry (fields := #[
            syntheticMapKey,
            {
              syntheticMapValue with
              type := some .TYPE_MESSAGE
              type_name := some ".p.N.OthersEntry"
            }
          ])
        ]
      },
      {
        name := some "N"
        field := #[
          {
            syntheticMapOwner "others" ".p.N.OthersEntry" with
            number := some 1
          }
        ]
        nested_type := #[syntheticMapEntry "OthersEntry"]
      }
    ]
  }
  expectErrorContains (compileResult nestedMapValueFile)
    "map values cannot be another map"

  let unreferenced : FileDescriptorProto := {
    syntheticMapFile "proto3" with
    message_type := #[{
      name := some "M"
      nested_type := #[syntheticMapEntry]
    }]
  }
  expectErrorContains (compileResult unreferenced)
    "map entry must be referenced by exactly one field"

  let topLevel : FileDescriptorProto := {
    name := some "top-level-map-entry.proto"
    «syntax» := some "proto3"
    message_type := #[syntheticMapEntry]
  }
  expectErrorContains (compileResult topLevel)
    "map_entry messages must be nested"

private def descriptorExtensionRange
    (start finish : Int32) : DescriptorProto.ExtensionRange := {
  start := some start
  «end» := some finish
}

private def descriptorExtensionField
    (name : String) (number : Int32) (extendee : String) :
    FieldDescriptorProto := {
  name := some name
  number := some number
  label := some .LABEL_OPTIONAL
  type := some .TYPE_INT32
  extendee := some extendee
}

private def extensionHostFile
    (ranges : Array DescriptorProto.ExtensionRange)
    (fields : Array FieldDescriptorProto := #[])
    (reserved : Array DescriptorProto.ReservedRange := #[]) :
    FileDescriptorProto := {
  name := some "host.proto"
  package := some "host.pkg"
  «syntax» := some "proto2"
  message_type := #[{
    name := some "Host"
    field := fields
    extension_range := ranges
    reserved_range := reserved
  }]
}

private def extensionFile
    (fileName packageName fieldName : String) (number : Int32)
    (extendee : String := ".host.pkg.Host") :
    FileDescriptorProto := {
  name := some fileName
  package := some packageName
  dependency := #["host.proto"]
  «syntax» := some "proto2"
  extension := #[descriptorExtensionField fieldName number extendee]
}

private def testDescriptorSetExtensionValidation : IO Unit := do
  let host :=
    extensionHostFile #[descriptorExtensionRange 100 200]
  let fileScoped :=
    extensionFile "file-extension.proto" "file.ext" "file_value" 123
  let nestedScoped : FileDescriptorProto := {
    name := some "nested-extension.proto"
    package := some "nested.ext"
    dependency := #["host.proto"]
    «syntax» := some "proto2"
    message_type := #[{
      name := some "Scope"
      extension := #[
        descriptorExtensionField "nested_value" 124 ".host.pkg.Host"
      ]
    }]
  }
  match compileSetResult #[host, fileScoped, nestedScoped] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError s!"valid cross-file extensions were rejected: {err}")

  -- Extension numbers are unique within an extendee, not within the lexical
  -- scope that declares the extensions.  Protoc accepts the same number for
  -- two different messages even when both extensions are file-scoped.
  let twoHosts : FileDescriptorProto := {
    name := some "two-hosts.proto"
    package := some "two.hosts"
    «syntax» := some "proto2"
    message_type := #[
      {
        name := some "First"
        extension_range := #[descriptorExtensionRange 100 200]
      },
      {
        name := some "Second"
        extension_range := #[descriptorExtensionRange 100 200]
      }
    ]
    extension := #[
      descriptorExtensionField "first_value" 100 ".two.hosts.First",
      descriptorExtensionField "second_value" 100 ".two.hosts.Second"
    ]
  }
  match compileSetResult #[twoHosts] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"extensions on different extendees were incorrectly treated as a tag collision: {err}")

  expectErrorContains
    (compileSetResult #[
      host,
      extensionFile "missing.proto" "missing.ext" "bad" 123 ".host.pkg.Missing"
    ])
    "does not name a message in the descriptor set"

  expectErrorContains
    (compileSetResult #[
      host,
      extensionFile "outside.proto" "outside.ext" "bad" 99
    ])
    "outside every extension range"

  expectErrorContains
    (compileSetResult #[
      host,
      extensionFile "first.proto" "first.ext" "first" 125,
      extensionFile "second.proto" "second.ext" "second" 125
    ])
    "extension number 125 for `host.pkg.Host` is already declared"

  expectErrorContains
    (compileSetResult #[
      extensionHostFile #[descriptorExtensionRange 0 10]
    ])
    "invalid extension range [0, 10)"

  expectErrorContains
    (compileSetResult #[
      extensionHostFile #[
        descriptorExtensionRange 100 150,
        descriptorExtensionRange 149 200
      ]
    ])
    "extension ranges [149, 200) and [100, 150) overlap"

  expectErrorContains
    (compileSetResult #[
      extensionHostFile
        #[descriptorExtensionRange 100 200]
        #[scalarField "ordinary" 150]
    ])
    "field number 150 is inside extension range"

  expectErrorContains
    (compileSetResult #[
      extensionHostFile
        #[descriptorExtensionRange 100 200]
        #[]
        #[{ start := some 150, «end» := some 160 }]
    ])
    "extension range [100, 200) overlaps reserved range [150, 160)"

private def testWholeSetSymbolUniqueness : IO Unit := do
  let serviceVsMessage : FileDescriptorProto := {
    name := some "service-vs-message.proto"
    package := some "symbols"
    «syntax» := some "proto2"
    message_type := #[{ name := some "Api" }]
    service := #[{ name := some "Api" }]
  }
  expectErrorContains (compileResult serviceVsMessage)
    "protobuf symbol `symbols.Api` is declared more than once"

  let packageVsRootType : FileDescriptorProto := {
    name := some "package-p-q.proto"
    package := some "package_scope.q"
    «syntax» := some "proto2"
    message_type := #[{ name := some "Inside" }]
  }
  let rootPackagePrefixType : FileDescriptorProto := {
    name := some "root-package-prefix.proto"
    «syntax» := some "proto2"
    message_type := #[{ name := some "package_scope" }]
  }
  expectErrorContains
    (compileSetResult #[packageVsRootType, rootPackagePrefixType])
    "protobuf symbol `package_scope` is declared more than once"
  let packageComponentType : FileDescriptorProto := {
    name := some "package-component-type.proto"
    package := some "package_scope"
    «syntax» := some "proto2"
    message_type := #[{ name := some "q" }]
  }
  expectErrorContains
    (compileSetResult #[packageComponentType, packageVsRootType])
    "protobuf symbol `package_scope.q` is declared more than once"

  let serviceFile (fileName packageName : String) : FileDescriptorProto := {
    name := some fileName
    package := some packageName
    «syntax» := some "proto2"
    service := #[{ name := some "Api" }]
  }
  expectErrorContains
    (compileSetResult #[
      serviceFile "service-first.proto" "symbols",
      serviceFile "service-second.proto" "symbols"
    ])
    "protobuf symbol `symbols.Api` is declared more than once"

  let duplicateMethod : FileDescriptorProto := {
    name := some "duplicate-method.proto"
    package := some "symbols"
    «syntax» := some "proto2"
    message_type := #[{ name := some "Request" }]
    service := #[{
      name := some "Api"
      method := #[
        {
          name := some "Call"
          input_type := some ".symbols.Request"
          output_type := some ".symbols.Request"
        },
        {
          name := some "Call"
          input_type := some ".symbols.Request"
          output_type := some ".symbols.Request"
        }
      ]
    }]
  }
  expectErrorContains (compileResult duplicateMethod)
    "protobuf symbol `symbols.Api.Call` is declared more than once"

  let duplicateEnumValue : FileDescriptorProto := {
    name := some "duplicate-enum-value.proto"
    package := some "symbols"
    «syntax» := some "proto2"
    enum_type := #[
      {
        name := some "First"
        value := #[{ name := some "VALUE", number := some 0 }]
      },
      {
        name := some "Second"
        value := #[{ name := some "VALUE", number := some 0 }]
      }
    ]
  }
  expectErrorContains (compileResult duplicateEnumValue)
    "protobuf symbol `symbols.VALUE` is declared more than once"

  let enumValueVsType : FileDescriptorProto := {
    duplicateEnumValue with
    name := some "enum-value-vs-type.proto"
    enum_type := #[{
      name := some "Kind"
      value := #[{ name := some "Sibling", number := some 0 }]
    }]
    message_type := #[{ name := some "Sibling" }]
  }
  expectErrorContains (compileResult enumValueVsType)
    "protobuf symbol `symbols.Sibling` is declared more than once"

  let fieldVsNestedType : FileDescriptorProto := {
    name := some "field-vs-nested-type.proto"
    package := some "symbols"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "Container"
      field := #[scalarField "Nested" 1]
      nested_type := #[{ name := some "Nested" }]
    }]
  }
  expectErrorContains (compileResult fieldVsNestedType)
    "protobuf symbol `symbols.Container.Nested` is declared more than once"

  let fieldVsOneof : FileDescriptorProto := {
    fieldVsNestedType with
    name := some "field-vs-oneof.proto"
    message_type := #[{
      name := some "Container"
      field := #[{ scalarField "choice" 1 with oneof_index := some 0 }]
      oneof_decl := #[{ name := some "choice" }]
    }]
  }
  expectErrorContains (compileResult fieldVsOneof)
    "protobuf symbol `symbols.Container.choice` is declared more than once"

  let extensionHost : FileDescriptorProto := {
    name := some "symbol-host.proto"
    package := some "symbols"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "Host"
      extension_range := #[descriptorExtensionRange 100 200]
    }]
  }
  let symbolExtension (fileName : String) (number : Int32) :
      FileDescriptorProto := {
    name := some fileName
    package := some "symbols"
    dependency := #["symbol-host.proto"]
    «syntax» := some "proto2"
    extension := #[
      descriptorExtensionField "extension_value" number ".symbols.Host"
    ]
  }
  expectErrorContains
    (compileSetResult #[
      extensionHost,
      symbolExtension "symbol-extension-first.proto" 100,
      symbolExtension "symbol-extension-second.proto" 101
    ])
    "protobuf symbol `symbols.extension_value` is declared more than once"

  let scopedExtensionCollision : FileDescriptorProto := {
    extensionHost with
    name := some "scoped-extension-collision.proto"
    message_type := #[
      extensionHost.message_type[0]!,
      {
        name := some "Container"
        field := #[scalarField "nested_extension" 1]
        extension := #[
          descriptorExtensionField
            "nested_extension" 100 ".symbols.Host"
        ]
      }
    ]
  }
  expectErrorContains (compileResult scopedExtensionCollision)
    "protobuf symbol `symbols.Container.nested_extension` is declared more than once"

  let sharedMethodNamePositive : FileDescriptorProto := {
    name := some "shared-method-name.proto"
    package := some "positive"
    «syntax» := some "proto2"
    message_type := #[
      { name := some "Request" },
      {
        name := some "FirstScope"
        enum_type := #[{
          name := some "Kind"
          value := #[{ name := some "VALUE", number := some 0 }]
        }]
      },
      {
        name := some "SecondScope"
        enum_type := #[{
          name := some "Kind"
          value := #[{ name := some "VALUE", number := some 0 }]
        }]
      }
    ]
    service := #[
      {
        name := some "FirstApi"
        method := #[{
          name := some "Call"
          input_type := some ".positive.Request"
          output_type := some ".positive.Request"
        }]
      },
      {
        name := some "SecondApi"
        method := #[{
          name := some "Call"
          input_type := some ".positive.Request"
          output_type := some ".positive.Request"
        }]
      }
    ]
  }
  let otherPackageService : FileDescriptorProto := {
    name := some "other-package-service.proto"
    package := some "other"
    «syntax» := some "proto2"
    service := #[{ name := some "FirstApi" }]
  }
  let sharedPackagePrefix : FileDescriptorProto := {
    name := some "shared-package-prefix.proto"
    package := some "positive.sibling"
    «syntax» := some "proto2"
    message_type := #[{ name := some "Message" }]
  }
  match compileSetResult #[
    sharedMethodNamePositive,
    otherPackageService,
    sharedPackagePrefix
  ] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"symbols in distinct protobuf scopes were incorrectly rejected: {err}")

private def testDescriptorDependencyValidation : IO Unit := do
  let emptyFile (fileName : String)
      (dependencies : Array String := #[]) : FileDescriptorProto := {
    name := some fileName
    «syntax» := some "proto2"
    dependency := dependencies
  }
  expectErrorContains
    (compileSetResult #[emptyFile "duplicate.proto", emptyFile "duplicate.proto"])
    "file descriptor name `duplicate.proto` is declared more than once"
  expectErrorContains
    (compileSetResult #[emptyFile "missing-import.proto" #["absent.proto"]])
    "dependency `absent.proto` is absent from the descriptor set"
  expectErrorContains
    (compileSetResult #[
      emptyFile "duplicate-import.proto" #["dependency.proto", "dependency.proto"],
      emptyFile "dependency.proto"
    ])
    "dependency `dependency.proto` is listed more than once"
  expectErrorContains
    (compileSetResult #[emptyFile "self-import.proto" #["self-import.proto"]])
    "file recursively imports itself"
  expectErrorContains
    (compileSetResult #[
      emptyFile "cycle-a.proto" #["cycle-b.proto"],
      emptyFile "cycle-b.proto" #["cycle-a.proto"]
    ])
    "file import cycle contains"

  let optionFile
      (fileName : String) (optionDependencies : Array String) :
      FileDescriptorProto := {
    name := some fileName
    «syntax» := some "editions"
    edition := some .EDITION_2024
    option_dependency := optionDependencies
  }
  match compileSetResult #[
    optionFile "option-use.proto" #["option-definitions.proto"],
    emptyFile "option-definitions.proto"
  ] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError s!"valid Edition 2024 option import was rejected: {err}")
  expectErrorContains
    (compileSetResult #[
      optionFile "missing-option-import.proto" #["absent.proto"]
    ])
    "option dependency `absent.proto` is absent from the descriptor set"
  expectErrorContains
    (compileSetResult #[
      optionFile "duplicate-option-import.proto"
        #["option-definitions.proto", "option-definitions.proto"],
      emptyFile "option-definitions.proto"
    ])
    "listed more than once across dependency and option_dependency"
  expectErrorContains
    (compileSetResult #[
      {
        optionFile "cross-duplicate-option-import.proto"
          #["option-definitions.proto"] with
        dependency := #["option-definitions.proto"]
      },
      emptyFile "option-definitions.proto"
    ])
    "listed more than once across dependency and option_dependency"
  expectErrorContains
    (compileSetResult #[
      optionFile "self-option-import.proto" #["self-option-import.proto"]
    ])
    "file recursively imports itself"
  expectErrorContains
    (compileSetResult #[
      optionFile "option-cycle-a.proto" #["option-cycle-b.proto"],
      optionFile "option-cycle-b.proto" #["option-cycle-a.proto"]
    ])
    "file import cycle contains"
  expectErrorContains
    (compileSetResult #[
      {
        optionFile "mixed-cycle-a.proto" #["mixed-cycle-b.proto"] with
        option_dependency := #[]
        dependency := #["mixed-cycle-b.proto"]
      },
      optionFile "mixed-cycle-b.proto" #["mixed-cycle-a.proto"]
    ])
    "file import cycle contains"
  expectErrorContains
    (compileSetResult #[
      {
        optionFile "option-import-2023.proto" #["option-definitions.proto"] with
        edition := some .EDITION_2023
      },
      emptyFile "option-definitions.proto"
    ])
    "option imports are not supported before Edition 2024"
  expectErrorContains
    (compileSetResult #[
      {
        emptyFile "option-import-proto2.proto" with
        option_dependency := #["option-definitions.proto"]
      },
      emptyFile "option-definitions.proto"
    ])
    "option imports are not supported before Edition 2024"
  expectErrorContains
    (compileSetResult #[
      {
        optionFile "option-index.proto" #["option-definitions.proto"] with
        public_dependency := #[0]
      },
      emptyFile "option-definitions.proto"
    ])
    "invalid public dependency index 0"

  let optionTypes : FileDescriptorProto := {
    optionFile "option-types.proto" #[] with
    package := some "option_visibility"
    message_type := #[{ name := some "Target" }]
  }
  let optionTypeUse : FileDescriptorProto := {
    optionFile "option-type-use.proto" #["option-types.proto"] with
    message_type := #[{
      name := some "Use"
      field := #[{
        scalarField "target" 1 with
        type := some .TYPE_MESSAGE
        type_name := some ".option_visibility.Target"
      }]
    }]
  }
  expectErrorContains
    (compileSetResult #[optionTypes, optionTypeUse])
    "not imported by `option-type-use.proto`"

  let indexedDependency : FileDescriptorProto := {
    emptyFile "indexed.proto" #["dependency.proto"] with
    public_dependency := #[-1]
  }
  expectErrorContains
    (compileSetResult #[indexedDependency, emptyFile "dependency.proto"])
    "invalid public dependency index -1"
  expectErrorContains
    (compileSetResult #[
      { indexedDependency with public_dependency := #[1] },
      emptyFile "dependency.proto"
    ])
    "invalid public dependency index 1"
  expectErrorContains
    (compileSetResult #[
      {
        indexedDependency with
        public_dependency := #[]
        weak_dependency := #[1]
      },
      emptyFile "dependency.proto"
    ])
    "invalid weak dependency index 1"

  let repeatedIndices : FileDescriptorProto := {
    indexedDependency with
    public_dependency := #[0, 0]
    weak_dependency := #[0, 0]
  }
  match compileSetResult #[repeatedIndices, emptyFile "dependency.proto"] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"repeated public/weak dependency indices were rejected: {err}")
  let sharedIndex : FileDescriptorProto := {
    indexedDependency with
    public_dependency := #[0]
    weak_dependency := #[0]
  }
  match compileSetResult #[sharedIndex, emptyFile "dependency.proto"] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"one dependency marked both public and weak was rejected: {err}")
  let edition2024Weak : FileDescriptorProto := {
    indexedDependency with
    «syntax» := some "editions"
    edition := some .EDITION_2024
    public_dependency := #[]
    weak_dependency := #[0]
  }
  expectErrorContains
    (compileSetResult #[edition2024Weak, emptyFile "dependency.proto"])
    "weak imports are not supported in Edition 2024"
  let edition2023Weak : FileDescriptorProto := {
    edition2024Weak with
    edition := some .EDITION_2023
  }
  match compileSetResult #[edition2023Weak, emptyFile "dependency.proto"] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError s!"Edition 2023 weak import was rejected: {err}")

  let typesFile : FileDescriptorProto := {
    name := some "visibility-types.proto"
    package := some "visibility.types"
    «syntax» := some "proto2"
    enum_type := #[{
      name := some "E"
      value := #[{ name := some "ZERO", number := some 0 }]
    }]
    message_type := #[
      { name := some "Target" },
      {
        name := some "Host"
        extension_range := #[descriptorExtensionRange 100 200]
      }
    ]
  }
  let mapEntry :=
    syntheticMapEntry "TargetsEntry" (fields := #[
      syntheticMapKey,
      {
        syntheticMapValue with
        type := some .TYPE_MESSAGE
        type_name := some ".visibility.types.Target"
      }
    ])
  let visibilityUseFile (dependencies : Array String) : FileDescriptorProto := {
    name := some "visibility-use.proto"
    package := some "visibility.use"
    dependency := dependencies
    «syntax» := some "proto2"
    message_type := #[{
      name := some "Use"
      field := #[
        {
          scalarField "message_value" 1 with
          type := some .TYPE_MESSAGE
          type_name := some ".visibility.types.Target"
        },
        {
          scalarField "group_value" 2 with
          type := some .TYPE_GROUP
          type_name := some ".visibility.types.Target"
        },
        {
          scalarField "enum_value" 3 with
          type := some .TYPE_ENUM
          type_name := some ".visibility.types.E"
        },
        {
          syntheticMapOwner
            "targets" ".visibility.use.Use.TargetsEntry" with
          number := some 4
        }
      ]
      nested_type := #[mapEntry]
    }]
    extension := #[{
      descriptorExtensionField
        "typed_extension" 100 ".visibility.types.Host" with
      type := some .TYPE_MESSAGE
      type_name := some ".visibility.types.Target"
    }]
    service := #[{
      name := some "Api"
      method := #[{
        name := some "Call"
        input_type := some ".visibility.types.Target"
        output_type := some ".visibility.types.Target"
      }]
    }]
  }
  expectErrorContains
    (compileSetResult #[typesFile, visibilityUseFile #[]])
    "not imported by `visibility-use.proto`"
  let fieldOnlyUse
      (field : FieldDescriptorProto)
      (nested : Array DescriptorProto := #[]) : FileDescriptorProto := {
    visibilityUseFile #[] with
    message_type := #[{
      name := some "Use"
      field := #[field]
      nested_type := nested
    }]
    extension := #[]
    service := #[]
  }
  expectErrorContains
    (compileSetResult #[
      typesFile,
      fieldOnlyUse {
        scalarField "group_value" 1 with
        type := some .TYPE_GROUP
        type_name := some ".visibility.types.Target"
      }
    ])
    "visibility.use.Use.group_value: target is defined"
  expectErrorContains
    (compileSetResult #[
      typesFile,
      fieldOnlyUse {
        scalarField "enum_value" 1 with
        type := some .TYPE_ENUM
        type_name := some ".visibility.types.E"
      }
    ])
    "visibility.use.Use.enum_value: target is defined"
  expectErrorContains
    (compileSetResult #[
      typesFile,
      fieldOnlyUse
        (syntheticMapOwner
          "targets" ".visibility.use.Use.TargetsEntry")
        #[mapEntry]
    ])
    "visibility.use.Use.TargetsEntry.value: target is defined"
  let extensionTypeOnly : FileDescriptorProto := {
    visibilityUseFile #[] with
    message_type := #[{
      name := some "LocalHost"
      extension_range := #[descriptorExtensionRange 100 200]
    }]
    extension := #[{
      descriptorExtensionField
        "typed_extension" 100 ".visibility.use.LocalHost" with
      type := some .TYPE_MESSAGE
      type_name := some ".visibility.types.Target"
    }]
    service := #[]
  }
  expectErrorContains
    (compileSetResult #[typesFile, extensionTypeOnly])
    "visibility.use.typed_extension: target is defined"
  match compileSetResult #[
    typesFile,
    visibilityUseFile #["visibility-types.proto"]
  ] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"directly imported descriptor targets were rejected: {err}")

  let bridgeFile (isPublic : Bool) : FileDescriptorProto := {
    name := some "visibility-bridge.proto"
    package := some "visibility.bridge"
    dependency := #["visibility-types.proto"]
    public_dependency := if isPublic then #[0] else #[]
    «syntax» := some "proto2"
  }
  expectErrorContains
    (compileSetResult #[
      typesFile,
      bridgeFile false,
      visibilityUseFile #["visibility-bridge.proto"]
    ])
    "not imported by `visibility-use.proto`"
  match compileSetResult #[
    typesFile,
    bridgeFile true,
    visibilityUseFile #["visibility-bridge.proto"]
  ] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"public-transitive descriptor targets were rejected: {err}")

  let serviceOnly : FileDescriptorProto := {
    visibilityUseFile #[] with
    message_type := #[]
    extension := #[]
  }
  expectErrorContains (compileSetResult #[typesFile, serviceOnly])
    "visibility.use.Api.Call input_type: target is defined"

  let extensionOnly : FileDescriptorProto := {
    visibilityUseFile #[] with
    message_type := #[]
    service := #[]
    extension := #[
      descriptorExtensionField
        "unimported_extendee" 100 ".visibility.types.Host"
    ]
  }
  expectErrorContains (compileSetResult #[typesFile, extensionOnly])
    "extension extendee `.visibility.types.Host`: target is defined"

private def testDescriptorNormalization : IO Unit := do
  let file : FileDescriptorProto := {
    name := some "normalization.proto"
    package := some "normalization"
    «syntax» := some "proto2"
    enum_type := #[{
      name := some "E"
      value := #[{ name := some "ZERO", number := some 0 }]
    }]
    message_type := #[
      {
        name := some "Target"
        extension_range := #[descriptorExtensionRange 100 200]
      },
      {
        name := some "Use"
        field := #[
          {
            name := some "defaulted"
            number := some 1
          },
          {
            name := some "message_value"
            number := some 2
            type_name := some "Target"
          },
          {
            name := some "enum_value"
            number := some 3
            type_name := some "E"
          },
          {
            name := some "inner"
            number := some 4
            type_name := some "Inner"
          },
          {
            syntheticMapOwner "targets" "TargetsEntry" with
            number := some 5
          }
        ]
        nested_type := #[
          { name := some "Inner" },
          syntheticMapEntry "TargetsEntry" (fields := #[
            syntheticMapKey,
            {
              syntheticMapValue with
              type := none
              type_name := some "Target"
            }
          ])
        ]
      }
    ]
    extension := #[{
      descriptorExtensionField "kind_extension" 100 "Target" with
      type := none
      type_name := some "E"
    }]
    service := #[{
      name := some "Api"
      method := #[{
        name := some "Call"
        input_type := some "Target"
        output_type := some "Use.Inner"
      }]
    }]
  }
  match normalizeFileDescriptorSet { file := #[file] } |>.run with
  | .error err =>
      throw (IO.userError s!"valid optional descriptor fields were rejected: {err}")
  | .ok normalized =>
      let fields := normalized.file[0]!.message_type[1]!.field
      unless fields[0]!.label == some .LABEL_OPTIONAL &&
          fields[0]!.type == some .TYPE_DOUBLE do
        throw (IO.userError
          "absent FieldDescriptorProto label/type did not normalize to OPTIONAL/DOUBLE")
      unless fields[1]!.label == some .LABEL_OPTIONAL &&
          fields[1]!.type == some .TYPE_MESSAGE &&
          fields[1]!.type_name == some ".normalization.Target" do
        throw (IO.userError
          "message type was not inferred and canonicalized from type_name")
      unless fields[2]!.label == some .LABEL_OPTIONAL &&
          fields[2]!.type == some .TYPE_ENUM &&
          fields[2]!.type_name == some ".normalization.E" do
        throw (IO.userError
          "enum type was not inferred and canonicalized from type_name")
      unless fields[3]!.type == some .TYPE_MESSAGE &&
          fields[3]!.type_name == some ".normalization.Use.Inner" do
        throw (IO.userError
          "nested message type was not inferred and canonicalized")
      unless fields[4]!.type_name ==
          some ".normalization.Use.TargetsEntry" do
        throw (IO.userError
          "map owner type_name was not canonicalized")
      let mapValue :=
        normalized.file[0]!.message_type[1]!.nested_type[1]!.field[1]!
      unless mapValue.type == some .TYPE_MESSAGE &&
          mapValue.type_name == some ".normalization.Target" do
        throw (IO.userError
          "map value type was not inferred and canonicalized")
      let extension := normalized.file[0]!.extension[0]!
      unless extension.label == some .LABEL_OPTIONAL &&
          extension.type == some .TYPE_ENUM &&
          extension.type_name == some ".normalization.E" &&
          extension.extendee == some ".normalization.Target" do
        throw (IO.userError
          "typed extension was not inferred and canonicalized")
      let method := normalized.file[0]!.service[0]!.method[0]!
      unless method.input_type == some ".normalization.Target" &&
          method.output_type == some ".normalization.Use.Inner" do
        throw (IO.userError
          "service method input/output types were not canonicalized")
  match compileResult file with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"normalized optional descriptor fields failed code generation: {err}")

private def testCompoundRelativeNameShadowing : IO Unit := do
  /-
  Match DescriptorBuilder::LookupSymbolNoPlaceholder's canonical example:
  once `shadow.Foo.Bar` is found, `Bar.Baz` must be resolved inside it and
  must not fall back to the otherwise valid `shadow.Bar.Baz`.
  -/
  let messageFieldFile : FileDescriptorProto := {
    name := some "compound-shadow-message.proto"
    package := some "shadow"
    «syntax» := some "proto2"
    message_type := #[
      {
        name := some "Bar"
        nested_type := #[{ name := some "Baz" }]
      },
      {
        name := some "Foo"
        field := #[{
          scalarField "value" 1 with
          type := some .TYPE_MESSAGE
          type_name := some "Bar.Baz"
        }]
        nested_type := #[{ name := some "Bar" }]
      }
    ]
  }
  expectErrorContains (compileResult messageFieldFile)
    "field type_name `Bar.Baz` cannot be resolved"

  let enumFieldFile : FileDescriptorProto := {
    messageFieldFile with
    name := some "compound-shadow-enum.proto"
    message_type := #[
      {
        name := some "Palette"
        enum_type := #[{
          name := some "Kind"
          value := #[{ name := some "ZERO", number := some 0 }]
        }]
      },
      {
        name := some "Foo"
        field := #[{
          scalarField "kind" 1 with
          type := some .TYPE_ENUM
          type_name := some "Palette.Kind"
        }]
        nested_type := #[{ name := some "Palette" }]
      }
    ]
  }
  expectErrorContains (compileResult enumFieldFile)
    "field type_name `Palette.Kind` cannot be resolved"

  let serviceTypes : FileDescriptorProto := {
    name := some "compound-shadow-service-types.proto"
    package := some "service_shadow"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "Requests"
      nested_type := #[{ name := some "Input" }]
    }]
  }
  let serviceUse : FileDescriptorProto := {
    name := some "compound-shadow-service-use.proto"
    package := some "service_shadow.inner"
    dependency := #["compound-shadow-service-types.proto"]
    «syntax» := some "proto2"
    message_type := #[{ name := some "Requests" }]
    service := #[{
      name := some "Api"
      method := #[{
        name := some "Call"
        input_type := some "Requests.Input"
        output_type := some ".service_shadow.Requests.Input"
      }]
    }]
  }
  expectErrorContains (compileSetResult #[serviceTypes, serviceUse])
    "input_type: message type name `Requests.Input` cannot be resolved"

  let extensionFile : FileDescriptorProto := {
    name := some "compound-shadow-extension.proto"
    package := some "extension_shadow"
    «syntax» := some "proto2"
    message_type := #[
      {
        name := some "Host"
        nested_type := #[{
          name := some "Target"
          extension_range := #[descriptorExtensionRange 100 200]
        }]
      },
      {
        name := some "Foo"
        nested_type := #[{ name := some "Host" }]
        extension := #[
          descriptorExtensionField "value" 100 "Host.Target"
        ]
      }
    ]
  }
  expectErrorContains (compileResult extensionFile)
    "extension extendee `Host.Target` does not name a message"

private def testEditionSymbolVisibility : IO Unit := do
  let types2024 : FileDescriptorProto := {
    name := some "visibility-2024-types.proto"
    package := some "edition_visibility"
    «syntax» := some "editions"
    edition := some .EDITION_2024
    message_type := #[
      { name := some "Top" },
      {
        name := some "LocalTop"
        visibility := some .VISIBILITY_LOCAL
      },
      {
        name := some "Outer"
        nested_type := #[
          { name := some "Nested" },
          {
            name := some "ExportedNested"
            visibility := some .VISIBILITY_EXPORT
          }
        ]
      }
    ]
  }
  let useType (target : String) : FileDescriptorProto := {
    name := some "visibility-2024-use.proto"
    package := some "edition_visibility_use"
    dependency := #["visibility-2024-types.proto"]
    «syntax» := some "editions"
    edition := some .EDITION_2024
    message_type := #[{
      name := some "Use"
      field := #[{
        scalarField "value" 1 with
        type := some .TYPE_MESSAGE
        type_name := some target
      }]
    }]
  }
  match compileSetResult #[types2024, useType ".edition_visibility.Top"] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"Edition 2024 top-level default export was rejected: {err}")
  expectErrorContains
    (compileSetResult #[
      types2024,
      useType ".edition_visibility.Outer.Nested"
    ])
    "target is local to `visibility-2024-types.proto`"
  expectErrorContains
    (compileSetResult #[
      types2024,
      useType ".edition_visibility.LocalTop"
    ])
    "target is local to `visibility-2024-types.proto`"
  match compileSetResult #[
    types2024,
    useType ".edition_visibility.Outer.ExportedNested"
  ] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"explicitly exported Edition 2024 nested type was rejected: {err}")

  let types2023 : FileDescriptorProto := {
    types2024 with
    name := some "visibility-2023-types.proto"
    edition := some .EDITION_2023
    message_type := #[{
      name := some "Outer2023"
      nested_type := #[{ name := some "Nested" }]
    }]
  }
  let use2023 : FileDescriptorProto := {
    useType ".edition_visibility.Outer2023.Nested" with
    name := some "visibility-2023-use.proto"
    dependency := #["visibility-2023-types.proto"]
    edition := some .EDITION_2023
  }
  match compileSetResult #[types2023, use2023] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"pre-Edition-2024 nested default export was rejected: {err}")

  let strictTypes : FileDescriptorProto := {
    types2024 with
    name := some "visibility-strict.proto"
    options := some {
      features := some {
        default_symbol_visibility := some .STRICT
      }
    }
    message_type := #[{
      name := some "Outer"
      nested_type := #[{
        name := some "IllegallyExported"
        visibility := some .VISIBILITY_EXPORT
      }]
    }]
  }
  expectErrorContains (compileResult strictTypes)
    "nested symbols cannot be explicitly exported"

  let strictLocal : FileDescriptorProto := {
    strictTypes with
    name := some "visibility-strict-local.proto"
    message_type := #[{
      name := some "Outer"
      nested_type := #[{
        name := some "ExplicitlyLocal"
        visibility := some .VISIBILITY_LOCAL
      }]
    }]
  }
  expectCompileSucceeds strictLocal
    "STRICT permits an explicitly local nested symbol"

  let strictEnumNamespace : FileDescriptorProto := {
    strictTypes with
    name := some "visibility-strict-enum-namespace.proto"
    message_type := #[{
      name := some "Namespace"
      reserved_range := #[{
        start := some 1
        «end» := some 536870912
      }]
      enum_type := #[{
        name := some "Kind"
        visibility := some .VISIBILITY_EXPORT
        value := #[{ name := some "ZERO", number := some 0 }]
      }]
    }]
  }
  let strictEnumUse : FileDescriptorProto := {
    useType ".edition_visibility.Namespace.Kind" with
    name := some "visibility-strict-enum-use.proto"
    dependency := #["visibility-strict-enum-namespace.proto"]
    message_type := #[{
      name := some "Use"
      field := #[{
        scalarField "kind" 1 with
        type := some .TYPE_ENUM
        type_name := some ".edition_visibility.Namespace.Kind"
      }]
    }]
  }
  match compileSetResult #[strictEnumNamespace, strictEnumUse] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"STRICT enum-namespace wrapper carve-out was rejected: {err}")

  let illegalStrictNestedEnum : FileDescriptorProto := {
    strictTypes with
    name := some "visibility-strict-nested-enum.proto"
    message_type := #[{
      name := some "Outer"
      enum_type := #[{
        name := some "Kind"
        visibility := some .VISIBILITY_EXPORT
        value := #[{ name := some "ZERO", number := some 0 }]
      }]
    }]
  }
  expectErrorContains (compileResult illegalStrictNestedEnum)
    "nested symbols cannot be explicitly exported"

  let defaultVisibility2023 : FileDescriptorProto := {
    types2023 with
    name := some "visibility-feature-2023.proto"
    options := some {
      features := some {
        default_symbol_visibility := some .EXPORT_ALL
      }
    }
  }
  expectErrorContains (compileResult defaultVisibility2023)
    "default_symbol_visibility is not supported before Edition 2024"

  let explicitMessageVisibility2023 : FileDescriptorProto := {
    types2023 with
    name := some "explicit-message-visibility-2023.proto"
    message_type := #[{
      name := some "M"
      visibility := some .VISIBILITY_LOCAL
    }]
  }
  expectErrorContains (compileResult explicitMessageVisibility2023)
    "explicit symbol visibility on message"

  let explicitEnumVisibility2023 : FileDescriptorProto := {
    types2023 with
    name := some "explicit-enum-visibility-2023.proto"
    message_type := #[]
    enum_type := #[{
      name := some "E"
      visibility := some .VISIBILITY_EXPORT
      value := #[{ name := some "ZERO", number := some 0 }]
    }]
  }
  expectErrorContains (compileResult explicitEnumVisibility2023)
    "explicit symbol visibility on enum"

private def testWholeSetTypeTargetValidation : IO Unit := do
  let typesFile : FileDescriptorProto := {
    name := some "types.proto"
    package := some "shared"
    «syntax» := some "proto2"
    enum_type := #[{
      name := some "E"
      value := #[
        { name := some "ZERO", number := some 0 },
        { name := some "ONE", number := some 1 }
      ]
    }]
    message_type := #[
      {
        name := some "Outer"
        nested_type := #[
          { name := some "Inner" },
          {
            name := some "User"
            field := #[{
              scalarField "inner" 1 with
              type := some .TYPE_MESSAGE
              type_name := some "Inner"
            }]
          }
        ]
      },
      {
        name := some "Host"
        extension_range := #[descriptorExtensionRange 100 200]
      }
    ]
  }
  let enumMapEntry :=
    syntheticMapEntry "ByEnumEntry" (fields := #[
      { syntheticMapKey with type := some .TYPE_STRING },
      {
        syntheticMapValue with
        type := some .TYPE_ENUM
        type_name := some "E"
      }
    ])
  let useFile : FileDescriptorProto := {
    name := some "use.proto"
    package := some "shared"
    dependency := #["types.proto"]
    «syntax» := some "proto2"
    message_type := #[{
      name := some "Use"
      field := #[
        {
          scalarField "e" 1 with
          type := some .TYPE_ENUM
          type_name := some "E"
          default_value := some "ONE"
        },
        {
          scalarField "inner" 2 with
          type := some .TYPE_MESSAGE
          type_name := some ".shared.Outer.Inner"
        },
        {
          syntheticMapOwner "by_enum" ".shared.Use.ByEnumEntry" with
          number := some 3
        }
      ]
      nested_type := #[enumMapEntry]
    }]
    extension := #[{
      descriptorExtensionField "enum_extension" 100 ".shared.Host" with
      type := some .TYPE_ENUM
      type_name := some "E"
      default_value := some "ONE"
    }]
    service := #[{
      name := some "Api"
      method := #[{
        name := some "Call"
        input_type := some "Outer.Inner"
        output_type := some ".shared.Outer"
      }]
    }]
  }
  match compileSetResult #[typesFile, useFile] with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError
        s!"valid relative/absolute cross-file type references were rejected: {err}")

  let expectBadField
      (field : FieldDescriptorProto) (needle : String) : IO Unit := do
    let file : FileDescriptorProto := {
      name := some "bad-field-type.proto"
      package := some "shared"
      «syntax» := some "proto2"
      enum_type := typesFile.enum_type
      message_type := #[
        typesFile.message_type[0]!,
        {
          name := some "Use"
          field := #[field]
        }
      ]
    }
    expectErrorContains (compileResult file) needle

  expectBadField {
    scalarField "missing" 1 with
    type := some .TYPE_MESSAGE
    type_name := some ".shared.DoesNotExist"
  } "cannot be resolved in the descriptor set"
  expectBadField {
    scalarField "wrong_message" 1 with
    type := some .TYPE_MESSAGE
    type_name := some "E"
  } "message field type_name `.shared.E` names enum `shared.E`"
  expectBadField {
    scalarField "wrong_enum" 1 with
    type := some .TYPE_ENUM
    type_name := some "Outer"
  } "enum field type_name `.shared.Outer` names message `shared.Outer`"
  expectBadField {
    scalarField "missing_name" 1 with
    type := some .TYPE_MESSAGE
    type_name := none
  } "field type requires type_name"
  expectBadField {
    scalarField "scalar_name" 1 with
    type_name := some ".shared.Outer"
  } "scalar field cannot set type_name"
  expectBadField {
    scalarField "bad_default" 1 with
    type := some .TYPE_ENUM
    type_name := some ".shared.E"
    default_value := some "MISSING"
  } "enum default `MISSING` is not a value of `shared.E`"

  let badMapValue :=
    syntheticMapEntry (fields := #[
      syntheticMapKey,
      {
        syntheticMapValue with
        type := some .TYPE_MESSAGE
        type_name := some ".shared.DoesNotExist"
      }
    ])
  expectErrorContains
    (compileResult (syntheticMapFile "proto2" badMapValue))
    "cannot be resolved in the descriptor set"

  let badExtension : FileDescriptorProto := {
    useFile with
    message_type := #[]
    service := #[]
    extension := #[{
      descriptorExtensionField "bad_extension" 100 ".shared.Host" with
      type := some .TYPE_ENUM
      type_name := some ".shared.Outer"
    }]
  }
  expectErrorContains (compileSetResult #[typesFile, badExtension])
    "enum field type_name `.shared.Outer` names message `shared.Outer`"

  let serviceFile : FileDescriptorProto := {
    name := some "bad-service.proto"
    package := some "shared"
    dependency := #["types.proto"]
    «syntax» := some "proto2"
    service := #[{
      name := some "Api"
      method := #[{
        name := some "Call"
        input_type := some ".shared.E"
        output_type := some ".shared.DoesNotExist"
      }]
    }]
  }
  expectErrorContains (compileSetResult #[typesFile, serviceFile])
    "input_type: message type name `.shared.E` names enum `shared.E`"
  let badOutput : FileDescriptorProto := {
    serviceFile with
    service := #[{
      name := some "Api"
      method := #[{
        name := some "Call"
        input_type := some ".shared.Outer"
        output_type := some ".shared.E"
      }]
    }]
  }
  expectErrorContains (compileSetResult #[typesFile, badOutput])
    "output_type: message type name `.shared.E` names enum `shared.E`"
  let missingInput : FileDescriptorProto := {
    serviceFile with
    service := #[{
      name := some "Api"
      method := #[{
        name := some "Call"
        output_type := some ".shared.Outer"
      }]
    }]
  }
  expectErrorContains (compileSetResult #[typesFile, missingInput])
    "method input_type is absent"
  let missingOutput : FileDescriptorProto := {
    serviceFile with
    service := #[{
      name := some "Api"
      method := #[{
        name := some "Call"
        input_type := some ".shared.Outer"
      }]
    }]
  }
  expectErrorContains (compileSetResult #[typesFile, missingOutput])
    "method output_type is absent"

private def testRawIdentifierValidation : IO Unit := do
  let base : FileDescriptorProto := {
    name := some "identifiers.proto"
    package := some "valid.package"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "Message"
      field := #[scalarField "field" 1]
    }]
    enum_type := #[{
      name := some "Enum"
      value := #[{ name := some "VALUE", number := some 0 }]
    }]
    service := #[{
      name := some "Service"
      method := #[{
        name := some "Call"
        input_type := some ".valid.package.Message"
        output_type := some ".valid.package.Message"
      }]
    }]
  }
  let expectBad (file : FileDescriptorProto) : IO Unit :=
    expectErrorContains (compileResult file) "bad»"

  expectBad { base with package := some "valid.bad»" }
  expectBad {
    base with
    message_type := #[{ base.message_type[0]! with name := some "bad»" }]
  }
  expectBad {
    base with
    enum_type := #[{ base.enum_type[0]! with name := some "bad»" }]
  }
  expectBad {
    base with
    enum_type := #[{
      base.enum_type[0]! with
      value := #[{ name := some "bad»", number := some 0 }]
    }]
  }
  expectBad {
    base with
    message_type := #[{
      base.message_type[0]! with
      field := #[scalarField "bad»" 1]
    }]
  }
  expectBad {
    base with
    message_type := #[{
      base.message_type[0]! with
      oneof_decl := #[{ name := some "bad»" }]
    }]
  }
  expectBad {
    base with
    message_type := #[{
      base.message_type[0]! with
      field := #[{
        scalarField "field" 1 with
        type_name := some ".valid.bad»"
      }]
    }]
  }
  expectBad {
    base with
    message_type := #[{
      base.message_type[0]! with
      field := #[{
        scalarField "field" 1 with
        type := some .TYPE_ENUM
        type_name := some ".valid.package.Enum"
        default_value := some "bad»"
      }]
    }]
  }
  expectBad {
    base with
    extension := #[{
      scalarField "extension" 100 with
      extendee := some ".valid.bad»"
    }]
  }
  expectBad {
    base with
    service := #[{ base.service[0]! with name := some "bad»" }]
  }
  expectBad {
    base with
    service := #[{
      base.service[0]! with
      method := #[{ base.service[0]!.method[0]! with name := some "bad»" }]
    }]
  }
  expectBad {
    base with
    service := #[{
      base.service[0]! with
      method := #[{
        base.service[0]!.method[0]! with
        input_type := some ".valid.bad»"
      }]
    }]
  }
  expectBad {
    base with
    service := #[{
      base.service[0]! with
      method := #[{
        base.service[0]!.method[0]! with
        output_type := some "valid.bad»"
      }]
    }]
  }

  -- `_root_` is an ordinary protobuf identifier even though Lean also uses it
  -- as a root-namespace qualifier.
  let rootPackage : FileDescriptorProto := {
    name := some "root-package.proto"
    package := some "_root_"
    «syntax» := some "proto2"
    message_type := #[{ name := some "_root_" }]
  }
  match compileResult rootPackage with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError s!"valid `_root_` identifiers were rejected: {err}")

  let validEnumDefault : FileDescriptorProto := {
    base with
    message_type := #[{
      base.message_type[0]! with
      field := #[{
        scalarField "field" 1 with
        type := some .TYPE_ENUM
        type_name := some ".valid.package.Enum"
        default_value := some "VALUE"
      }]
    }]
  }
  match compileResult validEnumDefault with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError s!"valid enum default identifier was rejected: {err}")

  -- These descriptor strings are not protobuf identifiers.
  let nonIdentifiers : FileDescriptorProto := {
    name := some "odd»path.proto"
    «syntax» := some "proto2"
    message_type := #[{
      name := some "M"
      field := #[{
        scalarField "value" 1 with
        json_name := some "bad» json-name"
      }]
      reserved_name := #["bad-name", "bad»"]
    }]
  }
  match compileResult nonIdentifiers with
  | .ok _ => pure ()
  | .error err =>
      throw (IO.userError s!"non-identifier descriptor text was rejected: {err}")

private def ofProtoExcept (result : Except ProtoError α) : IO α := do
  match result with
  | .ok value => pure value
  | .error err => throw (IO.userError err.toString)

private def testCurrentDescriptorFields : IO Unit := do
  unless Edition.EDITION_2026.toInt32 == (1002 : Int32) do
    throw (IO.userError "EDITION_2026 descriptor value changed")
  let features : FeatureSet := {
    enforce_naming_style := some .STYLE2026
    default_symbol_visibility := some .STRICT
    enforce_proto_limits := some .PROTO_LIMITS2026
  }
  let features' ← ofProtoExcept (FeatureSet.fromMessage (← ofProtoExcept features.toMessage))
  unless features'.enforce_naming_style == features.enforce_naming_style do
    throw (IO.userError "FeatureSet.enforce_naming_style did not roundtrip")
  unless features'.default_symbol_visibility == features.default_symbol_visibility do
    throw (IO.userError "FeatureSet.default_symbol_visibility did not roundtrip")
  unless features'.enforce_proto_limits == features.enforce_proto_limits do
    throw (IO.userError "FeatureSet.enforce_proto_limits did not roundtrip")

  let file : FileDescriptorProto := {
    name := some "visibility.proto"
    option_dependency := #["custom/options.proto"]
    message_type := #[{
      name := some "LocalMessage"
      visibility := some .VISIBILITY_LOCAL
    }]
    enum_type := #[{
      name := some "ExportedEnum"
      visibility := some .VISIBILITY_EXPORT
    }]
  }
  let file' ← ofProtoExcept (FileDescriptorProto.fromMessage (← ofProtoExcept file.toMessage))
  unless file'.option_dependency == file.option_dependency do
    throw (IO.userError "FileDescriptorProto.option_dependency did not roundtrip")
  unless file'.message_type[0]!.visibility == some .VISIBILITY_LOCAL do
    throw (IO.userError "DescriptorProto.visibility did not roundtrip")
  unless file'.enum_type[0]!.visibility == some .VISIBILITY_EXPORT do
    throw (IO.userError "EnumDescriptorProto.visibility did not roundtrip")

public def main : IO Unit := do
  testProto2PackedValidation
  testProto3RequiredValidation
  testProto3OptionalValidation
  testOneofDescriptorValidation
  testStaticFieldNumberValidation
  testProto3FirstEnumValueValidation
  testEnumAliasAndReservedValidation
  testDefaultTargetValidation
  testIntegerDefaultRangeValidation
  testDescriptorDefaultLexicalValidation
  testReservedRangeLowerBound
  testReservedNameSurvivesSanitizing
  testReservedSetValidation
  testEditionsOpenEnumFirstZeroValidation
  testEditionsLegacyPackedValidation
  testEditionsImplicitDefaultValidation
  testEditionsExtensionPresence
  testGroupDescriptorValidation
  testEditionsMessageEncodingValidation
  testBuiltinFeatureTargetValidation
  testEditionsClosedEnumSupport
  testSyntheticMapEntryValidation
  testDescriptorSetExtensionValidation
  testWholeSetSymbolUniqueness
  testDescriptorDependencyValidation
  testDescriptorNormalization
  testCompoundRelativeNameShadowing
  testEditionSymbolVisibility
  testWholeSetTypeTargetValidation
  testRawIdentifierValidation
  testCurrentDescriptorFields
