# protobuf
`protobuf` is an implementation of Google's Protocol Buffers written in Lean 4.

## Production readiness

Legend: `[x]` is supported; `[x] ◩` is supported with the stated compatibility
boundary. Markdown has no portable indeterminate checkbox, so `◩` is used as
the half-checked marker.

- [x] **Official language frontends** — `proto2`, `proto3`, Editions 2023, and
  Editions 2024, using descriptors produced by `protoc`.
- [x] **Static code generation** — standalone files, import trees, whole
  directories, and a `protoc-gen-lean4` plugin all produce ordinary Lean
  types with a typed binary API.
- [x] **Binary protobuf semantics** — every scalar wire type, unknown fields,
  presence, required fields, explicit defaults, packed and expanded fields,
  maps, oneofs, recursive messages, and the standard recursion and size
  limits.
- [x] **Proto2 and Editions features** — open and closed enums, enum aliases,
  extensions, groups, Editions `DELIMITED` messages, UTF-8 validation,
  feature inheritance, and Editions symbol visibility.
- [x] **Rich runtime and reflection** — immutable descriptors, generated and
  isolated descriptor pools, pool overlays, extension descriptors,
  `DynamicMessage`, and static/dynamic conversion that preserves unknown wire
  records.
- [x] **ProtoJSON** — generated and dynamic messages, field-name aliases,
  extensions, `Any`, wrappers, `Timestamp`, `Duration`, `FieldMask`, `Struct`,
  `Value`, and `ListValue`; the upstream Proto3 JSON conformance suite runs in
  CI.
- [x] **Schema validation and preservation** — invalid descriptor combinations
  are rejected before generation, while unknown wire fields and retained
  descriptor options survive processing.
- [x] **Regression coverage** — the test suite exercises generated code,
  plugin output by recompiling it, reflection, malformed inputs, recursion
  limits, JSON edge cases, and the upstream conformance runner.
- [x] ◩ **Services** — service and method descriptors are fully reflected;
  RPC-framework-specific client/server stubs are deliberately not generated.
- [x] ◩ **Custom options** — runtime- and default-retained option data is
  preserved; source-retained data remains in `source_file_descriptors`.
  Applications interpret option extensions with an explicit resolver.
- [x] ◩ **Extension lookup** — generated and isolated-pool resolvers are
  supported; there is intentionally no automatic process-wide registry of
  extension language types.
- [ ] **Legacy MessageSet and Proto1** — the MessageSet wire format is rejected,
  and a Proto1 language frontend is not planned.

# Usage

There are 5 methods to use this library:

1. Load a standalone .proto file.
2. Load a folder containing .proto files.
3. As a protoc plugin.
4. Use the internal notation.
5. Use the encoding/decoding utilities directly.

**The first 3 methods require the `protoc` command.
The last tested version is `libprotoc 35.0`; Edition 2024 inputs require
`protoc` 32.0 or newer.**

The `#load_proto_*` commands and repository test scripts honor `PROTOC`, so a
specific compiler can be selected without changing the process-wide `PATH`:

```bash
PROTOC=/path/to/protoc lake build
```

Downstream users of this package can expect the first 3 methods to be always reliable and production ready. The first two methods are highly recommended for production use.

## Standalone .proto file

Say you have a file `proto/A.proto` relative to **package root**:

```protobuf
syntax = "proto3";

package test.a;

message A {
    optional int32 t = 1;
}

message Q {
    oneof q {
        A a = 1;
        Q b = 2;
    }
    map<int32, int32> s = 4;
}
```

In any Lean source file:

```lean
import Protobuf

open Protobuf Encoding Notation

#load_proto_file "proto/A.proto"

#check test.a.A.t

instance : Repr ByteArray where
  reprPrec x p := s!"{reprPrec x.data p}"

#eval Protobuf.encode {
  q := test.a.Q.q_Type.a { t := some 1 }
  : test.a.Q
}
```

## A folder of .proto files

```lean
import Protobuf

open Protobuf Encoding Notation

#load_proto_dir "folder"
...
```

## As a protoc plugin

**Warning: Currently (v4.26.0) Lean 4 compiler does not prune the `meta` imports, causing executables to be exceedingly huge (180 MiB).**

First prepare a folder to contain the plugin, say `<plugin_folder>`.

```bash
clone https://github.com/Lean-zh/protobuf.git
cd protobuf
lake build Plugin
cp ./.lake/build/bin/protoc-gen-lean4 <plugin_folder>
```

Then create a Lean 4 project, with name `Foo`.

```bash
cd <root_of_Foo>
mkdir Foo/Proto
protoc --plugin=protoc-gen-lean4=<plugin_folder>/protoc-gen-lean4 --lean4_out=./Foo/Proto --lean4_opt=lean4_prefix=Foo.Proto -I <proto_files_search_path> <proto_file>
```

## Internal notation

**NOTE: the internal notation is protobuf-version-neutral, that is, you have to specify very specific behaviors of the encoding.**

One example is, in any lean source file:

```lean
import Protobuf

open Protobuf Encoding Notation

message A {
  repeated int32 a = 1 [packed = true];
}

#eval Protobuf.encode { a := #[1, 2, 3] : A }
```

With this you can define messages in a very convenient and compact way, and it does not require the `protoc` command to be present.

## Binary encoding and decoding

Every generated message implements `Protobuf.ProtoMessage`. Its methods are
exported from the `Protobuf` namespace:

```lean
def roundTrip (value : A) : Except Encoding.ProtoError A := do
  let bytes ← Protobuf.encode value
  Protobuf.decode bytes

def parseA (bytes : ByteArray) : Except Encoding.ProtoError A :=
  Protobuf.decodeThe A bytes
```

`decodeThe` is an always-inlined positional wrapper around `decode`; it is
useful when the result type cannot be inferred from context.

### Migration from generated helper names

Earlier versions generated binary and wire helpers directly below every
message, enum, and oneof namespace. Those compatibility names have been
removed completely:

- Replace `Message.encode value` with `Protobuf.encode value`.
- Replace `Message.decode bytes` with `Protobuf.decodeThe Message bytes`, or
  use `Protobuf.decode bytes` when Lean can infer the result type.
- Explicit-default accessors now live only at
  `Message.«Explicit.Default.Accessors».field.get` and `.has`.
- The former message, enum, and oneof helper spellings are ordinary schema
  names again; fields, enum values, alternatives, and nested types may use
  names such as `encode`, `toMessage`, `toInt32`, or `merge`.

There are intentionally no deprecated aliases or collision-dependent
fallbacks. Names below `«protobuf.internal»` are generator implementation
details and are not a public migration target.

## Using encoding/decoding API
Please read the source code under the folder `Encoding` to learn their usage.

This usage is highly unrecommended and should only serve for debugging purposes.

## ProtoJSON

`Protobuf.Json` implements the protobuf JSON mapping for generated messages and
reflection-based `DynamicMessage` values:

```lean
open Protobuf.Json

def roundTrip (value : test.proto3.All) : IO test.proto3.All := do
  let text ← IO.ofExcept (←
    toJsonString value PrintOptions.withGeneratedPool)
  IO.ofExcept (←
    fromJsonString text test.proto3.All ParseOptions.withGeneratedPool)
```

The generated-pool options enable bracketed extension fields and resolve
`google.protobuf.Any` payloads through runtime descriptors. Callers using
isolated descriptor pools can instead supply their own `ExtensionResolver` and
`TypeResolver`.

The implementation covers protobuf field-name aliases, presence and required
fields, maps, oneofs, open and closed enums, exact integer ranges, special
floating-point values, base64 variants, recursion limits, and the standard
well-known JSON forms for wrappers, `Timestamp`, `Duration`, `FieldMask`,
`Struct`, `Value`, `ListValue`, and `Any`. The upstream protobuf Proto3
Binary/JSON conformance suite is run in CI against the reflection-only adapter.

## Runtime descriptors and reflection

Files produced by `#load_proto_file`, `#load_proto_dir`, or the protoc plugin
register a compact serialized `FileDescriptorProto` at module initialization.
The process-wide generated pool also contains
`google/protobuf/descriptor.proto`:

```lean
open Protobuf.Reflection

def allDescriptor : MessageDescriptor :=
  messageDescriptor test.proto3.All

#eval do
  let some file ← generatedPool.findFileByName "Proto3.proto"
    | throw (IO.userError "descriptor is not registered")
  IO.println file.name
```

Descriptor identity includes its pool. Independent pools may contain
same-named schemas without making their descriptors equal. A dynamic pool may
also use another pool as an underlay:

```lean
let local ← DescriptorPool.new
let overlay ← DescriptorPool.newWithUnderlay generatedPool
```

Registered files and their descriptor graphs are immutable. Pools can grow,
including when a shared library is loaded later, so global enumeration order
is not an initialization contract; `DescriptorPool.files` returns the local
files sorted by name.

`DynamicMessage` provides schema-aware field access and mutation while
preserving unknown wire records. `presentValues` reports physical presence
rather than manufacturing protobuf defaults. Singular message occurrences
merge, repeated scalar fields accept packed and expanded wire forms, and
unknown values of a closed enum remain unknown data. Oneof selection follows
wire order, and Editions `DELIMITED` message fields are reflected as group wire
data without changing their descriptor's declared `TYPE_MESSAGE`. Generated
static messages can be converted with `DynamicMessage.ofStatic` and
`toStatic`; conversion to a dynamic message does not reject an incomplete
required field, while conversion back through the generated decoder does.

Extensions are resolved explicitly:

```lean
let resolver := generatedExtensionResolver
let some extension ←
    resolver.findExtensionByNumber allDescriptor 100
  | throw (IO.userError "extension is not registered")
```

There is deliberately no automatic process-wide registry of extension
language types. Callers choose the generated pool's resolver or provide a
local one.

Reflection-only applications which do not use generated Lean message types
can avoid generating those definitions:

```lean
#load_proto_descriptors "proto/A.proto"
```

This command performs the same whole-descriptor-set validation and registers
the same runtime metadata as `#load_proto_file`, but emits no static message,
enum, or accessor definitions. It is useful for dynamic gateways and
conformance tools, and avoids compiling specializations for otherwise unused
generated types.

## Group wire encoding

Legacy proto2 group fields are supported, including optional, required,
repeated, and extension fields:

```protobuf
repeated group Result = 1 { fields... }
```

Editions message fields using
`features.message_encoding = DELIMITED` are supported as the modern spelling
of the same START_GROUP/END_GROUP wire representation. Proto3 group
declarations remain invalid, as required by the language specification.

Generated static extension accessors honor explicit defaults, proto2 `packed`
encoding, the corresponding Editions repeated-field encoding feature, Editions
UTF-8 validation and message encoding, and the built-in `deprecated` option.
Target-language-specific options, optimization hints, option-definition
metadata, and debug/reflection options are not given Lean-specific behavior.

Arbitrary custom field options are not categorically filtered out by `protoc`.
Runtime- or default-retained values can reach the generator in `proto_file`
descriptor unknown fields and are preserved while descriptors are processed.
Source-retained values are supplied only through `source_file_descriptors` and
are not merged into the static generation input. Custom option values are not
given an automatic Lean-specific interpretation. Reflection exposes the
retained descriptor/options messages and their unknown wire fields, so
applications which know an option extension can interpret it with an explicit
resolver.

# Missing features

Service and method descriptors are reflected, but no RPC framework-specific
stubs are generated.

## Less likely to have
Some of them may never be supported:

### Legacy MessageSet compatibility

The legacy MessageSet wire format selected by
`google.protobuf.MessageOptions.message_set_wire_format` is not implemented.
It is a compatibility feature for an old Proto1 wire representation, not a
Proto1 language frontend. Although `protoc` 35 accepts the option in proto2 and
Editions inputs, this package currently rejects those inputs; proto3 rejects
the option as required by its language rules. A separate Proto1 frontend is
outside the scope of this item and is not planned.
