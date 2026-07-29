# protobuf
`protobuf` is an implementation of Google's Protocol Buffers in Lean 4, supporting `proto2`, `proto3`, and `edition`.

The goal of this package is to be the standard choice among all Lean 4 protobuf implementations. So far (1/7/2026), this packages has been fully featured in terms of **all core protobuf features** a user would expect.

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

#eval test.a.Q.encode { q := test.a.Q.q_Type.a { t := some 1 } }
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

#eval A.encode { a := #[1, 2, 3] }
```

With this you can define messages in a very convenient and compact way, and it does not require the `protoc` command to be present.

## Using encoding/decoding API
Please read the source code under the folder `Encoding` to learn their usage.

This usage is highly unrecommended and should only serve for debugging purposes.

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
exposed or interpreted after static code generation; doing so would require
reflection support or an explicitly defined Lean code-generation meaning.

# Missing features

Work in progress:

1. Reflection API: e.g. function `descriptor : MsgType -> Descriptor`. The option `no_standard_descriptor_accessor` is currently ignored.
2. Json mapping: designing, likely to be an add-on after we have reflection API.
3. Service/RPC: we will need to think through frameworking issues first. Currently services are ignored.

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
