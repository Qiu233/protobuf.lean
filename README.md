# protobuf
`protobuf` is an implementation of Google's Protocol Buffers in Lean 4, supporting `proto2`, `proto3`, and `edition`.

The goal of this package is to be the standard choice among all Lean 4 protobuf implementations. So far (1/7/2026), this packages has been fully featured in terms of **all core protobuf features** a user would expect.

# Missing features

Work in progress:

1. Reflection API: e.g. function `descriptor : MsgType -> Descriptor`. The option `no_standard_descriptor_accessor` is currently ignored.
2. Json mapping: designing, likely to be an add-on after we have reflection API.
3. Service/RPC: we will need to think through frameworking issues first. Currently services are ignored.
4. proto2 `default` option of fields.

Less likely to have (some of them may never be supported):

* Proto1 behaviors: e.g. option `message_set_wire_format` is forbidden.
* EGROUP/SGROUP: the delimited serialization of message is not allowed, though we are able to deserialize them from wire format. The `edition` `features` enabling this are forbidden.
* proto2 group fields: things like `repeated group Result = 1 { fields... }` are not allowed. Use nested message instead.

# Usage

There are 5 methods to use this library:

1. Load a standalone .proto file.
2. Load a folder containing .proto files.
3. As a protoc plugin.
4. Use the internal notation.
5. Use the encoding/decoding utilities directly.

**The first 3 methods require the `protoc` command.
The last tested `protoc` version is `libprotoc 30.2`.**

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

## A folder of protobuf files

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
