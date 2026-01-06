# protobuf
`protobuf` is an implementation of google's protobuf in Lean 4, supporting `proto2`, `proto3`, and `edition`.

# Missing features

❌Won't support:

* Proto1 behaviors: e.g. option `message_set_wire_format` is forbidden.
* EGROUP/SGROUP: the delimited encoding of message is not allowed, though we are able to parse them from wire format. The `edition` `features` enabling this are forbidden.
* proto2 group fields: things like `repeated group Result = 1 { fields... }` are not allowed. Use nested message instead.


Work in progress:

1. Reflection API: e.g. function `descriptor : MsgType -> Descriptor`. The option `no_standard_descriptor_accessor` is currently ignored.
2. Json mapping: designing, likely to be an add-on after we have reflection API.
3. Service/RPC: we will need to think through frameworking issues first. Currently services are ignored.

# Usage

There are 5 ways to use this library, and the first 4 can be mixed:

1. Load a standalone .proto file.
2. Load a folder containing .proto files.
3. Use the internal notation.
4. Use the encoding/decoding utilities directly.
5. As a protoc plugin.

**To use in the first 2 ways, you must first install the `protoc` command.
The last tested `protoc` version is `libprotoc 30.2`.**

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

## Internal notation

**NOTE: the internal notation is protobuf-version-neutral, that is, you have to control very specific behavior of the encoding.**

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

## As a protoc plugin

This usage is highly unrecommended, due to:
* Currently (v4.26.0) Lean 4 compiler does not prune the `meta` imports, causing executables to be exceedingly **huge (180 MiB)**.
* When compiling multiple files, there is no clear way to generate correct `import XXX` statements, since it simultaneously depends on the in/out directory you specify in the `protoc` command (see `-I` and `--lean4_out` below). So we choose to **not generate them** and leave to users to complete after putting the generated .lean files to the location they want.

First prepare a folder to put the plugin, say `<folder>`.

```bash
clone https://github.com/Lean-zh/protobuf.git
cd protobuf
lake build Plugin
cp ./.lake/build/bin/protoc-gen-lean4 <folder>
protoc --plugin=protoc-gen-lean4=<folder>/protoc-gen-lean4 --lean4_out=<output_folder> -I=<input_folder> ...
```
