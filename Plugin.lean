module

public import Protobuf

open Protobuf Encoding Notation Internal

set_option protobuf.trace.descriptor true
set_option protobuf.trace.notation true

public section

#load_proto_file "proto/google/protobuf/descriptor.proto"
#load_proto_file "proto/google/protobuf/compiler/plugin.proto"

def main : IO Unit := pure ()
