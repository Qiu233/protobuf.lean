module

import Protobuf

open scoped Protobuf.Notation

#load_proto_file "Test/VisibilityExportAllUse.proto" in "."

#check visibility_export_all.Outer.Nested
#check visibility_export_all_use.Use
