module

import Protobuf

open Protobuf
open scoped Protobuf.Notation

#load_proto_file "Test/RootName.proto"

#check «_root_.protobuf».X
#check «_root_.protobuf».Y
#check «_root_.protobuf».«_root_.protobuf»
#check «_root_.protobuf».RootHolder

#eval! (do
  let expected : «_root_.protobuf».Y := {
    x := some { a := 7 }
    mapped := ({} : Std.HashMap String «_root_.protobuf».X).insert
      "key" { a := 9 }
  }
  let bytes ← IO.ofExcept (Protobuf.encode expected)
  let actual ← IO.ofExcept
    (Protobuf.decodeThe «_root_.protobuf».Y bytes)
  unless actual.x.map (·.a) == some 7 &&
      actual.mapped["key"]?.map (·.a) == some 9 do
    throw (IO.userError "sanitized _root_ package roundtrip failed")
  let nestedName : «_root_.protobuf».RootHolder := {
    value := some { value := 11 }
  }
  unless nestedName.value.map (·.value) == some 11 do
    throw (IO.userError "sanitized _root_ type name changed")
  : IO Unit)
