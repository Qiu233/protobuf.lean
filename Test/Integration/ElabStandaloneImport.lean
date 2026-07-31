import Protobuf

open Protobuf Encoding Notation

#load_proto_file "Test/Fixtures/Plugin/app/main.proto" in "Test/Fixtures/Plugin"

#check plugin.integration.dep.Common
#check plugin.integration.odd.CommonFile
#check plugin.integration.app.Main

def main : IO Unit :=
  pure ()
