import Lake
open Lake DSL

package "protobuf" where
  version := v!"0.1.0"
  leanOptions := #[ ⟨`experimental.module, true⟩ ]

require binary from git "https://github.com/Lean-zh/binary"

@[default_target]
lean_lib Protobuf where

lean_exe Plugin where
  root := `Plugin
  exeName := "protoc-gen-lean4"

lean_lib Bench where
  roots := #[`Test.Bench]

lean_exe benchProtoEncode where
  root := `Test.Bench.ProtoEncode

lean_exe benchProtoDecode where
  root := `Test.Bench.ProtoDecode

lean_exe benchJsonEncode where
  root := `Test.Bench.JsonEncode

lean_exe benchJsonDecode where
  root := `Test.Bench.JsonDecode
