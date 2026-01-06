import Lake
open Lake DSL

package "protobuf" where
  version := v!"0.1.0"
  leanOptions := #[ ⟨`experimental.module, true⟩ ]

@[default_target]
lean_lib Protobuf where

lean_exe Plugin where
  root := `Plugin
  exeName := "protoc-gen-lean4"

require binary from git "https://github.com/Lean-zh/binary.git" @ "26cae831784e3135923c506be2b739f5db8bc3cf"
