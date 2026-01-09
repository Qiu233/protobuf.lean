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

require binary from git "https://github.com/Lean-zh/binary.git" @ "2fb5c4b9b3d53bcd09461ef0f69ea455b3144b12"
