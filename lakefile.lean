import Lake
open Lake DSL

package "protobuf" where
  version := v!"0.1.0"
  leanOptions := #[ ⟨`experimental.module, true⟩ ]

lean_lib «Protobuf» where

@[default_target]
lean_exe "protobuf" where
  root := `Main

require binary from git "https://github.com/Qiu233/binary" @ "d845ca7766aebeabc481f95d0c738cfb80828369"
