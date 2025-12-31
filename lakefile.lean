import Lake
open Lake DSL

package "protobuf" where
  version := v!"0.1.0"
  leanOptions := #[ ⟨`experimental.module, true⟩ ]

lean_lib «Protobuf» where

@[default_target]
lean_exe "protobuf" where
  root := `Main

require binary from git "https://github.com/Qiu233/binary" @ "34c54ee3dda26c4bfaff0041464756df2ecc0760"
