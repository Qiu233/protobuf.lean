import Lake
open Lake DSL

package "protobuf" where
  version := v!"0.1.0"

lean_lib «Protobuf» where
  -- add library configuration options here

@[default_target]
lean_exe "protobuf" where
  root := `Main

require binary from git "https://github.com/Qiu233/binary" @ "e6f373912bf7e0b4553e5f07c89af14bd2c40f52"
