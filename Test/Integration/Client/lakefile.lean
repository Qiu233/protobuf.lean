import Lake
open Lake DSL

-- A package of its own, so that `Client.lean` reaches `Protobuf.Json` the way
-- a downstream client does: through the dependency's library, rather than as
-- one more module of the package that defines it.
package "jsonClient"

require protobuf from ".." / ".." / ".."

lean_exe client where
  root := `Client
