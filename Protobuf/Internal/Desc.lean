module

/-
The bootstrap descriptor schema is intentionally split along its dependency
graph.  Keeping these generated declarations in one module makes Lean
elaborate one very large block serially; the aggregate imports below preserve
the historical `Protobuf.Internal.Desc` API while allowing independent option
and schema groups to compile in parallel.
-/

public import Protobuf.Internal.Desc.Base
public import Protobuf.Internal.Desc.Core
public import Protobuf.Internal.Desc.Features
public import Protobuf.Internal.Desc.Options
public import Protobuf.Internal.Desc.Schema
