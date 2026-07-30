module

public import Protobuf.Reflection.Pool

public section

namespace Protobuf.Reflection

/--
The process-wide pool populated by statically generated protobuf modules.

The pool is created here but never mutated in this module. Generated
downstream modules register their own files from `initialize` declarations.
-/
initialize generatedPool : DescriptorPool ← DescriptorPool.new

end Protobuf.Reflection
