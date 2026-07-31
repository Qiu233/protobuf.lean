import Protobuf.Utils

namespace Test.Core.Utils

example : !(#[] : Array Nat).hasDups := by native_decide
example : !(#[1] : Array Nat).hasDups := by native_decide
example : !(#[1, 2, 3] : Array Nat).hasDups := by native_decide
example : (#[1, 1] : Array Nat).hasDups := by native_decide
example : (#[1, 2, 1] : Array Nat).hasDups := by native_decide
example : (#[1, 2, 2] : Array Nat).hasDups := by native_decide
example :
    (#[1, 2, 3] : Array Nat).hasDupsBy (fun left right => left % 2 == right % 2) := by
  native_decide

end Test.Core.Utils
