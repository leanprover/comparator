import Lean.Environment

namespace Comparator

structure ExportedEnv where
  constMap : Std.HashMap Lean.Name Lean.ConstantInfo
  constOrder : Array Lean.Name
  deriving Inhabited

end Comparator
