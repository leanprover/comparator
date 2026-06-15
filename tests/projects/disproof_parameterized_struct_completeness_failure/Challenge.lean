structure MyStruct.{u} (α : Type u) where
  A : α

theorem foo (s : MyStruct.{1} Type) (x : s.A) : False := sorry
