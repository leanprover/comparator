/- Tests static type and universe level inference for structure projections on fields with varying universe levels. -/
structure MyStruct.{u} where
  A : Type u
  B : Type u

theorem foo (s : MyStruct.{1}) (h : s.B) : False := sorry
