structure MyStruct.{u} (α : Type u) where
  A : α

theorem foo.disproof (h : ∀ (s : MyStruct.{1} Type) (_x : s.A), False) : False :=
  h ⟨PUnit.{1}⟩ PUnit.unit.{1}
