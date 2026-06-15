theorem weird.disproof (h : ∀ (α : Type 0) (β : Type 0), ¬(ULift.{0} α = ULift.{0} β)) : False :=
  h PUnit PUnit rfl
