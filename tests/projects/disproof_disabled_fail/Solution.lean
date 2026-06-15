theorem foo.disproof (h : ∀ x : Nat, ¬ 1 + 1 = 2) : False :=
  h 0 rfl
