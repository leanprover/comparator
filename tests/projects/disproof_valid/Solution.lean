theorem foo.disproof (h : ∀ x : Nat, ¬ 1 + 1 = 2) : False :=
  h 0 rfl

theorem bar.disproof (h : 1 + 1 = 3) : False := by
  nomatch h
