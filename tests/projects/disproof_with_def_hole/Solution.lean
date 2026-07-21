def myAnswer : Prop := True

theorem myThm.disproof (h : myAnswer ↔ (1 + 1 = 3)) : False := by
  have h_equiv : True ↔ (1 + 1 = 3) := h
  have h_contra : 1 + 1 = 3 := h_equiv.mp trivial
  nomatch h_contra
