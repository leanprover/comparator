structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

theorem polymorphic_challenge.disproof.{w} (h : ∀ {α : Type w} {β : Type w} (_x : α) (_y : β), Nonempty (Equiv α β)) : False := by
  have h_equiv : Nonempty (Equiv (Sum PUnit.{w+1} PUnit.{w+1}) PUnit.{w+1}) := h (Sum.inl PUnit.unit) PUnit.unit
  cases h_equiv with
  | intro eq =>
    have h_inl := eq.left_inv (Sum.inl PUnit.unit)
    have h_inr := eq.left_inv (Sum.inr PUnit.unit)
    have h_contra : Sum.inl PUnit.unit = Sum.inr PUnit.unit := Eq.trans (Eq.symm h_inl) h_inr
    nomatch h_contra
