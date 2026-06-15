/-
  CHALLENGE: Universe-Dependent Isomorphism Target Spec
  Tests valid disproofs under a target that strictly depends on and uses
  the universe level parameter u:
  ∀ {α : Type u} (x : α), Nonempty (Equiv α PUnit.{u+1})
-/
structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

theorem polymorphic_challenge {α : Type u} (x : α) : Nonempty (Equiv α PUnit.{u+1}) := sorry
