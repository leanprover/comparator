/-
  CHALLENGE: False Two-Universe Isomorphism Target Spec
  Tests valid disproofs under a target that strictly depends on and uses
  both independent universe level parameters u and v:
  ∀ {α : Type u} {β : Type v} (x : α) (y : β), Nonempty (Equiv α β)
-/
structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

theorem polymorphic_challenge {α : Type u} {β : Type v} (x : α) (y : β) : Nonempty (Equiv α β) := sorry
