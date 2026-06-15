/-
  CHALLENGE: Universe-Polymorphic Type Inequality (weird)
  Tests valid universe-specialization disproofs under independent parameters.
-/
theorem weird (α : Type u) (β : Type v) : ¬(ULift.{v} α = ULift.{u} β) := sorry
