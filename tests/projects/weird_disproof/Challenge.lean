/- Tests valid universe-specialization disproofs
See: https://github.com/leanprover/lean4/pull/13771#issuecomment-4514606134 -/
theorem weird (α : Type u) (β : Type v) : ¬(ULift.{v} α = ULift.{u} β) := sorry
