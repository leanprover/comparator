universe u_1

def helper (β : Type u_1) : β = β := rfl

universe u_2

theorem sameType (α : Type u_2) : α = α := by
  rfl
