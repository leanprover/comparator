theorem add_zero_right (n : Nat) : n + 0 = n := rfl

theorem comm (n m : Nat) : n + m = m + n := by
  have _ := add_zero_right n
  grind
