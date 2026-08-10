import Lean
open Lean Elab Term

/-- The structure the statement is really about. -/
structure S : Type where
  a : Nat

/-- The definition hole: the solver supplies the carrier. -/
def T : Type := S

/-- Elaborates to a raw `Expr.proj`. Ordinary elaborator, nothing unchecked. -/
elab "pr% " s:term : term => do
  return Expr.proj `S 0 (← elabTerm s none)

theorem tgt : ∀ (s : T), (pr% s) = (0 : Nat) := sorry
