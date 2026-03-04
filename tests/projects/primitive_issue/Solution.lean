prelude
import Init.Prelude
import Init.Core

def Nat.gcd (_ _ : Nat) : Nat := 0

theorem thm1 a b : Nat.gcd a b = 0 := by
  unfold Nat.gcd
  rfl

theorem thm2 : Nat.gcd 1 1 = 1 := rfl

theorem boom : False :=
  Nat.noConfusion <| Eq.trans (thm1 1 1).symm thm2

-- The following are just to make the export “primitive-complete”
def Nat.land (_ _ : Nat) : Nat := 0
def Nat.lor (_ _ : Nat) : Nat := 0
def Nat.xor (_ _ : Nat) : Nat := 0
def Nat.shiftRight (_ _ : Nat) : Nat := 0
def Nat.shiftLeft (_ _ : Nat) : Nat := 0
