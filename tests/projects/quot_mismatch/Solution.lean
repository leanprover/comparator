prelude

inductive True : Prop where
  | intro : True

-- comparator's `primitiveTargets` must exist in both modules or lean4export aborts.
def Nat.add        (_ _ : True) : True := True.intro
def Nat.sub        (_ _ : True) : True := True.intro
def Nat.mul        (_ _ : True) : True := True.intro
def Nat.pow        (_ _ : True) : True := True.intro
def Nat.gcd        (_ _ : True) : True := True.intro
def Nat.div        (_ _ : True) : True := True.intro
def Nat.mod        (_ _ : True) : True := True.intro
def Nat.beq        (_ _ : True) : True := True.intro
def Nat.ble        (_ _ : True) : True := True.intro
def Nat.land       (_ _ : True) : True := True.intro
def Nat.lor        (_ _ : True) : True := True.intro
def Nat.xor        (_ _ : True) : True := True.intro
def Nat.shiftLeft  (_ _ : True) : True := True.intro
def Nat.shiftRight (_ _ : True) : True := True.intro
def String.ofList  (_   : True) : True := True.intro
def Char.ofNat     (_   : True) : True := True.intro
def List           (_   : True) : True := True.intro
def eagerReduce    (_   : True) : True := True.intro

-- The target. Honest, true, kernel-valid.
theorem Quot.lift : True := True.intro
