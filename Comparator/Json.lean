import Lean

namespace Comparator

def constKind : Lean.ConstantInfo → String
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

structure KernelReport where
  accepted : Option Bool := none
  failureMessage : Option String := none
  deriving Lean.ToJson, Inhabited, Repr

inductive CheckFailure where
  | kind (kind1 kind2 : String) -- Declaration kind mismatch
  | signature                   -- Target statement/signature mismatch
  | dependency                  -- Transitive dependency DAG mismatch
  | axioms                      -- Illegal leaf axioms detected
  | notFound                    -- Target decl not found
  deriving Lean.ToJson, Inhabited, Repr

structure TargetReport where
  targetName : Lean.Name
  targetKind : String
  failureCategory : Option CheckFailure
  failureMessage : Option String
  deriving Lean.ToJson, Inhabited, Repr

structure VerificationReport where
  reports : Array TargetReport := #[]
  kernel : KernelReport := {}
  nanoda : KernelReport := {}
  deriving Lean.ToJson, Inhabited, Repr

end Comparator
