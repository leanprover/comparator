import Lean.Environment

namespace Comparator

namespace Utils

/-- Get a human-readable name for the kind of constant -/
def constantKindName (info : Lean.ConstantInfo) : String :=
  match info with
  | .axiomInfo .. => "axiom"
  | .defnInfo .. => "def"
  | .thmInfo .. => "theorem"
  | .opaqueInfo .. => "opaque"
  | .quotInfo .. => "quot"
  | .inductInfo .. => "inductive"
  | .ctorInfo .. => "constructor"
  | .recInfo .. => "recursor"

end Utils

end Comparator
