/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.ExportedEnv

namespace Comparator

namespace Axioms

structure Context where
  solution : ExportedEnv
  legalAxioms : Std.HashSet Lean.Name

structure State where
  worklist : Array Lean.Name
  checked : Std.HashSet Lean.Name

abbrev AxiomsM := ReaderT Context <| StateT State <| Except String

partial def loop : AxiomsM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  if (← get).checked.contains target then
    loop
  else
    let some info := (← read).solution.constMap[target]?
      | throw s!"Constant not found in solution '{target}'"

    runForUsedConsts info validateConst

    modify fun s => { s with checked := s.checked.insert target }
    loop
where
  validateConst (n : Lean.Name) : AxiomsM Unit := do
    let some info := (← read).solution.constMap[n]?
      | throw s!"Constant not found in solution '{n}'"

    if let .axiomInfo info := info then
      if !(← read).legalAxioms.contains info.name then
        throw s!"Illegal axiom detected: '{n}'"

    if !(← get).checked.contains n then
      modify fun s => { s with worklist := s.worklist.push n }

end Axioms

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

def checkAxioms (solution : ExportedEnv) (targets : Array Lean.Name) (legal : Array Lean.Name) :
    Except String Unit := do
  let mut worklist := #[]
  for target in targets do
    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"
    let info := match solutionConst with
      | .thmInfo info
      | .defnInfo info => info.value.getUsedConstants
      | _ => throw s!"Solution constant is a {constantKindName solutionConst} which is not a theorem or def: '{target}'"
    worklist := worklist ++ info.value.getUsedConstants

  let legalAxioms := Std.HashSet.ofArray legal
  Axioms.loop.run { solution, legalAxioms } |>.run' { worklist, checked := {} }

end Comparator
