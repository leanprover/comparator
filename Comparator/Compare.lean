/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.ExportedEnv

namespace Comparator

namespace Compare

structure Context where
  challenge : ExportedEnv
  solution : ExportedEnv

structure State where
  worklist : Array Lean.Name
  checked : Std.HashSet Lean.Name

abbrev CompareM := ReaderT Context <| StateT State <| Except String

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

def addWorklist (n : Lean.Name) : CompareM Unit := do
  if !(← get).checked.contains n then
    modify fun s => { s with worklist := s.worklist.push n }

def addRelevantConsts (info : Lean.ConstantInfo) : CompareM Unit := do
  runForUsedConsts info addWorklist

partial def loop : CompareM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  if (← get).checked.contains target then
    loop
  else
    let some challengeConst := (← read).challenge.constMap[target]?
      | throw s!"Const not found in challenge '{target}'"
    let some solutionConst := (← read).solution.constMap[target]?
      | throw s!"Const not found in target '{target}'"

    if challengeConst != solutionConst then
      throw s!"Const does not match between challenge and target '{target}'"

    addRelevantConsts solutionConst

    modify fun s => { s with checked := s.checked.insert target }
    loop

end Compare

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

def compareAt (challenge solution : ExportedEnv) (targets : Array Lean.Name) :
    Except String Unit := do
  let mut worklist := #[]
  for target in targets do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"


    let (challengeConst, solutionConst) ←
      match challengeConst, solutionConst with
      | .thmInfo cc, .thmInfo sc
      | .axiomInfo cc, .axiomInfo sc
      | .defnInfo cc, .defnInfo sc
      | .opaqueInfo cc, .opaqueInfo sc
      | .quotInfo cc, .quotInfo sc
      | .inductInfo cc, .inductInfo sc
      | .ctorInfo cc, .ctorInfo sc
      | .recInfo cc, .recInfo sc => pure (cc.toConstantVal, sc.toConstantVal)
      | c, s => throw s!"Challenge and solution constant kind don't match: '{target}' (challenge: {constantKindName c}, solution: {constantKindName s})"

    if challengeConst != solutionConst then
      throw s!"Challenge and solution theorem statement do not match: '{target}'"

    worklist := worklist ++ challengeConst.type.getUsedConstants

  Compare.loop.run { challenge, solution } |>.run' { worklist, checked := {} }

end Comparator
