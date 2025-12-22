/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.ExportedEnv
import Comparator.Utils

namespace Comparator

namespace Compare

structure Context where
  challenge : ExportedEnv
  solution : ExportedEnv
  targetNames : Std.HashSet Lean.Name

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

partial def loop : CompareM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  if (← get).checked.contains target then
    loop
  else
    let some solutionConst := (← read).solution.constMap[target]?
      | throw s!"Const not found in target '{target}'"

    if let some challengeConst := (← read).challenge.constMap[target]? then
      -- Solution constant values don't need to match, since the challenges are expected to be axioms
      if (← read).targetNames.contains target then
        if challengeConst.toConstantVal != solutionConst.toConstantVal then
          throw s!"Challenge and solution types do not match: '{target}'"
      else
        if challengeConst != solutionConst then
          throw s!"Const does not match between challenge and target '{target}'"

    runForUsedConsts solutionConst addWorklist

    modify fun s => { s with checked := s.checked.insert target }
    loop

end Compare

def compareAt (challenge solution : ExportedEnv) (targets axioms : Array Lean.Name) :
    Except String Unit := do
  let mut worklist := targets
  let targetNames := Std.HashSet.ofArray targets
  let targetsAndAxioms := targets ++ axioms

  for target in targetsAndAxioms do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    match challengeConst with
    | .thmInfo _ | .axiomInfo _ => pure ()
    | _ => throw s!"Challenge must be theorem or axiom not {Utils.constantKindName challengeConst}: '{target}'"

  let prog := do
    targetsAndAxioms.forM Compare.addWorklist
    Compare.loop
  prog.run { challenge, solution, targetNames } |>.run' { worklist, checked := {} }

end Comparator
