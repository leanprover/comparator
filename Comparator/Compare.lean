/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.Axioms
import Export.Parse

namespace Comparator

namespace Compare

structure Context where
  challenge : Export.ExportedEnv
  solution : Export.ExportedEnv
  holes : Std.HashSet Lean.Name

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

/--
Check that two `DefinitionVal`s agree on everything except the body (`value`) and
reducibility hints: same name, level params, type, safety, and mutual group.
-/
def checkHoleDefnVal [Monad m] [MonadExcept String m] (target : Lean.Name)
    (cc sc : Lean.DefinitionVal) : m Unit := do
  if cc.toConstantVal != sc.toConstantVal then
    throw s!"Hole type/name/level-params mismatch for '{target}'"
  if cc.safety != sc.safety then
    throw s!"Hole safety mismatch for '{target}'"
  if cc.all != sc.all then
    throw s!"Hole mutual-group mismatch for '{target}'"

/--
Check that a hole is a `.defnInfo` on both sides and that the two definitions agree
modulo body + hints (see `checkHoleDefnVal`).
-/
def checkHoleMatch [Monad m] [MonadExcept String m] (target : Lean.Name)
    (challengeConst solutionConst : Lean.ConstantInfo) : m Unit := do
  let .defnInfo cc := challengeConst
    | throw s!"Challenge hole '{target}' is not a definition"
  let .defnInfo sc := solutionConst
    | throw s!"Solution hole '{target}' is not a definition"
  checkHoleDefnVal target cc sc

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

    if (← read).holes.contains target then
      checkHoleMatch target challengeConst solutionConst
    else
      if challengeConst != solutionConst then
        throw s!"Const does not match between challenge and target '{target}'"

    addRelevantConsts solutionConst

    modify fun s => { s with checked := s.checked.insert target }
    loop

end Compare

/--
Verify that each theorem target in `solution` has the same statement as in `challenge`,
and that all transitively-used constants match byte-for-byte between the two environments,
except for names listed in `holes`.

For `holes`, `solution` may provide a body different from `challenge`'s (the motivating use
case is `def n : Nat := sorry` in the challenge being filled in by the solution). We still
require the name, universe params, type, safety, and mutual-group list to match. The
solution's hole body is walked transitively, so any constants it references must themselves
match the challenge (or be other holes).
-/
def compareAt (challenge solution : Export.ExportedEnv)
    (targets : Array Lean.Name) (holes : Array Lean.Name) (primitive : Array Lean.Name) :
    Except String Unit := do
  let mut worklist := primitive
  for target in targets do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"


    let (challengeConst, solutionConst) ←
      match challengeConst, solutionConst with
      | .thmInfo cc, .thmInfo sc
      | .axiomInfo cc, .axiomInfo sc => pure (cc.toConstantVal, sc.toConstantVal)
      | _, _ => throw s!"Challenge and solution constant kind don't match: '{target}'"

    if challengeConst != solutionConst then
      throw s!"Challenge and solution theorem statement do not match: '{target}'"

    worklist := worklist ++ challengeConst.type.getUsedConstants

  for hole in holes do
    let some challengeConst := challenge.constMap[hole]?
      | throw s!"Hole not found in challenge: '{hole}'"
    let some solutionConst := solution.constMap[hole]?
      | throw s!"Hole not found in solution: '{hole}'"
    Compare.checkHoleMatch hole challengeConst solutionConst
    worklist := worklist ++ challengeConst.type.getUsedConstants

  let holesSet := Std.HashSet.ofArray holes
  Compare.loop.run { challenge, solution, holes := holesSet } |>.run' { worklist, checked := {} }

end Comparator
