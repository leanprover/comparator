/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean
import Comparator.Axioms
import Export.Parse

open Lean Meta

namespace Comparator

inductive TheoremMode where
  | direct
  | disproof
  deriving BEq, Inhabited, ToJson, Repr

structure TheoremTarget where
  challengeName : Name
  solutionName : Name
  mode : TheoremMode
  deriving Inhabited, ToJson, Repr

def checkDisproof (challengeType : Expr) (challengeLevelParams : List Name) (solutionType : Expr) : IO Bool := do
  try
    let env ← importModules #[{ module := `Init }] {} 0
    let checkAction : MetaM Bool := do
      let us ← challengeLevelParams.mapM fun _ => mkFreshLevelMVar
      let expected := Expr.forallE `_h (challengeType.instantiateLevelParams challengeLevelParams us) (mkConst ``False) .default
      isDefEq solutionType expected
    let (res, _) ← (checkAction.run').toIO { fileName := "", fileMap := default } { env := env }
    return res
  catch _ =>
    return false

namespace Compare

structure Context where
  challenge : Export.ExportedEnv
  solution : Export.ExportedEnv
  definitionTargets : Std.HashSet Lean.Name

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
      | throw s!"Const not found in solution '{target}'"

    if (← read).definitionTargets.contains solutionConst.name then
      solutionConst.type.getUsedConstants.forM addWorklist
    else
      if challengeConst != solutionConst then
        throw s!"Const does not match between challenge and target '{target}'"
      addRelevantConsts solutionConst

    modify fun s => { s with checked := s.checked.insert target }
    loop

end Compare

def definitionHoleMatches (challengeHole solutionHole : Lean.DefinitionVal) : Bool :=
  challengeHole.toConstantVal == solutionHole.toConstantVal
    && challengeHole.safety == solutionHole.safety

def compareAt (challenge solution : Export.ExportedEnv) (theoremTargets : Array TheoremTarget)
    (definitionTargets : Array Lean.Name) (primitive : Array Lean.Name) : IO (Except String Unit) := ExceptT.run do
  let mut worklist := primitive

  for target in theoremTargets do
    let some challengeConst := challenge.constMap[target.challengeName]?
      | throw s!"Const not found in challenge: '{target.challengeName}'"
    let some solutionConst := solution.constMap[target.solutionName]?
      | throw s!"Const not found in solution: '{target.solutionName}'"

    worklist := worklist ++ challengeConst.type.getUsedConstants

    match target.mode with
    | .direct =>
      let (challengeVal, solutionVal) ←
        match challengeConst, solutionConst with
        | .thmInfo cc, .thmInfo sc
        | .axiomInfo cc, .axiomInfo sc => pure (cc.toConstantVal, sc.toConstantVal)
        | _, _ => throw s!"Challenge and solution constant kind don't match: '{target.solutionName}'"

      if challengeVal != solutionVal then
        throw s!"Challenge and solution theorem statement do not match: '{target.solutionName}'"

    | .disproof =>
      let .thmInfo cc := challengeConst
        | throw s!"Challenge target is not a theorem: '{target.challengeName}'"
      let .thmInfo sc := solutionConst
        | throw s!"Solution disproof target is not a theorem: '{target.solutionName}'"

      unless ← checkDisproof cc.type cc.levelParams sc.type do
        throw s!"Solution disproof statement does not match accepted disproof interface: '{target.solutionName}'"

  for target in definitionTargets do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"

    let .defnInfo challengeConst := challengeConst
      | throw s!"Challenge constant is not a definition: '{target}'"
    let .defnInfo solutionConst := solutionConst
      | throw s!"Solution constant is not a definition: '{target}'"

    if !definitionHoleMatches challengeConst solutionConst then
      throw s!"Const does not match between challenge and target '{target}'"

    worklist := worklist.push solutionConst.name

  let definitionTargets := Std.HashSet.ofArray definitionTargets
  Compare.loop.run { challenge, solution, definitionTargets } |>.run' { worklist, checked := {} }

end Comparator
