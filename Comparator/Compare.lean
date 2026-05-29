/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.Axioms
import Export.Parse
import Lean.Util.InstantiateLevelParams

namespace Comparator

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

def canonicalLevelParams (levelParams : List Lean.Name) : List Lean.Name :=
  (List.range levelParams.length).map fun i => Lean.Name.mkSimple s!"_cmp_u_{i}"

def normalizeExprLevelParams (levelParams : List Lean.Name) (e : Lean.Expr) : Lean.Expr :=
  e.instantiateLevelParams levelParams ((canonicalLevelParams levelParams).map Lean.mkLevelParam)

def normalizeConstantVal (val : Lean.ConstantVal) : Lean.ConstantVal :=
  let levelParams' := canonicalLevelParams val.levelParams
  { val with
    levelParams := levelParams'
    type := normalizeExprLevelParams val.levelParams val.type }

def normalizeRecursorRule (levelParams : List Lean.Name) (rule : Lean.RecursorRule) :
    Lean.RecursorRule :=
  { rule with rhs := normalizeExprLevelParams levelParams rule.rhs }

def normalizeConstantInfo : Lean.ConstantInfo → Lean.ConstantInfo
  | .axiomInfo val =>
      .axiomInfo {
        val with
        levelParams := canonicalLevelParams val.levelParams
        type := normalizeExprLevelParams val.levelParams val.type
      }
  | .defnInfo val =>
      .defnInfo {
        val with
        levelParams := canonicalLevelParams val.levelParams
        type := normalizeExprLevelParams val.levelParams val.type
        value := normalizeExprLevelParams val.levelParams val.value
      }
  | .thmInfo val =>
      .thmInfo {
        val with
        levelParams := canonicalLevelParams val.levelParams
        type := normalizeExprLevelParams val.levelParams val.type
        value := normalizeExprLevelParams val.levelParams val.value
      }
  | .opaqueInfo val =>
      .opaqueInfo {
        val with
        levelParams := canonicalLevelParams val.levelParams
        type := normalizeExprLevelParams val.levelParams val.type
        value := normalizeExprLevelParams val.levelParams val.value
      }
  | .quotInfo val =>
      .quotInfo {
        val with
        levelParams := canonicalLevelParams val.levelParams
        type := normalizeExprLevelParams val.levelParams val.type
      }
  | .inductInfo val =>
      .inductInfo {
        val with
        levelParams := canonicalLevelParams val.levelParams
        type := normalizeExprLevelParams val.levelParams val.type
      }
  | .ctorInfo val =>
      .ctorInfo {
        val with
        levelParams := canonicalLevelParams val.levelParams
        type := normalizeExprLevelParams val.levelParams val.type
      }
  | .recInfo val =>
      .recInfo {
        val with
        levelParams := canonicalLevelParams val.levelParams
        type := normalizeExprLevelParams val.levelParams val.type
        rules := val.rules.map (normalizeRecursorRule val.levelParams)
      }

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
      if normalizeConstantInfo challengeConst != normalizeConstantInfo solutionConst then
        throw s!"Const does not match between challenge and target '{target}'"
      addRelevantConsts solutionConst

    modify fun s => { s with checked := s.checked.insert target }
    loop

end Compare

def definitionHoleMatches (challengeHole solutionHole : Lean.DefinitionVal) : Bool :=
  challengeHole.toConstantVal == solutionHole.toConstantVal
    && challengeHole.safety == solutionHole.safety

def compareAt (challenge solution : Export.ExportedEnv) (theoremTargets : Array Lean.Name)
    (definitionTargets : Array Lean.Name) (primitive : Array Lean.Name) : Except String Unit := do
  let mut worklist := primitive

  for target in theoremTargets do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"

    let (challengeConst, solutionConst) ←
      match challengeConst, solutionConst with
      | .thmInfo cc, .thmInfo sc
      | .axiomInfo cc, .axiomInfo sc => pure (cc.toConstantVal, sc.toConstantVal)
      | _, _ => throw s!"Challenge and solution constant kind don't match: '{target}'"

    if Compare.normalizeConstantVal challengeConst != Compare.normalizeConstantVal solutionConst then
      throw s!"Challenge and solution theorem statement do not match: '{target}'"

    worklist := worklist ++ challengeConst.type.getUsedConstants

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
