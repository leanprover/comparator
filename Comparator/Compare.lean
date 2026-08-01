/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.Axioms
import Export.Parse

open Lean

namespace Comparator

partial def matchLevel (l1 l2 : Level) (params : List Name) (subst : List (Name × Level)) : List (Name × Level) :=
  match l1, l2 with
  | .param n, _ => if params.contains n && !subst.any (·.1 == n) then (n, l2) :: subst else subst
  | .succ n1, .succ n2 => matchLevel n1 n2 params subst
  | .max n1 n2, .max m1 m2 => matchLevel n2 m2 params (matchLevel n1 m1 params subst)
  | .max n1 n2, l2 => matchLevel n2 l2 params (matchLevel n1 l2 params subst)
  | .imax n1 n2, .imax m1 m2 => matchLevel n2 m2 params (matchLevel n1 m1 params subst)
  | .imax n1 n2, l2 => matchLevel n2 l2 params (matchLevel n1 l2 params subst)
  | _, _ => subst

partial def collectLevels (e : Expr) (acc : List Level) : List Level :=
  match e with
  | .sort l => l :: acc
  | .const _ ls => ls ++ acc
  | .app f a => collectLevels f (collectLevels a acc)
  | .lam _ d b _
  | .forallE _ d b _ => collectLevels d (collectLevels b acc)
  | .letE _ t v b _ => collectLevels t (collectLevels v (collectLevels b acc))
  | .mdata _ b
  | .proj _ _ b => collectLevels b acc
  | _ => acc

def checkDisproof (chalType : Expr) (chalLevels : List Name) (solType : Expr) (solLevels : List Name) : Bool :=
  match solType with
  | .forallE _ exp (.const ``False []) _
  | .app (.const ``Not []) exp =>
    let subst := ((collectLevels chalType []).zip (collectLevels exp [])).foldl
      (fun acc (l1, l2) => matchLevel l1 l2 chalLevels acc) []
    let levels := chalLevels.map fun n => (subst.lookup n).getD Level.zero
    chalType.instantiateLevelParams chalLevels levels ==
      exp.instantiateLevelParams solLevels (solLevels.map .param)
  | _ => false

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

def compareAt (challenge solution : Export.ExportedEnv) (theoremTargets : Array Lean.Name)
    (definitionTargets : Array Lean.Name) (primitive : Array Lean.Name) (allowDisproofs : Bool := false) : Except String Unit := do
  let mut worklist := primitive

  for target in theoremTargets do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    worklist := worklist ++ challengeConst.type.getUsedConstants

    let dname := target ++ `disproof
    if allowDisproofs && solution.constMap[dname]?.isSome then
      let some solutionConst := solution.constMap[dname]?
        | unreachable!
      let .thmInfo cc := challengeConst
        | throw s!"Challenge target is not a theorem: '{target}'"
      let .thmInfo sc := solutionConst
        | throw s!"Solution disproof target is not a theorem: '{dname}'"

      unless checkDisproof cc.type cc.levelParams sc.type sc.levelParams do
        throw s!"Solution disproof statement does not match accepted disproof interface: '{dname}'"

    else
      let some solutionConst := solution.constMap[target]?
        | throw s!"Const not found in solution: '{target}'"
      let (challengeConst, solutionConst) ←
        match challengeConst, solutionConst with
        | .thmInfo cc, .thmInfo sc
        | .axiomInfo cc, .axiomInfo sc => pure (cc.toConstantVal, sc.toConstantVal)
        | _, _ => throw s!"Challenge and solution constant kind don't match: '{target}'"

      if challengeConst != solutionConst then
        throw s!"Challenge and solution theorem statement do not match: '{target}'"

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
