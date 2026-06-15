/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.Util
import Export.Parse

namespace Comparator

abbrev AxiomCache := Std.HashMap Lean.Name Lean.NameSet

partial def getAxioms (env : Export.ExportedEnv) (targetName : Lean.Name)
    (cache : AxiomCache := {}) : Except String (AxiomCache × Array Lean.Name) := do
  let rec collect (n : Lean.Name) : StateT AxiomCache (Except String) Lean.NameSet := do
    if let some cached := (← get)[n]? then
      return cached
    let some info := env.constMap[n]?
      | throw s!"Constant not found in solution '{n}'"

    let res ← if let .axiomInfo _ := info then
      pure {n}
    else
      modify (·.insert n {})
      let foldOne (c : Lean.Name) :
          StateT Lean.NameSet (StateT AxiomCache (Except String)) Unit := do
        let s ← liftM (collect c)
        modify (·.merge s)
      runForUsedConsts info foldOne |>.run {} |>.map (·.2)

    modify (·.insert n res)
    return res

  let (resSet, updatedCache) ← collect targetName |>.run cache
  return (updatedCache, resSet.toArray)

def checkAxioms (solution : Export.ExportedEnv) (theoremTargets : Array Lean.Name)
    (definitionTargets : Array Lean.Name) (legalAxioms : Array Lean.Name)
    (cache : AxiomCache := {}) : Except String AxiomCache := do
  let legalAxiomsSet := Std.HashSet.ofArray legalAxioms

  let checkTarget (isTheorem : Bool) (target : Lean.Name) :
      StateT AxiomCache (Except String) Unit := do
    let some const := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"
    match isTheorem, const with
    | true, .thmInfo _ | false, .defnInfo _ =>
      let (nextCache, axioms) ← liftM <| getAxioms solution target (← get)
      set nextCache
      for ax in axioms do
        if !legalAxiomsSet.contains ax then
          throw s!"Illegal axiom detected: '{ax}'"
    | true, _ => throw s!"Solution constant is not a theorem: '{target}'"
    | false, _ => throw s!"Solution constant is not a definition: '{target}'"

  let ((), finalCache) ← (do
    theoremTargets.forM (checkTarget true)
    definitionTargets.forM (checkTarget false)).run cache
  return finalCache

end Comparator
