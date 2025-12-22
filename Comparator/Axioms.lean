/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.ExportedEnv
import Comparator.Utils

namespace Comparator

namespace Axioms

structure Context where
  solution : ExportedEnv
  allowPartial : Bool
  targetNames : Std.HashSet Lean.Name
  legalAxioms : Std.HashSet Lean.Name

structure State where
  worklist : Array Lean.Name
  checked : Std.HashSet Lean.Name

abbrev AxiomsM := ReaderT Context <| StateT State <| Except String

def addWorklist (n : Lean.Name) : AxiomsM Unit := do
  if !(← get).checked.contains n then
    modify fun s => { s with worklist := s.worklist.push n }

partial def loop : AxiomsM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  if (← get).checked.contains target then
    loop
  else
    let some info := (← read).solution.constMap[target]?
      | throw s!"Constant not found in solution '{target}'"

    if let .axiomInfo info := info then
      if !(← read).legalAxioms.contains info.name then
        throw s!"Illegal axiom detected: '{target}'"

    if (← read).targetNames.contains target then
      if info.isUnsafe then throw s!"Solution constant is unsafe: '{target}'"
      if info.isPartial && !(← read).allowPartial then throw s!"Solution constant is partial: '{target}'"

    runForUsedConsts info addWorklist

    modify fun s => { s with checked := s.checked.insert target }
    loop

end Axioms

def checkAxioms (solution : ExportedEnv) (targets : Array Lean.Name) (legal : Array Lean.Name) (allowPartial : Bool) :
    Except String Unit := do
  let mut worklist := #[]
  let legalAxioms := Std.HashSet.ofArray legal
  let targetNames := Std.HashSet.ofArray targets

  for target in legal do
    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"

    match solutionConst with
    | .thmInfo _ | .axiomInfo _ => pure ()
    | _ => throw s!"Solution must not instantiate allowed axioms with informative constants ({Utils.constantKindName solutionConst} forbidden): '{target}'"

  let prog := do
    targets.forM Axioms.addWorklist
    Axioms.loop
  prog.run { solution, allowPartial, legalAxioms, targetNames } |>.run' { worklist, checked := {} }
end Comparator
