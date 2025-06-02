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

def compareAt (challenge solution : ExportedEnv) (target : Lean.Name) : Except String Unit := do
  let some challengeConst := challenge.constMap[target]?
    | throw "Const not found in challenge: '{target}'"
  let some solutionConst := solution.constMap[target]?
    | throw "Const not found in solution: '{target}'"

  let .thmInfo challengeConst := challengeConst
    | throw s!"Challenge constant is not a theorem: '{target}'"

  let .thmInfo solutionConst := solutionConst
    | throw s!"Solution constant is not a theorem: '{target}'"

  if challengeConst.toConstantVal != solutionConst.toConstantVal then
    throw s!"Challenge and solution theorem statement do not match: '{target}'"

  let worklist := challengeConst.type.getUsedConstants
  Compare.loop.run { challenge, solution } |>.run'  { worklist, checked := {} }

end Comparator
