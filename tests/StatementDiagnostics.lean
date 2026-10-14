import Comparator.Compare

open Lean Comparator

private def target : Name := `testTheorem

-- These in-memory exports exercise comparison without installing declarations
-- into a Lean environment or asking a pretty printer to elaborate them.
private def mkTheoremInfo (type : Expr) (levelParams : List Name := []) : ConstantInfo :=
  .thmInfo { name := target, levelParams, type, value := .bvar 0 }

private def mkAxiomInfo (type : Expr) : ConstantInfo :=
  .axiomInfo { name := target, levelParams := [], type, isUnsafe := false }

private def exported (info : ConstantInfo) : Export.ExportedEnv :=
  { constMap := ({} : Std.HashMap Name ConstantInfo).insert target info, constOrder := #[target] }

private def compare (challenge solution : ConstantInfo) : Except String Unit :=
  compareAt (exported challenge) (exported solution) #[target] #[] #[]

private def expectMismatch (result : Except String Unit) (details : Array String) : IO Unit := do
  let .error message := result
    | throw <| IO.userError "Expected statement mismatch"
  let expectedPrefix := s!"Challenge and solution theorem statement do not match: '{target}'"
  unless message.startsWith expectedPrefix do
    throw <| IO.userError s!"Missing mismatch prefix in: {message}"
  for detail in details do
    unless message.splitOn "\n" |>.contains detail do
      throw <| IO.userError s!"Missing diagnostic '{detail}' in: {message}"

private def expectError (result : Except String Unit) (expected : String) : IO Unit := do
  let .error message := result
    | throw <| IO.userError "Expected comparison error"
  unless message == expected do
    throw <| IO.userError s!"Expected '{expected}', got '{message}'"

private def expectAccepted (result : Except String Unit) : IO Unit := do
  match result with
  | .ok () => pure ()
  | .error message => throw <| IO.userError s!"Expected acceptance, got '{message}'"

private def tests : Array (String × IO Unit) := #[
  ("theorem type mismatch", expectMismatch
    (compare (mkTheoremInfo <| mkConst `Nat) (mkTheoremInfo <| mkConst `Int))
    #["Challenge type: Nat", "Solution type: Int",
      "Challenge universe parameters: []", "Solution universe parameters: []"]),
  ("axiom type mismatch", expectMismatch
    (compare (mkAxiomInfo <| mkConst `Bool) (mkAxiomInfo <| mkConst `Nat))
    #["Challenge type: Bool", "Solution type: Nat"]),
  ("universe parameter mismatch with identical types", expectMismatch
    (compare (mkTheoremInfo (.sort <| .param `u) [`u])
      (mkTheoremInfo (.sort <| .param `u) [`v]))
    #["Challenge type: Sort.{u}", "Solution type: Sort.{u}",
      "Challenge universe parameters: [u]", "Solution universe parameters: [v]"]),
  ("matching theorem", expectAccepted <|
    compare (mkTheoremInfo <| .sort .zero) (mkTheoremInfo <| .sort .zero)),
  ("matching axiom", expectAccepted <|
    compare (mkAxiomInfo <| .sort .zero) (mkAxiomInfo <| .sort .zero)),
  ("missing challenge target", expectError
    (compareAt default (exported <| mkTheoremInfo <| .sort .zero) #[target] #[] #[])
    s!"Const not found in challenge: '{target}'"),
  ("missing solution target", expectError
    (compareAt (exported <| mkTheoremInfo <| .sort .zero) default #[target] #[] #[])
    s!"Const not found in solution: '{target}'"),
  ("different constant kinds", expectError
    (compare (mkTheoremInfo <| .sort .zero) (mkAxiomInfo <| .sort .zero))
    s!"Challenge and solution constant kind don't match: '{target}'")
]

#eval do
  let mut failed := 0
  for (name, test) in tests do
    try
      test
      IO.println s!"PASS: {name}"
    catch error =>
      failed := failed + 1
      IO.println s!"FAIL: {name}: {error}"
  unless failed == 0 do
    throw <| IO.userError s!"{failed} statement diagnostic regressions failed"
