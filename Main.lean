/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean
import Comparator
import Lean4Checker.Replay

namespace Comparator

structure Context where
  projectDir : System.FilePath
  challengeModule : Lean.Name
  solutionModule : Lean.Name
  theoremNames : Array Lean.Name
  legalAxioms : Array Lean.Name

abbrev M := ReaderT Context IO

structure LandrunArgs where
  cmd : String
  args : Array String
  envPass : Array String
  envOverride : Array (String × Option String) := #[]
  writablePaths : Array System.FilePath

@[inline]
def getTheoremNames : M (Array Lean.Name) := do return (← read).theoremNames

@[inline]
def getProjectDir : M System.FilePath := do return (← read).projectDir

@[inline]
def getChallengeModule : M Lean.Name := do return (← read).challengeModule

@[inline]
def getSolutionModule : M Lean.Name := do return (← read).solutionModule

@[inline]
def getLegalAxioms : M (Array Lean.Name) := do return (← read).legalAxioms

def landrunArgs (writablePaths : Array System.FilePath) (env : Array String) : Array String :=
  let base := #["--best-effort", "--rox", "/", "--rw", "/dev"]
  let base := env.foldl (init := base) (fun acc env => acc ++ #["--env", env])
  writablePaths.foldl (init := base) (fun acc path => acc ++ #["--rwx", path.toString])

def runSandBoxedWithStdout (spawnArgs : LandrunArgs) : M String := do
  let args :=
    landrunArgs spawnArgs.writablePaths spawnArgs.envPass ++
    #[spawnArgs.cmd] ++
    spawnArgs.args
  IO.Process.run {
    cmd := "landrun",
    args,
    stdout := .piped,
    env := spawnArgs.envOverride
    cwd := (← getProjectDir)
  }

def runSandBoxed (spawnArgs : LandrunArgs) : M Unit := do
  let args :=
    landrunArgs spawnArgs.writablePaths spawnArgs.envPass ++
    #[spawnArgs.cmd] ++
    spawnArgs.args
  let proc ← IO.Process.spawn {
    cmd := "landrun",
    args,
    env := spawnArgs.envOverride
    cwd := (← getProjectDir)
  }
  let ret ← proc.wait
  if ret != 0 then
    throw <| .userError s!"Child exited with {ret}"

def safeLakeBuild (target : Lean.Name) : M Unit := do
  IO.println s!"Building {target}"
  let dotLakeDir := (← getProjectDir) / ".lake"
  runSandBoxed {
    cmd := "lake",
    args := #["build", target.toString (escape := false)],
    envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    writablePaths := #[dotLakeDir]
  }

def safeExport (module : Lean.Name) (decls : Array Lean.Name) : M String := do
  IO.println s!"Exporting {decls} from {module}"
  let baseArgs := #[module.toString (escape := false), "--"]
  let args := decls.foldl (·.push <| ·.toString (escape := false)) baseArgs
  runSandBoxedWithStdout {
    cmd := "lean4export",
    args := args,
    envPass := #["PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    writablePaths := #[]
  }

def runKernel (solution : Comparator.ExportedEnv) : M Unit := do
  IO.println "Running kernel on solution."
  let mut env ← Lean.mkEmptyEnvironment
  let mut constMap := solution.constMap
  -- Lean's kernel interprets just the addition of `Quot as adding all of these so adding them
  -- multiple times leads to errors.
  constMap := constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  discard <| env.replay' constMap
  IO.println "Solution valid."

def verifyMatch (challengeExport : String) (solutionExport : String) : M Unit := do
  let challenge ← IO.ofExcept <| Comparator.parse challengeExport
  let solution ← IO.ofExcept <| Comparator.parse solutionExport
  let theoremNames ← getTheoremNames
  let targets := (← getTheoremNames) ++ (← getLegalAxioms)
  IO.ofExcept <| Comparator.compareAt challenge solution targets
  IO.ofExcept <| Comparator.checkAxioms solution theoremNames (← getLegalAxioms)
  runKernel solution

def compareIt : M Unit := do
  let challengeModule ← getChallengeModule
  let exportTargets := (← getTheoremNames) ++ (← getLegalAxioms)
  safeLakeBuild challengeModule
  let challengeExport ← safeExport challengeModule exportTargets

  let solutionModule ← getSolutionModule
  safeLakeBuild solutionModule
  let solutionExport ← safeExport solutionModule exportTargets

  verifyMatch challengeExport solutionExport

  IO.println "Your solution is okay!"

structure Config where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  permitted_axioms : Array String
  deriving Lean.FromJson, Lean.ToJson, Repr

def M.run (x : M α) (cfg : Config) : IO α := do
  let cwd ← IO.Process.getCurrentDir
  ReaderT.run x {
    projectDir := cwd
    challengeModule := cfg.challenge_module.toName,
    solutionModule := cfg.solution_module.toName,
    theoremNames := cfg.theorem_names.map String.toName,
    legalAxioms := cfg.permitted_axioms.map String.toName,
  }

end Comparator

def main (args : List String) : IO Unit := do
  let some (configPath : String) := args[0]?
    | throw <| .userError "Expected config file path as first argument."
  let content ← IO.FS.readFile configPath
  let config ← IO.ofExcept <| Lean.FromJson.fromJson? <| ← IO.ofExcept <| Lean.Json.parse content
  Comparator.M.run Comparator.compareIt config
