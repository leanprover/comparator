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
  leanPrefix : System.FilePath
  gitLocation : System.FilePath

abbrev M := ReaderT Context IO

structure LandrunArgs where
  cmd : String
  args : Array String
  envPass : Array String
  envOverride : Array (String × Option String) := #[]
  readablePaths : Array System.FilePath
  writablePaths : Array System.FilePath
  executablePaths : Array System.FilePath

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

@[inline]
def getLeanPrefix : M System.FilePath := do return (← read).leanPrefix

@[inline]
def getGitLocation : M System.FilePath := do return (← read).gitLocation

def queryGitLocation : IO System.FilePath := do
  let out ← IO.Process.run {
    cmd := "which",
    args := #["git"],
    stdout := .piped,
  }
  return out.trimAscii.toString

def queryLeanPrefix (projectDir : System.FilePath) : IO System.FilePath := do
  let out ← IO.Process.run {
    cmd := "lean",
    args := #["--print-prefix"],
    stdout := .piped,
    cwd := projectDir
  }
  return out.trimAscii.toString

def landrunArgs (readablePaths writablePaths executablePaths : Array System.FilePath) (env : Array String) : Array String :=
  let args := #["--best-effort", "--ro", "/", "--rw", "/dev", "-ldd", "-add-exec"]
  let args := env.foldl (init := args) (fun acc env => acc ++ #["--env", env])
  let args := readablePaths.foldl (init := args) (fun acc path => acc ++ #["--ro", path.toString])
  let args := writablePaths.foldl (init := args) (fun acc path => acc ++ #["--rwx", path.toString])
  let args := executablePaths.foldl (init := args) (fun acc path => acc ++ #["--rox", path.toString])
  args

def runSandBoxedWithStdout (spawnArgs : LandrunArgs) : M String := do
  let args :=
    landrunArgs spawnArgs.readablePaths spawnArgs.writablePaths spawnArgs.executablePaths spawnArgs.envPass ++
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
    landrunArgs spawnArgs.readablePaths spawnArgs.writablePaths spawnArgs.executablePaths spawnArgs.envPass ++
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
  let leanPrefix ← getLeanPrefix
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"
  let gitLocation ← getGitLocation

  runSandBoxed {
    cmd := "lake",
    args := #["build", target.toString (escape := false)],
    envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir]
    writablePaths := #[dotLakeDir]
    executablePaths := #[leanPrefix, gitLocation]
  }

def safeExport (module : Lean.Name) (decls : Array Lean.Name) : M String := do
  IO.println s!"Exporting {decls} from {module}"
  let baseArgs := #[module.toString (escape := false), "--"]
  let args := decls.foldl (·.push <| ·.toString (escape := false)) baseArgs

  let leanPrefix ← getLeanPrefix
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"
  runSandBoxedWithStdout {
    cmd := "lean4export",
    args := args,
    envPass := #["PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir, dotLakeDir]
    writablePaths := #[]
    executablePaths := #[leanPrefix]
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
  IO.ofExcept <| Comparator.compareAt challenge solution (← getTheoremNames) (← getLegalAxioms)
  IO.ofExcept <| Comparator.checkAxioms solution (← getTheoremNames) (← getLegalAxioms)
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
  let leanPrefix ← queryLeanPrefix cwd
  let gitLocation ← queryGitLocation
  ReaderT.run x {
    projectDir := cwd
    challengeModule := cfg.challenge_module.toName,
    solutionModule := cfg.solution_module.toName,
    theoremNames := cfg.theorem_names.map String.toName,
    legalAxioms := cfg.permitted_axioms.map String.toName,
    leanPrefix := leanPrefix,
    gitLocation := gitLocation,
  }

end Comparator

def main (args : List String) : IO Unit := do
  let some (configPath : String) := args[0]?
    | throw <| .userError "Expected config file path as first argument."
  let content ← IO.FS.readFile configPath
  let config ← IO.ofExcept <| Lean.FromJson.fromJson? <| ← IO.ofExcept <| Lean.Json.parse content
  Comparator.M.run Comparator.compareIt config
