import Lean


/-!
Two files:
- Challenge.lean: Containing theorem called `challenge` with `sorry`
- Solution.lean: Containing theorem called `challenge` with proof

1. Obtain Challenge.olean + Solution.olean as well as possible dependency oleans in a way that
   doesn't touch the system or each other (???)
2. Serialize both olean closures into export format with (`lean4export`)[https://github.com/leanprover/lean4export].
   As olean files are potentially dangerous this process should run in isolation. (???)
3. Load both closures into verifier process
4. Check that they match sufficiently:
  - theorem statements of `challenge` as well as all used constants match
  - collect axioms from proof of `challenge` and:
    - make sure no blacklisted ones are contained
    - make sure all used whitelisted ones match between solution and challenge environment
5. Run 1 or more kernels on solution olean:
  - lean4checker
  - nanoda
  - lean4lean
  - ??

isolation command:
landrun --rox / --rox /usr --rw /dev --rox /home/lean/.elan --rox /home/lean/actions-runner/_work --rox /home/lean/.cache/mathlib/ --rw pr-branch/.lake/ --env PATH --env HOME --env GITHUB_OUTPUT -- bash -euxo pipefail {0}


Assumptions:
1. The entire environment and project apart from the content of `Challenge.lean` is controlled by a
   trustworthy party
-/

structure Context where
  projectDir : System.FilePath
  theoremName : Lean.Name
  legalAxioms : Array Lean.Name
  lean4Export : System.FilePath
  landrun : System.FilePath
  lake : System.FilePath

abbrev M := ReaderT Context IO

structure LandrunArgs where
  cmd : String
  args : Array String
  envPass : Array String := #["PATH", "HOME"]
  envOverride : Array (String × Option String) := #[]
  writablePaths : Array System.FilePath

@[inline]
def getTheoremName : M Lean.Name := do return (← read).theoremName

@[inline]
def getLake : M System.FilePath := do return (← read).lake

@[inline]
def getLean4Export : M System.FilePath := do return (← read).lean4Export

@[inline]
def getLandrun : M System.FilePath := do return (← read).landrun

@[inline]
def getProjectDir : M System.FilePath := do return (← read).projectDir

def landrunArgs (writablePaths : Array System.FilePath) (env : Array String) : Array String :=
  -- TODO: temporary best-effort
  let base := #["--best-effort", "--rox", "/", "--rw", "/dev"]
  let base := env.foldl (init := base) (fun acc env => acc ++ #["--env", env])
  writablePaths.foldl (init := base) (fun acc path => acc ++ #["--rwx", path.toString])

def runSandBoxedWithStdout (spawnArgs : LandrunArgs) : M String := do
  let args := landrunArgs spawnArgs.writablePaths spawnArgs.envPass ++ #[spawnArgs.cmd] ++ spawnArgs.args
  let landrun ← getLandrun
  let proc ← IO.Process.spawn {
    cmd := landrun.toString,
    args,
    stdout := .piped,
    env := spawnArgs.envOverride
    cwd := (← getProjectDir)
  }
  let ret ← proc.wait
  if ret != 0 then
    throw <| .userError s!"Child exited with {ret}"
  else
    proc.stdout.readToEnd

def runSandBoxed (spawnArgs : LandrunArgs) : M Unit := do
  let args := landrunArgs spawnArgs.writablePaths spawnArgs.envPass ++ #[spawnArgs.cmd] ++ spawnArgs.args
  let landrun ← getLandrun
  let proc ← IO.Process.spawn {
    cmd := landrun.toString,
    args,
    env := spawnArgs.envOverride
    cwd := (← getProjectDir)
  }
  let ret ← proc.wait
  if ret != 0 then
    throw <| .userError s!"Child exited with {ret}"

def safeLakeBuild (target : Lean.Name) : M Unit := do
  IO.println s!"Building {target}"
  let lake ← getLake
  let dotLakeDir := (← getProjectDir) / ".lake"
  runSandBoxed {
    cmd := lake.toString,
    args := #["build", target.toString (escape := false)],
    envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    writablePaths := #[dotLakeDir]
  }

def safeExport (module : Lean.Name) (decl : Lean.Name) : M String := do
  IO.println s!"Exporting {decl} from {module}"
  let lean4export ← getLean4Export
  runSandBoxedWithStdout {
    cmd := lean4export.toString,
    args := #[module.toString (escape := false), "--", decl.toString (escape := false)]
    envPass := #["PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    writablePaths := #[]
  }

def verifyMatch (challengeExport : String) (solutionExport : String) : M Bool := do
  return true

def runCheckers (solutionExport : String) : M Bool := do
  return true

def compareIt : M Unit := do
  safeLakeBuild `Challenge
  let challengeExport ← safeExport `Challenge (← getTheoremName)
  safeLakeBuild `Solution
  let solutionExport ← safeExport `Solution (← getTheoremName)
  if !(← verifyMatch challengeExport solutionExport) then
    throw <| .userError "Challenge and Solution environment do not match, this is likely a cheater attempt"

  if !(← runCheckers solutionExport) then
    throw <| .userError "Checker failed to verify Solution"

  IO.println "Your solution is okay!"

def M.run (x : M α) (args : List String) : IO α := do
  let cwd ← IO.Process.getCurrentDir
  ReaderT.run x {
    projectDir := cwd
    theoremName := `todo,
    legalAxioms := #[],
    lean4Export := cwd.parent.get! / "lean4export" / ".lake" / "build" / "bin" / "lean4export",
    landrun := cwd.parent.get! / "landrun" / "landrun",
    lake := "lake"
  }

def main (args : List String) : IO Unit :=
  M.run compareIt args
