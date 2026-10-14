import runtests

/-!
Regression tests for the integration runner's temporary-directory lifetime.

Run after compiling `runtests.lean` into the package's Lean search path:

```
lake env lean -o .lake/build/lib/lean/runtests.olean runtests.lean
lake env lean tests/RunnerTempDir.lean
```
-/

namespace RunnerTempDirTests

def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw <| IO.userError message

def withCurrentDir (dir : System.FilePath) (action : IO α) : IO α := do
  let previous ← IO.Process.getCurrentDir
  try
    IO.Process.setCurrentDir dir
    action
  finally
    IO.Process.setCurrentDir previous

def makeProject (fixture : System.FilePath) : IO System.FilePath := do
  let project := fixture / "project"
  IO.FS.createDir project
  IO.FS.writeFile (project / "test.json") "{\"exit_code\": 0}"
  IO.FS.writeFile (project / "copied-marker") fixture.toString
  return project

-- Predict the old runner's two random directory names without touching any
-- directory that already exists. Reset the seed before invoking the runner.
partial def unusedOldPaths (seed : Nat := 0) : IO (Nat × System.FilePath × System.FilePath) := do
  IO.setRandSeed seed
  let first : System.FilePath := "/tmp" / s!"lean_test_{← IO.rand 0 999999}"
  let second : System.FilePath := "/tmp" / s!"lean_test_{← IO.rand 0 999999}"
  if first == second || (← first.pathExists) || (← second.pathExists) then
    unusedOldPaths (seed + 1)
  else
    return (seed, first, second)

def checkRunnerError (result : TestResult) (messagePart : String) : IO Unit := do
  match result with
  | .error _ message =>
    check (message.contains messagePart) s!"Unexpected project setup error: {message}"
  | _ => throw <| IO.userError "Expected the project setup to fail"

-- A missing lean-toolchain fails after the project has been copied. The
-- runner must remove that copy, rather than choosing a new random directory.
def testSetupErrorCleanup : IO Unit := IO.FS.withTempDir fun fixture => do
  let project ← makeProject fixture
  let (seed, first, _) ← unusedOldPaths
  try
    IO.setRandSeed seed
    let result ← withCurrentDir fixture <|
      runTestProject project "setup_error" fixture "/bin/sh"
    checkRunnerError result "lean-toolchain"
    check (!(← first.pathExists)) "Project directory leaked after a setup error"
  finally
    -- On the old implementation the leaked directory contains our marker.
    if (← (first / "copied-marker").pathExists) then
      check ((← IO.FS.readFile (first / "copied-marker")) == fixture.toString)
        "Refusing to clean a directory from another test"
      IO.FS.removeDirAll first

def testSetupErrorPreservesOtherDirectory : IO Unit := IO.FS.withTempDir fun fixture => do
  let project ← makeProject fixture
  let (seed, first, second) ← unusedOldPaths
  IO.FS.createDir second
  IO.FS.writeFile (second / "unrelated-marker") fixture.toString
  try
    IO.setRandSeed seed
    let result ← withCurrentDir fixture <|
      runTestProject project "setup_error" fixture "/bin/sh"
    checkRunnerError result "lean-toolchain"
    check (← (second / "unrelated-marker").pathExists)
      "Error cleanup removed an unrelated directory"
  finally
    if (← (first / "copied-marker").pathExists) then
      check ((← IO.FS.readFile (first / "copied-marker")) == fixture.toString)
        "Refusing to clean a directory from another test"
      IO.FS.removeDirAll first
    if (← second.pathExists) then
      check ((← IO.FS.readFile (second / "unrelated-marker")) == fixture.toString)
        "Refusing to clean a directory from another test"
      IO.FS.removeDirAll second

-- Invalid configuration fails before any temporary directory is allocated.
def testInvalidConfigPreservesOtherDirectory : IO Unit := IO.FS.withTempDir fun fixture => do
  let project ← makeProject fixture
  IO.FS.writeFile (project / "test.json") "invalid JSON"
  let (seed, first, _) ← unusedOldPaths
  IO.FS.createDir first
  IO.FS.writeFile (first / "unrelated-marker") fixture.toString
  try
    IO.setRandSeed seed
    let result ← runTestProject project "invalid_config" fixture "/bin/sh"
    checkRunnerError result "Failed to parse JSON"
    check (← (first / "unrelated-marker").pathExists)
      "Invalid configuration removed an unrelated directory"
  finally
    if (← first.pathExists) then
      check ((← IO.FS.readFile (first / "unrelated-marker")) == fixture.toString)
        "Refusing to clean a directory from another test"
      IO.FS.removeDirAll first

def testExitCleanup (exitCode : Nat) : IO Unit := IO.FS.withTempDir fun fixture => do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let project ← makeProject fixture
  IO.FS.writeFile (fixture / "lean-toolchain") toolchain
  let recordedPath := fixture / "recorded-path"
  -- Run a harmless script through `lake env` in place of comparator. It
  -- records the actual working directory so cleanup is checked for both
  -- successful and unsuccessful child-process exits.
  IO.FS.writeFile (project / "config.json")
    s!"pwd > '{recordedPath}'\nexit {exitCode}\n"
  let result ← withCurrentDir fixture <|
    runTestProject project "exit_cleanup" fixture "/bin/sh"
  match result with
  | .success _ => check (exitCode == 0) "Nonzero exit unexpectedly succeeded"
  | .failure _ expected actual =>
    check (expected == 0 && actual == exitCode) "Unexpected exit-code mismatch"
  | .error _ message => throw <| IO.userError message
  let tempDir : System.FilePath := (← IO.FS.readFile recordedPath).trimAscii.toString
  check (!(← tempDir.pathExists)) "Project directory leaked after a child-process exit"

#eval testSetupErrorCleanup
#eval testSetupErrorPreservesOtherDirectory
#eval testInvalidConfigPreservesOtherDirectory
#eval testExitCleanup 0
#eval testExitCleanup 7

end RunnerTempDirTests
