import Lean

/-!
# Comparator Test Runner

Runs integration tests for the comparator from `tests/projects/`.
Each test project is a directory containing:
- `Challenge.lean` / `Solution.lean`: the Lean source files
- `config.json`: the comparator configuration
- `test.json`: expected exit code, e.g. `{"exit_code": 0}` for a passing test
- (optional) `lakefile.toml`: custom lake configuration; a default is generated if absent

## Usage

```bash
# Run all tests
lean --run runtests.lean

# Run only tests whose name contains "simple" or "def_hole"
lean --run runtests.lean simple def_hole
```
-/

open Lean System.FilePath IO.FS IO.Process System

structure TestConfig where
  exit_code : Nat
  expected_json_output : Option Lean.Json := none
  deriving FromJson, ToJson

inductive TestResult
  | success (projectName : String)
  | failure (projectName : String) (expected : Nat) (actual : Nat)
  | error (projectName : String) (message : String)

def copyFile (src : FilePath) (dst : FilePath) : IO Unit := do
  let contents ← IO.FS.readBinFile src
  IO.FS.writeBinFile dst contents

partial def copyDirContents (src : FilePath) (dst : FilePath) : IO Unit := do
  let entries ← System.FilePath.readDir src
  for entry in entries do
    let srcPath := entry.path
    let relativeName := entry.fileName
    let dstPath := dst / relativeName

    if (← srcPath.isDir) then
      IO.FS.createDirAll dstPath
      copyDirContents srcPath dstPath
    else
      copyFile srcPath dstPath

def createAdditionalFiles (dir : FilePath) : IO Unit := do
  -- Only generate a default lakefile if the test project doesn't provide its own
  if !(← (dir / "lakefile.toml").pathExists) then
    let lakefileContent :=
"
name = \"comparatortest\"
version = \"0.1.0\"

[[lean_lib]]
name = \"Solution\"

[[lean_lib]]
name = \"Challenge\"
"
    IO.FS.writeFile (dir / "lakefile.toml") lakefileContent

def runCommandInDir (dir : FilePath) (cmd : String) (args : Array String) : IO Nat := do
  let output ← IO.Process.spawn {
    cmd := cmd
    args := args
    cwd := some dir
  }
  let exitCode ← output.wait
  pure exitCode.toNat

def readTestConfig (configPath : FilePath) : IO TestConfig := do
  let content ← IO.FS.readFile configPath
  match Lean.Json.parse content with
  | .error e => throw <| IO.userError s!"Failed to parse JSON: {e}"
  | .ok json =>
    match Lean.fromJson? json with
    | .error e => throw <| IO.userError s!"Failed to decode config: {e}"
    | .ok cfg => pure cfg

def getTempDir : IO FilePath := do
  return "/tmp" / s!"lean_test_{← IO.rand 0 999999}"

def runTestProject (projectPath : FilePath) (projectName : String) (testsDir : FilePath)
    (comparatorPath : FilePath) : IO TestResult := do
  try
    let configPath := projectPath / "test.json"
    let config ← readTestConfig configPath

    let tempDir ← getTempDir
    IO.FS.createDirAll tempDir

    copyDirContents projectPath tempDir

    copyFile "lean-toolchain" (tempDir / "lean-toolchain")

    createAdditionalFiles tempDir

    let exitCode ← runCommandInDir tempDir "lake" #["env", comparatorPath.toString, "config.json"]

    let projectConfig := Lean.Json.parse (← IO.FS.readFile (tempDir / "config.json")) |>.toOption.getD .null
    if let .ok jsonOut := projectConfig.getObjValAs? String "json_output_path" then
      let outputJson ← IO.ofExcept <| Lean.Json.parse (← IO.FS.readFile (tempDir / jsonOut))
      if let some expectedJson := config.expected_json_output then
        if outputJson != expectedJson then
          IO.FS.removeDirAll tempDir
          return .error projectName s!"JSON mismatch.\nExpected: {expectedJson}\nGot: {outputJson}"
      else
        IO.FS.removeDirAll tempDir
        return .error projectName s!"Configuration specifies 'json_output_path' but test.json is missing 'expected_json_output'."

    IO.FS.removeDirAll tempDir

    if exitCode == config.exit_code then
      return TestResult.success projectName
    else
      return TestResult.failure projectName config.exit_code exitCode

  catch e =>
    try
      let tempDir ← getTempDir
      if (← tempDir.pathExists) then
        IO.FS.removeDirAll tempDir
    catch _ =>
      pure ()
    return TestResult.error projectName e.toString

def findProjects (testsDir : FilePath) : IO (Array FilePath) := do
  let projectsDir := testsDir / "projects"
  if !(← projectsDir.pathExists) then
    throw <| IO.userError s!"Projects directory not found: {projectsDir}"

  let entries ← System.FilePath.readDir projectsDir
  let mut projects := #[]
  for entry in entries do
    if (← entry.path.isDir) then
      projects := projects.push entry.path
  pure projects

def printTestResult (result : TestResult) : IO Unit := do
  match result with
  | .success name =>
    IO.println s!"✓ {name}: PASSED"
  | .failure name expected actual =>
    IO.println s!"✗ {name}: FAILED (expected exit code {expected}, got {actual})"
  | .error name msg =>
    IO.println s!"✗ {name}: ERROR - {msg}"

/-- Run comparator integration tests. When `args` is non-empty, only tests whose
project name contains one of the given strings (as a substring) are executed. -/
def main (args : List String) : IO UInt32 := do
  let testsDir : FilePath := "tests"
  let filters := args

  IO.println "# Running tests\n"

  let allProjects ← findProjects testsDir

  let projects := if filters.isEmpty then
    allProjects
  else
    allProjects.filter fun p => filters.any (p.fileName.get!.contains ·)

  if projects.isEmpty then
    if filters.isEmpty then
      IO.println "No projects found!"
    else
      IO.println s!"No projects matching {filters} found!"
    return 1

  let comparatorPath ← IO.FS.realPath <| ".lake" / "build" / "bin" / "comparator"

  let mut allPassed := true
  let mut results := #[]
  for projectPath in projects do
    let projectName := projectPath.fileName.get!
    IO.println s!"\n## Running test: {projectName}\n"
    let result ← runTestProject projectPath projectName testsDir comparatorPath
    results := results.push result
    match result with
    | .success _ => pure ()
    | _ => allPassed := false

  IO.println "\n# Summary\n"

  for result in results do
    printTestResult result

  IO.println ""
  if allPassed then
    IO.println "All tests passed!"
    return 0
  else
    IO.println "Some tests failed."
    return 1
