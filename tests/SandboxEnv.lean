import Main

/-!
Exercise the environment passed by `safeLakeBuild` and `safeExport`. The launcher below models
Landrun's `--env` filtering, but does not provide any filesystem or process isolation. It runs only
the trusted probes created by this test.

Run with `LEAN_NUM_THREADS=1`, `LEAN_NUM_THREADS=3`, and with the variable unset. Put this project's
build directory first so `import Main` does not resolve to lean4export's module of the same name:

```
lake env bash -c '
  export LEAN_PATH="$PWD/.lake/build/lib/lean:$LEAN_PATH"
  LEAN_NUM_THREADS=1 lean tests/SandboxEnv.lean
  LEAN_NUM_THREADS=3 lean tests/SandboxEnv.lean
  env -u LEAN_NUM_THREADS lean tests/SandboxEnv.lean
'
```
-/

namespace SandboxEnvTests

def writeExecutable (path : System.FilePath) (contents : String) : IO Unit := do
  IO.FS.writeFile path contents
  IO.setAccessRights path {
    user := { read := true, write := true, execution := true }
  }

def launcher : String := r#"#!/bin/bash
set -euo pipefail
env_args=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --env)
      # Like Landrun's processEnvironmentVars, omit a key that is not set.
      if value=$(/usr/bin/printenv "$2"); then
        env_args+=("$2=$value")
      fi
      shift 2
      ;;
    --ro|--rw|--rox|--rwx) shift 2 ;;
    --) shift; break ;;
    --best-effort|-ldd|-add-exec) shift ;;
    *) echo "Unexpected launcher argument: $1" >&2; exit 1 ;;
  esac
done
# The build path requests `lake` by name; replace it with this test's trusted probe.
if [[ $1 == lake ]]; then
  shift
  set -- "${0%/*}/lake" "$@"
fi
exec /usr/bin/env -i "${env_args[@]}" "$@"
"#

def probe : String := r#"#!/bin/sh
set -eu
test "${LEAN_ABORT_ON_PANIC-}" = 1
if test "${LEAN_NUM_THREADS+x}" = x; then
  printf 'set:%s' "$LEAN_NUM_THREADS"
else
  printf unset
fi
"#

def run : IO Unit := IO.FS.withTempDir fun dir => do
  writeExecutable (dir / "landrun") launcher
  writeExecutable (dir / "lake") <|
    "#!/bin/sh\nset -eu\ntest \"$#\" = 2\ntest \"$1\" = build\ntest \"$2\" = Challenge\n" ++
    "exec \"${0%/*}/probe\" > .lake/build-env\n"
  writeExecutable (dir / "lean4export") <|
    "#!/bin/sh\nset -eu\ntest \"$#\" = 3\ntest \"$1\" = Challenge\n" ++
    "test \"$2\" = --\ntest \"$3\" = proof\nexec \"${0%/*}/probe\"\n"
  writeExecutable (dir / "probe") probe

  let context : Comparator.Context := {
    projectDir := dir
    challengeModule := `Challenge
    solutionModule := `Solution
    theoremNames := #[`proof]
    definitionNames := #[]
    legalAxioms := #[]
    leanPrefix := dir
    gitLocation := dir / "git"
    whichLandrun := (dir / "landrun").toString
    whichLean4Export := (dir / "lean4export").toString
    externalKernels := {}
  }
  let expected := (← IO.getEnv "LEAN_NUM_THREADS").map ("set:" ++ ·) |>.getD "unset"
  ReaderT.run (Comparator.safeLakeBuild `Challenge) context
  let buildEnv ← IO.FS.readFile (dir / ".lake" / "build-env")
  let exportEnv ← ReaderT.run (Comparator.safeExport `Challenge #[`proof]) context
  let mut failures : Array String := #[]
  for (stage, actual) in #[ ("build", buildEnv), ("export", exportEnv) ] do
    if actual != expected then
      failures := failures.push s!"{stage}: expected {expected}, got {actual}"
  unless failures.isEmpty do
    throw <| IO.userError ("LEAN_NUM_THREADS was not preserved: " ++
      String.intercalate "; " failures.toList)
  IO.println s!"Build and export preserved LEAN_NUM_THREADS ({expected})."

end SandboxEnvTests

#eval SandboxEnvTests.run
