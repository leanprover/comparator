import Lean

private def waitForStart (path : System.FilePath) : Nat → IO Unit
  | 0 => throw <| .userError "descendant did not start within 30 seconds"
  | remaining + 1 => do
    if ← path.pathExists then
      return
    IO.sleep 10
    waitForStart path remaining

theorem cleanupTest : True := by
  run_tac
    let childSource :=
      "def waitForRelease : Nat → IO Unit\n  | 0 => pure ()\n  | remaining + 1 => do\n    if ← System.FilePath.pathExists \".lake/release-descendant\" then\n      IO.FS.writeFile \".lake/descendant-survived\" \"\"\n    else\n      IO.sleep 10\n      waitForRelease remaining\n\ndef main : IO Unit := do\n  IO.FS.writeFile \".lake/descendant-started\" \"\"\n  waitForRelease 6000\n"
    let childPath : System.FilePath := ".lake" / "detached_child.lean"
    let startedPath : System.FilePath := ".lake" / "descendant-started"
    IO.FS.writeFile childPath childSource
    discard <| IO.Process.spawn {
      cmd := "lean"
      args := #["--run", childPath.toString]
      stdin := .null
      stdout := .null
      stderr := .null
      setsid := true
    }
    waitForStart startedPath 3000
  trivial
