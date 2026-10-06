import Comparator.Landlock

open System

def main (args : List String) : IO UInt32 := do
  let some (comparatorPath : String) := args[0]?
    | throw <| .userError "expected the Comparator executable path"
  let cwd ← IO.Process.getCurrentDir
  let fakeLandrun ← IO.FS.realPath <| "scripts" / "fake-landrun.sh"
  let rejected ←
    try
      Comparator.Landlock.requireEnforcement fakeLandrun.toString comparatorPath cwd
      pure false
    catch _ =>
      pure true
  unless rejected do
    throw <| .userError "the insecure Landrun shim passed the enforcement probe"
  return 0
