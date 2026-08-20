import Comparator.Namespace

open System

def wrapperIsExact : Bool :=
  Comparator.Namespace.wrap
      { setpriv := "setpriv-test", unshare := "unshare-test" }
      "landrun-test" #["landrun-arg"] ==
    ("setpriv-test", #[
      "--pdeathsig", "SIGKILL", "unshare-test",
      "--user", "--map-current-user",
      "--pid", "--fork", "--kill-child=SIGKILL",
      "--mount-proc", "--", "landrun-test", "landrun-arg"
    ])

def main (args : List String) : IO UInt32 := do
  unless wrapperIsExact do
    throw <| .userError "the namespace supervisor invocation changed unexpectedly"
  let some (comparatorPath : String) := args[0]?
    | throw <| .userError "expected the Comparator executable path"
  let cwd ← IO.Process.getCurrentDir
  let unavailableTools : Comparator.Namespace.Tools := { setpriv := "false", unshare := "false" }
  if ← Comparator.Namespace.select false unavailableTools comparatorPath cwd then
    throw <| .userError "non-strict namespace selection did not fall back"
  let strictRejected ←
    try
      discard <| Comparator.Namespace.select true unavailableTools comparatorPath cwd
      pure false
    catch e =>
      pure <| e.toString.contains "no workload command was started"
  unless strictRejected do
    throw <| .userError "strict namespace selection did not fail informatively"
  return 0
