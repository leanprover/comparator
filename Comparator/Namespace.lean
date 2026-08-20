/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Comparator.Namespace

structure Tools where
  setpriv : String
  unshare : String
  deriving Repr

def configuredTools : IO Tools := do
  return {
    setpriv := (← IO.getEnv "COMPARATOR_SETPRIV").getD "setpriv"
    unshare := (← IO.getEnv "COMPARATOR_UNSHARE").getD "unshare"
  }

private def probeSuccess := "comparator-namespace-probe-ok"

/-- Build the util-linux supervisor invocation used for every sandboxed command. -/
def wrap (tools : Tools) (cmd : String) (args : Array String) : String × Array String :=
  (tools.setpriv, #[
    "--pdeathsig", "SIGKILL",
    tools.unshare,
    "--user", "--map-current-user",
    "--pid", "--fork", "--kill-child=SIGKILL",
    "--mount-proc", "--",
    cmd
  ] ++ args)

/-- Internal child mode used to verify that the namespace has a private procfs and no capabilities. -/
def runProbeChild : IO Unit := do
  let stat ← IO.FS.readFile "/proc/self/stat"
  unless stat.takeWhile (fun c => c != ' ') == "1" do
    throw <| .userError "The namespace probe is not PID 1 in its procfs view"
  let status ← IO.FS.readFile "/proc/self/status"
  unless status.contains "CapEff:\t0000000000000000" do
    throw <| .userError "The namespace probe retained effective capabilities"
  IO.println probeSuccess

private def readSetting (path : System.FilePath) : IO (Option String) :=
  try
    return some (← IO.FS.readFile path).trimAscii.toString
  catch _ =>
    return none

private def explainFailure (problem : String) : IO String := do
  let maxUserNamespaces ← readSetting "/proc/sys/user/max_user_namespaces"
  let unprivilegedClone ← readSetting "/proc/sys/kernel/unprivileged_userns_clone"
  let apparmorRestriction ←
    readSetting "/proc/sys/kernel/apparmor_restrict_unprivileged_userns"

  let problem := problem.trimAscii.toString
  let problem := if problem.isEmpty then "no diagnostic was produced" else problem
  let mut lines := #[s!"Namespace setup failed: {problem}"]
  lines := lines.push
    "Comparator needs util-linux versions of setpriv and unshare with --pdeathsig, --map-current-user, --kill-child, and --mount-proc support. Install or update util-linux if either command or option is missing."
  if maxUserNamespaces == some "0" then
    lines := lines.push
      "user.max_user_namespaces is 0. On a dedicated runner, an administrator can enable it with: sudo sysctl -w user.max_user_namespaces=15000"
  if unprivilegedClone == some "0" then
    lines := lines.push
      "kernel.unprivileged_userns_clone is 0. On a dedicated runner, an administrator can enable it with: sudo sysctl -w kernel.unprivileged_userns_clone=1"
  if apparmorRestriction == some "1" then
    lines := lines.push
      "Ubuntu AppArmor is restricting unprivileged user namespaces. On a disposable CI runner, enable them with: sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0"
  if problem.contains "mount" || problem.contains "proc" then
    lines := lines.push
      "The host or container may forbid mounting a private /proc. Use a runner whose container policy permits unprivileged user, PID, and mount namespaces."
  lines := lines.push
    "These sysctl changes affect the host. Do not apply them blindly on a shared machine; ask its administrator or use a compatible runner."
  return String.intercalate "\n" lines.toList

private def probe (tools : Tools) (comparatorPath cwd : System.FilePath) : IO (Except String Unit) := do
  let (cmd, args) := wrap tools comparatorPath.toString #["--namespace-probe"]
  try
    let { stdout, stderr, exitCode } ← IO.Process.output { cmd, args, cwd := cwd }
    if exitCode == 0 && stdout.trimAscii.toString == probeSuccess then
      return .ok ()
    let output := if stderr.trimAscii.isEmpty then stdout else stderr
    return .error output
  catch e =>
    return .error e.toString

/--
Check namespace support before any workload starts. Returns whether subsequent sandbox invocations
must use the namespace supervisor. Non-strict mode warns once when containment is unavailable.
-/
def select (failClosed : Bool) (tools : Tools) (comparatorPath cwd : System.FilePath) : IO Bool := do
  if !System.Platform.isLinux then
    let details := "Namespace descendant containment is only available on Linux."
    if failClosed then
      throw <| .userError s!"{details}\nfail_closed is enabled; no workload command was started."
    IO.eprintln s!"WARNING: {details}\nContinuing without descendant containment; do not use this \
fallback for untrusted workloads."
    return false

  let result ← probe tools comparatorPath cwd
  match result with
  | .ok () =>
    return true
  | .error problem =>
    let details ← explainFailure problem
    if failClosed then
      throw <| .userError s!"{details}\nfail_closed is enabled; no workload command was started."
    IO.eprintln s!"WARNING: {details}\nContinuing without descendant containment; do not use this fallback for untrusted workloads."
    return false

end Comparator.Namespace
