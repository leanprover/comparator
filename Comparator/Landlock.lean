/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Comparator.Landlock

/-- The Landrun policy shared by Comparator workloads and the enforcement probe. -/
def baseArgs : Array String :=
  #["--best-effort", "--ro", "/", "--rw", "/dev", "-ldd", "-add-exec"]

private def probeContents := "comparator-landlock-enforcement-probe"
private def replacementContents := "landlock-did-not-deny-this-write"
private def probeSuccess := "comparator-landlock-enforcement-ok"
private def permissionDenied : UInt32 := 13

/--
Internal child mode for the end-to-end Landrun probe. The probe file is writable by the user but
must be read-only under Comparator's Landrun policy.
-/
def runProbeChild (path : System.FilePath) : IO Unit := do
  let contents ← IO.FS.readFile path
  unless contents == probeContents do
    throw <| .userError "The Landlock enforcement probe could not read its input file"

  let writeWasDenied ←
    try
      IO.FS.writeFile path replacementContents
      pure false
    catch e =>
      match e with
      | .permissionDenied _ code _ =>
        if code == permissionDenied then
          pure true
        else
          throw e
      | _ =>
        throw e

  unless writeWasDenied do
    throw <| .userError "The Landlock enforcement probe unexpectedly wrote its read-only file"
  unless (← IO.FS.readFile path) == probeContents do
    throw <| .userError "The Landlock enforcement probe file was modified"
  IO.println probeSuccess

private def failureMessage (details : String) : String :=
  let details := details.trimAscii.toString
  let details := if details.isEmpty then "no diagnostic was produced" else details
  s!"The installed Landrun did not enforce Comparator's read-only filesystem policy ({details}); \
fail_closed is enabled, so no workload command was started"

/--
Run the installed Landrun around a child Comparator process and verify that Comparator's policy
denies a write to a file which is writable outside the sandbox. This detects unavailable or disabled
Landlock and an accidentally configured no-op Landrun shim before any workload command starts.
-/
def requireEnforcement (landrunPath : String) (comparatorPath cwd : System.FilePath) : IO Unit :=
  try
    IO.FS.withTempFile fun handle probePath => do
      let probePathString := probePath.toString
      if System.Platform.isLinux &&
          (probePathString == "/dev" || probePathString.startsWith "/dev/") then
        let message :=
          s!"The Landlock enforcement probe cannot use {probePath} because Comparator's policy \
makes /dev writable. Set TMPDIR to a directory outside /dev; fail_closed is enabled, so no \
workload command was started"
        throw <| .userError message
      handle.putStr probeContents
      handle.flush
      let { stdout, stderr, exitCode } ← IO.Process.output {
        cmd := landrunPath
        args := baseArgs ++ #[
          "--", comparatorPath.toString, "--landlock-enforcement-probe", probePath.toString
        ]
        cwd := cwd
      }
      let contents ← IO.FS.readFile probePath
      unless exitCode == 0 && stdout.trimAscii.toString == probeSuccess &&
          contents == probeContents do
        throw <| .userError (failureMessage stderr)
  catch e =>
    if e.toString.contains "fail_closed is enabled" then
      throw e
    throw <| .userError (failureMessage e.toString)

end Comparator.Landlock
