/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean
import Comparator
import Lean4Checker.Replay
import Export.Parse

namespace Comparator

structure Context where
  projectDir : System.FilePath
  challengeModule : Lean.Name
  solutionModule : Lean.Name
  theoremNames : Array Lean.Name
  definitionNames : Array Lean.Name
  legalAxioms : Array Lean.Name
  leanPrefix : System.FilePath
  gitLocation : System.FilePath
  enableNanoda : Bool
  whichLandrun : String
  whichLean4Export : String
  whichNanoda : String
  jsonOutputPath : Option String

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
def getDefinitionNames : M (Array Lean.Name) := do return (← read).definitionNames

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

@[inline]
def getNanodaEnabled : M Bool := do return (← read).enableNanoda

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

def buildLandrunArgs (spawnArgs : LandrunArgs) : Array String :=
  let args := #["--best-effort", "--ro", "/", "--rw", "/dev", "-ldd", "-add-exec"]
  let args := spawnArgs.envPass.foldl (init := args) (fun acc env => acc ++ #["--env", env])
  let args := spawnArgs.readablePaths.foldl (init := args) (fun acc path => acc ++ #["--ro", path.toString])
  let args := spawnArgs.writablePaths.foldl (init := args) (fun acc path => acc ++ #["--rwx", path.toString])
  let args := spawnArgs.executablePaths.foldl (init := args) (fun acc path => acc ++ #["--rox", path.toString])
  args ++ #[spawnArgs.cmd] ++ spawnArgs.args

def runSandBoxedWithStdout (spawnArgs : LandrunArgs) : M String := do
  let args := buildLandrunArgs spawnArgs
  let { stdout, stderr, exitCode } ← IO.Process.output {
    cmd := (← read).whichLandrun,
    args,
    env := spawnArgs.envOverride
    cwd := (← getProjectDir)
  }
  IO.eprint stderr
  if exitCode != 0 then
    throw <| .userError s!"Child exited with {exitCode}"
  return stdout


def runSandBoxed (spawnArgs : LandrunArgs) : M Unit := do
  let args := buildLandrunArgs spawnArgs
  let proc ← IO.Process.spawn {
    cmd := (← read).whichLandrun,
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

  if !(← System.FilePath.pathExists dotLakeDir) then
    IO.FS.createDir dotLakeDir

  runSandBoxed {
    cmd := "lake",
    args := #["build", target.toString],
    envPass := #["PATH", "HOME", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir]
    writablePaths := #[dotLakeDir]
    executablePaths := #[leanPrefix, gitLocation]
  }

def safeExport (module : Lean.Name) (decls : Array Lean.Name) : M String := do
  IO.println s!"Exporting {decls} from {module}"
  let baseArgs := #[module.toString, "--"]
  let args := decls.foldl (·.push <| ·.toString) baseArgs

  let leanPrefix ← getLeanPrefix
  let projectDir ← getProjectDir
  let dotLakeDir := projectDir / ".lake"
  runSandBoxedWithStdout {
    cmd := (← read).whichLean4Export
    args := args,
    envPass := #["PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"]
    envOverride := #[("LEAN_ABORT_ON_PANIC", some "1")]
    readablePaths := #[projectDir, dotLakeDir]
    writablePaths := #[]
    executablePaths := #[leanPrefix]
  }

def runNanoda (solutionExport : String) : M Unit := do
  IO.println "Running nanoda kernel on solution"
  IO.FS.withTempFile fun config configPath => do
    let legalAxioms ← getLegalAxioms
    config.putStr <| Lean.Json.compress <| Lean.Json.mkObj [
      ("use_stdin", true),
      ("permitted_axioms", .arr <| legalAxioms.map (.str ∘ Lean.Name.toString)),
      ("unpermitted_axiom_hard_error", true),
      ("nat_extension", true),
      ("string_extension", true),
    ]
    config.flush

    let spawnArgs := {
      cmd := (← read).whichNanoda
      args := #[configPath.toString],
      envPass := #[]
      readablePaths := #[configPath.toString]
      writablePaths := #[]
      executablePaths := #[]
    }

    let args := buildLandrunArgs spawnArgs
    let proc ← IO.Process.spawn {
      cmd := (← read).whichLandrun,
      args,
      stdin := .piped
      env := spawnArgs.envOverride
      cwd := (← getProjectDir)
    }

    let (nanodaStdin, proc) ← proc.takeStdin
    nanodaStdin.putStr solutionExport
    nanodaStdin.flush
    let ret ← proc.wait
    if ret != 0 then
      throw <| .userError s!"Child exited with {ret}"

    IO.println "Nanoda kernel accepts the solution"

def runKernel (solution : Export.ExportedEnv) : M Unit := do
  IO.println "Running Lean default kernel on solution."
  let mut env ← Lean.mkEmptyEnvironment
  let mut constMap := solution.constMap
  -- Lean's kernel interprets just the addition of `Quot as adding all of these so adding them
  -- multiple times leads to errors.
  constMap := constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  discard <| env.replay' constMap
  IO.println "Lean default kernel accepts the solution"

def primitiveTargets : M (Array Lean.Name) := do
  -- The challenge needs to have all the built-in constants of the kernel, as the
  -- kernel makes no guarantees when fed other definitions here.
  -- List from `git grep new_persistent_expr_const src/kernel/`
  return #[
    -- ``Nat.zero,
    -- ``Nat.succ,
    ``Nat.add,
    ``Nat.sub,
    ``Nat.mul,
    ``Nat.pow,
    ``Nat.gcd,
    ``Nat.div,
    ``Nat.mod,
    ``Nat.beq,
    ``Nat.ble,
    ``Nat.land,
    ``Nat.lor,
    ``Nat.xor,
    ``Nat.shiftLeft,
    ``Nat.shiftRight,
    ``String.ofList,
  ]

def builtinTargets : M (Array Lean.Name) := do
  if ← getNanodaEnabled then
    -- TODO: fix when nanoda fixes its string handling
    let mut additional := #[``Nat, ``String, ``String.mk, ``Char, ``Char.ofNat, ``List]
    if (← getLegalAxioms).contains ``Quot.sound then
      additional := additional ++ #[``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
    return additional
  else
    return #[]

def stringStream (s : String) : BaseIO IO.FS.Stream := do
  let ref ← IO.mkRef {
    data := s.toByteArray
  }
  return IO.FS.Stream.ofBuffer ref

@[inline]
def getJsonOutputPath : M (Option String) := do return (← read).jsonOutputPath

partial def getAxioms (env : Export.ExportedEnv) (n : Lean.Name) : Array Lean.Name :=
  let rec collect (n : Lean.Name) : StateM (Std.HashSet Lean.Name) Unit := do
    if !(← get).contains n then
      modify (·.insert n)
      if let some info := env.constMap[n]? then Comparator.runForUsedConsts info collect
  let (_, deps) := (collect n).run {}
  deps.toArray.filter fun dep => match env.constMap[dep]? with | some (.axiomInfo _) => true | _ => false

structure VerificationOutcome where
  target : Lean.Name
  targetKind : String
  failureCategory : Option String
  failureMessage : Option String
  unpermittedAxioms : Array Lean.Name
  transitiveAxioms : Array Lean.Name
  deriving Lean.ToJson

structure VerifyResult where
  outcomes : Array VerificationOutcome
  kernelAccepted : Option Bool := none
  kernelFailureMessage : Option String := none
  nanodaAccepted : Option Bool := none
  nanodaFailureMessage : Option String := none
  deriving Lean.ToJson

def outcome (sol : Export.ExportedEnv) (target : Lean.Name) (kind : String) (legal : Array Lean.Name)
    (cat msg : Option String := none) : VerificationOutcome :=
  let transitiveAxioms := getAxioms sol target
  let unpermittedAxioms := transitiveAxioms.filter (!legal.contains ·)
  { target, targetKind := kind, failureCategory := cat, failureMessage := msg, unpermittedAxioms, transitiveAxioms }

def writeReport (report : VerifyResult) : M Unit := do
  if let some p ← getJsonOutputPath then IO.FS.writeFile p (Lean.Json.compress <| Lean.toJson report)

def throwFailures (header : String) (failures : Array (Lean.Name × String)) : M α :=
  throw <| .userError <| failures.foldl (fun acc (n, f) => acc ++ s!"- {n}: {f}\n") header

def verifyMatch (challengeExport : String) (solutionExport : String) : M VerifyResult := do
  let challenge ← Export.parseStream (← stringStream challengeExport)
  let solution ← Export.parseStream (← stringStream solutionExport)
  let theoremNames ← getTheoremNames; let definitionNames ← getDefinitionNames; let legalAxioms ← getLegalAxioms

  if let .error e := Comparator.compareAt challenge solution legalAxioms #[] (← primitiveTargets) then
    let outcomes := theoremNames.map (outcome solution · "theorem" legalAxioms (some "global_precheck") (some e)) ++
                    definitionNames.map (outcome solution · "definition" legalAxioms (some "global_precheck") (some e))
    writeReport { outcomes }; throw <| .userError e

  let check (kind : String) (name : Lean.Name) : M VerificationOutcome := do
    let (t, d) := if kind == "theorem" then (#[name], definitionNames) else (#[], #[name])
    let (fail, cat) := match Comparator.compareAt challenge solution t d #[] with
      | .error e => (some e, some "comparison")
      | .ok () => match Comparator.checkAxioms solution t d legalAxioms with
        | .error e => (some e, some "axioms")
        | .ok () => (none, none)
    return outcome solution name kind legalAxioms cat fail

  let outcomes := (← theoremNames.mapM (check "theorem")) ++ (← definitionNames.mapM (check "definition"))
  let result := { outcomes }
  writeReport result

  let fails := outcomes.filter (·.failureCategory.isSome)
  if !fails.isEmpty then
    let defFails := fails.filter (·.targetKind == "definition") |>.map fun o => (o.target, o.failureMessage.get!)
    let thmFails := fails.filter (·.targetKind == "theorem") |>.map fun o => (o.target, o.failureMessage.get!)
    if !defFails.isEmpty then throwFailures "Some definition targets failed:\n" defFails
    if !thmFails.isEmpty then throwFailures "Some theorem targets failed:\n" thmFails
  return result

def compareIt : M Unit := do
  let exportTargets := (← builtinTargets) ++ (← getTheoremNames) ++ (← getLegalAxioms) ++ (← primitiveTargets) ++ (← getDefinitionNames)
  safeLakeBuild (← getChallengeModule)
  let challengeExport ← safeExport (← getChallengeModule) exportTargets
  safeLakeBuild (← getSolutionModule)
  let solutionExport ← safeExport (← getSolutionModule) exportTargets

  let mut result ← verifyMatch challengeExport solutionExport
  let mut errs := #[]
  let runCheck (run : M Unit) (update : VerifyResult → Bool → Option String → VerifyResult) (r : VerifyResult) (errs : Array IO.Error) : M (VerifyResult × Array IO.Error) := do
    try run; return (update r true none, errs)
    catch e => return (update r false (some e.toString), errs.push e)

  if ← getNanodaEnabled then
    (result, errs) ← runCheck (runNanoda solutionExport) (fun r acc msg => { r with nanodaAccepted := some acc, nanodaFailureMessage := msg }) result errs

  let runK := do runKernel (← Export.parseStream (← stringStream solutionExport))
  (result, errs) ← runCheck runK (fun r acc msg => { r with kernelAccepted := some acc, kernelFailureMessage := msg }) result errs

  writeReport result
  if !errs.isEmpty then throw errs[0]!

  IO.println "Your solution is okay!"

structure Config where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  definition_names : Option (Array String) := none
  permitted_axioms : Array String
  enable_nanoda : Bool
  json_output_path : Option String := none
  deriving Lean.FromJson, Lean.ToJson, Repr

def M.run (x : M α) (cfg : Config) : IO α := do
  let cwd ← IO.Process.getCurrentDir
  let leanPrefix ← queryLeanPrefix cwd
  let gitLocation ← queryGitLocation
  let whichLean4Export := (← IO.getEnv "COMPARATOR_LEAN4EXPORT").getD "lean4export"
  let whichLandrun := (← IO.getEnv "COMPARATOR_LANDRUN").getD "landrun"
  let whichNanoda := (← IO.getEnv "COMPARATOR_NANODA").getD "nanoda_bin"
  ReaderT.run x {
    projectDir := cwd
    challengeModule := cfg.challenge_module.toName,
    solutionModule := cfg.solution_module.toName,
    theoremNames := cfg.theorem_names.map String.toName,
    definitionNames := cfg.definition_names.getD #[] |>.map String.toName,
    legalAxioms := cfg.permitted_axioms.map String.toName,
    leanPrefix := leanPrefix,
    gitLocation := gitLocation,
    enableNanoda := cfg.enable_nanoda,
    whichLean4Export,
    whichLandrun,
    whichNanoda,
    jsonOutputPath := cfg.json_output_path
  }

end Comparator

def main (args : List String) : IO Unit := do
  let some (configPath : String) := args[0]?
    | throw <| .userError "Expected config file path as first argument."
  let content ← IO.FS.readFile configPath
  let config ← IO.ofExcept <| Lean.FromJson.fromJson? <| ← IO.ofExcept <| Lean.Json.parse content
  Comparator.M.run Comparator.compareIt config
