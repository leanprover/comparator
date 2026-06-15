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

abbrev DepM := StateM (Std.HashSet Lean.Name)

partial def collectDeps (env : Export.ExportedEnv) (n : Lean.Name) : DepM Unit := do
  if (← get).contains n then
    return
  modify (·.insert n)
  if let some info := env.constMap[n]? then
    Comparator.runForUsedConsts info (collectDeps env)

def getAxioms (env : Export.ExportedEnv) (n : Lean.Name) : Array Lean.Name := Id.run do
  let (_, deps) := (collectDeps env n).run {}
  return deps.toArray.filter fun dep => match env.constMap[dep]? with
    | some (.axiomInfo _) => true
    | _ => false

structure VerificationOutcome where
  target : Lean.Name
  targetKind : String
  origin : String := "configured"
  mode : Option String
  actualName : Option Lean.Name
  accepted : Bool
  failureCategory : Option String
  transitiveAxioms : Array Lean.Name
  deriving Lean.ToJson

structure VerifyResult where
  acceptedTheorems : Array Lean.Name
  outcomes : Array VerificationOutcome
  deriving Lean.ToJson

def outcome (solution : Export.ExportedEnv) (target : Lean.Name) (targetKind : String)
    (mode : Option String) (accepted : Bool) (failureCategory : Option String := none) :
    VerificationOutcome :=
  { target, targetKind, mode, accepted, failureCategory
    actualName := if accepted then some target else none
    transitiveAxioms := getAxioms solution target }

def writeReport (result : VerifyResult) : M Unit := do
  if let some path ← getJsonOutputPath then
    IO.FS.writeFile path (Lean.Json.compress <| Lean.toJson result)

def throwFailures (header : String) (failures : Array (Lean.Name × String)) : M α := do
  let mut msg := header
  for (name, failure) in failures do
    msg := msg ++ s!"- {name}: {failure}\n"
  throw <| .userError msg

def verifyMatch (challengeExport : String) (solutionExport : String) :
    M VerifyResult := do
  let challenge ← Export.parseStream (← stringStream challengeExport)
  let solution ← Export.parseStream (← stringStream solutionExport)
  let theoremNames ← getTheoremNames
  let definitionNames ← getDefinitionNames
  let legalAxioms ← getLegalAxioms

  if let .error e := Comparator.compareAt challenge solution legalAxioms #[] (← primitiveTargets) then
    let outcomes :=
      theoremNames.map (outcome solution · "theorem" (some "direct") false (some "global_precheck")) ++
      definitionNames.map (outcome solution · "definition" none false (some "global_precheck"))
    writeReport { acceptedTheorems := #[], outcomes }
    throw <| .userError e

  let mut theoremFailures := #[]
  let mut outcomes := #[]
  for theoremName in theoremNames do
    let (failure, category) ← match Comparator.compareAt challenge solution #[theoremName] definitionNames #[] with
    | .error e => pure (some e, some "comparison")
    | .ok () =>
      match Comparator.checkAxioms solution #[theoremName] #[] legalAxioms with
      | .error e => pure (some e, some "axioms")
      | .ok () => pure (none, none)
    outcomes := outcomes.push <| outcome solution theoremName "theorem" (some "direct")
      failure.isNone category
    if let some e := failure then
      theoremFailures := theoremFailures.push (theoremName, e)

  let mut definitionFailures := #[]
  for definitionName in definitionNames do
    let (failure, category) ← match Comparator.compareAt challenge solution #[] #[definitionName] #[] with
    | .error e => pure (some e, some "comparison")
    | .ok () =>
      match Comparator.checkAxioms solution #[] #[definitionName] legalAxioms with
      | .error e => pure (some e, some "axioms")
      | .ok () => pure (none, none)
    outcomes := outcomes.push <| outcome solution definitionName "definition" none
      failure.isNone category
    if let some e := failure then
      definitionFailures := definitionFailures.push (definitionName, e)

  let result := { acceptedTheorems := theoremNames, outcomes }
  writeReport result

  if !definitionFailures.isEmpty then
    throwFailures "Some definition targets failed:\n" definitionFailures
  if !theoremFailures.isEmpty then
    throwFailures "Some theorem targets failed:\n" theoremFailures

  return result

def getTargets (theorems definitions : Array Lean.Name) : M (Array Lean.Name) := do
  return (← builtinTargets) ++ theorems ++ (← getLegalAxioms) ++ (← primitiveTargets) ++ definitions

def compareIt : M Unit := do
  let theoremNames ← getTheoremNames
  let definitionNames ← getDefinitionNames

  let challengeModule ← getChallengeModule
  safeLakeBuild challengeModule
  let challengeExport ← safeExport challengeModule (← getTargets theoremNames definitionNames)

  let solutionModule ← getSolutionModule
  safeLakeBuild solutionModule
  let solutionExport ← safeExport solutionModule (← getTargets theoremNames definitionNames)

  let result ← verifyMatch challengeExport solutionExport
  let verifiedSolutionExport ← safeExport solutionModule (← getTargets result.acceptedTheorems definitionNames)

  if ← getNanodaEnabled then
    runNanoda verifiedSolutionExport

  let verifiedSolution ← Export.parseStream (← stringStream verifiedSolutionExport)
  runKernel verifiedSolution

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
