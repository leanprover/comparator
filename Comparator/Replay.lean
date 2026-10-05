/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.CoreM
import Lean.AddDecl
import Lean.Util.FoldConsts

/-!
This file is a copy of `src/Lean/Replay.lean` from Lean v4.35.0-rc3, renamed to
`Lean.Kernel.Environment.replayParallel` (namespace `ParallelReplay`) so that it does not clash with
Lean's own `replay`. The only change in behavior: theorems are added to the environment with
`addDeclWithoutChecking`, and each theorem is checked by the kernel (`addDeclCore`) in a separate task
against the environment as it was just before that theorem; `replayParallel` waits for all of these
tasks and fails if any of them failed. Every declaration is therefore checked by the same kernel call
against the same environment as in `replay`; only the order in which theorems are checked differs.
-/

/-!
# `Lean.Kernel.Environment.replayParallel` (based on `Lean.Kernel.Environment.replay`)

`replayParallel env constantMap` will "replay" all the constants in `constantMap : HashMap Name ConstantInfo` into `env`,
sending each declaration to the kernel for checking.

`replayParallel` does not send constructors or recursors in `constantMap` to the kernel,
but rather checks that they are identical to constructors or recursors generated in the environment
after replaying any inductive definitions occurring in `constantMap`.

`replayParallel` can be used either as:
* a verifier for a `Kernel.Environment`, by sending everything to the kernel, or
* a mechanism to safely transfer constants from one `Kernel.Environment` to another.

-/

namespace Lean.Kernel.Environment

namespace ParallelReplay

structure Context where
  newConstants : Std.HashMap Name ConstantInfo

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  /-- Kernel checks of theorems, running in parallel; see `addThmAsync`. -/
  tasks : Array (Name × Task (Except Kernel.Exception Kernel.Environment)) := #[]

abbrev M := ReaderT Context <| StateRefT State IO

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Use the current `Environment` to throw a `Kernel.Exception`. -/
def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

/-- Add a declaration, possibly throwing a `Kernel.Exception`. -/
def addDecl (d : Declaration) : M Unit := do
  match (← get).env.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok env => modify fun s => { s with env := env }
  | .error ex => throwKernelException ex

/--
Add a theorem to the environment without checking it, and spawn a task that checks it with the kernel
against the environment as it was before the theorem was added.
-/
def addThmAsync (info : TheoremVal) : M Unit := do
  let kenv := (← get).env
  let decl := Declaration.thmDecl info
  match kenv.addDeclWithoutChecking decl with
  | .ok env =>
    let t := Task.spawn fun () => kenv.addDeclCore 0 0 decl (cancelTk? := none)
    modify fun s => { s with env := env, tasks := s.tasks.push (info.name, t) }
  | .error ex => throwKernelException ex

mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      try
        match ci with
        | .defnInfo   info =>
          addDecl (Declaration.defnDecl   info)
        | .thmInfo    info =>
          -- Ignore duplicate theorems. This code is identical to that in `finalizeImport` before it
          -- added extended duplicates support for the module system, which is not relevant for us
          -- here as we always load all .olean information. We need this case *because* of the module
          -- system -- as we have more data loaded than it, we might encounter duplicate private
          -- theorems where elaboration under the module system would have only one of them in scope.
          if let some (.thmInfo info') := (← get).env.find? ci.name then
            if info.name == info'.name &&
              info.type == info'.type &&
              info.levelParams == info'.levelParams &&
              info.all == info'.all
            then
              return
          addThmAsync info
        | .axiomInfo  info =>
          addDecl (Declaration.axiomDecl  info)
        | .opaqueInfo info =>
          addDecl (Declaration.opaqueDecl info)
        | .inductInfo info =>
          let lparams := info.levelParams
          let nparams := info.numParams
          let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
              pure ((← read).newConstants[n]!))
          -- Make sure we are really finished with the constructors.
          for (_, ctors) in ctorInfo do
            for ctor in ctors do
              replayConstants ctor.getUsedConstantsAsSet
          let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
            { name := ci.name
              type := ci.type
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          addDecl (Declaration.inductDecl lparams nparams types false)
        -- We postpone checking constructors,
        -- and at the end make sure they are identical
        -- to the constructors generated when we replay the inductives.
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        -- Similarly we postpone checking recursors.
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          -- `Quot.lift` and `Quot.ind` have types that reference `Eq`,
          -- so we need to ensure `Eq` is replayed before adding the quotient declaration.
          replayConstant `Eq
          addDecl (Declaration.quotDecl)
        modify fun s => { s with pending := s.pending.erase name }
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n

end

/--
Check that all postponed constructors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

end ParallelReplay

open ParallelReplay

/--
"Replay" some constants into a `Kernel.Environment`, sending them to the kernel for checking.

Throws a `IO.userError` if the kernel rejects a constant,
or if there are malformed recursors or constructors for inductive types.

Theorems are checked in parallel tasks; non-theorem declarations are checked in order, as in `replay`.
-/
def replayParallel (newConstants : Std.HashMap Name ConstantInfo) (env : Kernel.Environment) :
    IO Kernel.Environment := do
  let mut remaining : NameSet := ∅
  for (n, ci) in newConstants.toList do
    -- We skip unsafe constants, and also partial constants.
    -- Later we may want to handle partial constants.
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := { newConstants }) do
      for n in remaining do
        replayConstant n
      -- Wait for the kernel checks of all theorems.
      for (name, t) in (← get).tasks do
        if let .error ex := t.get then
          try ParallelReplay.throwKernelException ex
          catch ex => throw <| .userError s!"while replaying declaration '{name}':\n{ex}"
      checkPostponedConstructors
      checkPostponedRecursors
  return s.env

end Kernel.Environment
