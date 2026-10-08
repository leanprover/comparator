/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.AddDecl
import all Lean.Replay
import Lean.Util.FoldConsts

/-!
# `Lean.Kernel.Environment.replayParallel`

`replayParallel` is `Lean.Kernel.Environment.replay` (from `Lean.Replay`) with one change: theorems are
added to the environment with `addDeclWithoutChecking`, and each theorem is checked by the kernel
(`addDeclCore`) in a separate task against the environment as it was just before that theorem.
`replayParallel` waits for all of these tasks, and fails if any of them failed, before the postponed
constructor and recursor checks. Every declaration is therefore checked by the same kernel call against
the same environment as in `replay`; only the order in which theorems are checked differs.

Everything else is reused from `Lean.Replay`: `Context`, `State`, `M`, `isTodo`, `throwKernelException`,
`addDecl` and the postponed constructor and recursor checks. They are not public there, hence
`import all Lean.Replay`. The only code copied from `Lean.Replay` (Lean v4.35.0-rc3) is `replayConstant`,
whose `.thmInfo` case is the one change, and the loop in `replayParallel`.
-/

namespace Lean.Kernel.Environment

namespace ParallelReplay

/-- State added on top of `Replay.M`: the kernel checks of theorems, running in parallel. -/
structure ExtraState where
  /-- Kernel checks of theorems, running in parallel; see `addThmAsync`. -/
  tasks : Array (Name × Task (Except Kernel.Exception Kernel.Environment)) := #[]

abbrev M := StateRefT ExtraState Replay.M

/--
Add a theorem to the environment without checking it, and spawn a task that checks it with the kernel
against the environment as it was before the theorem was added.
-/
def addThmAsync (info : TheoremVal) : M Unit := do
  let kenv := (← getThe Replay.State).env
  let decl := Declaration.thmDecl info
  match kenv.addDeclWithoutChecking decl with
  | .ok env =>
    let t := Task.spawn fun () => kenv.addDeclCore 0 0 decl (cancelTk? := none)
    modifyThe Replay.State fun s => { s with env := env }
    modifyThe ExtraState fun s => { s with tasks := s.tasks.push (info.name, t) }
  | .error ex => Replay.throwKernelException ex

mutual
/--
`Replay.replayConstant`, in the monad `M`, except that theorems are added with `addThmAsync` instead
of `addDecl`.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← Replay.isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← getThe Replay.State).pending.contains name then
      try
        match ci with
        | .defnInfo   info =>
          Replay.addDecl (Declaration.defnDecl   info)
        | .thmInfo    info =>
          -- Ignore duplicate theorems. This code is identical to that in `finalizeImport` before it
          -- added extended duplicates support for the module system, which is not relevant for us
          -- here as we always load all .olean information. We need this case *because* of the module
          -- system -- as we have more data loaded than it, we might encounter duplicate private
          -- theorems where elaboration under the module system would have only one of them in scope.
          if let some (.thmInfo info') := (← getThe Replay.State).env.find? ci.name then
            if info.name == info'.name &&
              info.type == info'.type &&
              info.levelParams == info'.levelParams &&
              info.all == info'.all
            then
              return
          addThmAsync info
        | .axiomInfo  info =>
          Replay.addDecl (Declaration.axiomDecl  info)
        | .opaqueInfo info =>
          Replay.addDecl (Declaration.opaqueDecl info)
        | .inductInfo info =>
          let lparams := info.levelParams
          let nparams := info.numParams
          let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
          for o in all do
            modifyThe Replay.State fun s =>
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
          Replay.addDecl (Declaration.inductDecl lparams nparams types false)
        -- We postpone checking constructors,
        -- and at the end make sure they are identical
        -- to the constructors generated when we replay the inductives.
        | .ctorInfo info =>
          modifyThe Replay.State fun s =>
            { s with postponedConstructors := s.postponedConstructors.insert info.name }
        -- Similarly we postpone checking recursors.
        | .recInfo info =>
          modifyThe Replay.State fun s =>
            { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          -- `Quot.lift` and `Quot.ind` have types that reference `Eq`,
          -- so we need to ensure `Eq` is replayed before adding the quotient declaration.
          replayConstant `Eq
          Replay.addDecl (Declaration.quotDecl)
        modifyThe Replay.State fun s => { s with pending := s.pending.erase name }
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n

end

end ParallelReplay

open ParallelReplay

/--
"Replay" some constants into a `Kernel.Environment`, sending them to the kernel for checking.

Throws a `IO.userError` if the kernel rejects a constant,
or if there are malformed recursors or constructors for inductive types.

Theorems are checked in parallel tasks; non-theorem declarations are checked in order, as in `replay`.
-/
public def replayParallel (newConstants : Std.HashMap Name ConstantInfo) (env : Kernel.Environment) :
    IO Kernel.Environment := do
  let mut remaining : NameSet := ∅
  for (n, ci) in newConstants.toList do
    -- We skip unsafe constants, and also partial constants.
    -- Later we may want to handle partial constants.
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := ({ env, remaining } : Replay.State)) do
    ReaderT.run (r := ({ newConstants } : Replay.Context)) do
      let ((), extra) ← StateRefT'.run (s := ({} : ExtraState)) do
        for n in remaining do
          replayConstant n
      -- Wait for the kernel checks of all theorems.
      for (name, t) in extra.tasks do
        if let .error ex := t.get then
          try Replay.throwKernelException ex
          catch ex => throw <| .userError s!"while replaying declaration '{name}':\n{ex}"
      Replay.checkPostponedConstructors
      Replay.checkPostponedRecursors
  return s.env

end Kernel.Environment
