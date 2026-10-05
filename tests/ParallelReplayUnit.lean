import Lean
import Comparator.Replay

/-!
Kernel-level tests of `Lean.Kernel.Environment.replayParallel`. Every case must be accepted or rejected
exactly as by `Lean.Kernel.Environment.replay`; the rejected cases include proofs that the elaborator would
never produce, so they are built directly as `ConstantInfo`s.

Run with `lake env lean --run tests/ParallelReplayUnit.lean` (after `lake build`).
-/

open Lean

/-- `inductive TestTrue : Prop | intro` and `inductive TestFalse : Prop` (no constructors). -/
def propInductives : List ConstantInfo :=
  let trueInd : InductiveVal := {
    name := `TestTrue, levelParams := [], type := .sort .zero,
    numParams := 0, numIndices := 0, all := [`TestTrue], ctors := [`TestTrue.intro],
    numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }
  let trueCtor : ConstructorVal := {
    name := `TestTrue.intro, levelParams := [], type := .const `TestTrue [],
    induct := `TestTrue, cidx := 0, numParams := 0, numFields := 0, isUnsafe := false }
  let falseInd : InductiveVal := {
    name := `TestFalse, levelParams := [], type := .sort .zero,
    numParams := 0, numIndices := 0, all := [`TestFalse], ctors := [],
    numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }
  [.inductInfo trueInd, .ctorInfo trueCtor, .inductInfo falseInd]

def thm (name : Name) (type value : Expr) : ConstantInfo :=
  .thmInfo { name, levelParams := [], type, value, all := [name] }

/-- Replay `propInductives ++ extra` with both `replay` and `replayParallel`; return whether both
gave the expected verdict. -/
def runBoth (label : String) (expectAccept : Bool) (extra : List ConstantInfo) : IO Bool := do
  let constMap := (propInductives ++ extra).foldl (init := {}) fun m ci => m.insert ci.name ci
  let kenv := (← mkEmptyEnvironment).toKernelEnv
  let seqOk ← try discard <| kenv.replay constMap; pure true catch _ => pure false
  let parOk ← try discard <| kenv.replayParallel constMap; pure true catch _ => pure false
  let ok := seqOk == expectAccept && parOk == expectAccept
  IO.println s!"{if ok then "ok  " else "FAIL"} {label}: expected accept={expectAccept}, replay={seqOk}, replayParallel={parOk}"
  return ok

def main : IO UInt32 := do
  let tru := Expr.const `TestTrue []
  let intro := Expr.const `TestTrue.intro []
  let fls := Expr.const `TestFalse []
  let results := #[
    -- a valid chain: `lemA : TestTrue := intro`, `thmB : TestTrue := lemA`
    ← runBoth "valid chain of theorems" true
      [thm `lemA tru intro, thm `thmB tru (.const `lemA [])],
    -- a theorem whose proof has the wrong type (`TestTrue` is a type, not a proof of `TestTrue`)
    ← runBoth "ill-typed proof of the last theorem" false
      [thm `lemA tru intro, thm `thmB tru tru],
    -- an ill-typed lemma used by a theorem whose own proof is fine given the lemma's statement
    ← runBoth "ill-typed proof of a lemma used later" false
      [thm `lemBad fls intro, thm `thmUsesBad fls (.const `lemBad [])],
    -- two theorems that prove `TestFalse` from each other
    ← runBoth "cyclic theorems" false
      [thm `cycleA fls (.const `cycleB []), thm `cycleB fls (.const `cycleA [])],
    -- an ill-typed definition (checked on the main thread, as in `replay`)
    ← runBoth "ill-typed definition" false
      [.defnInfo { name := `badDef, levelParams := [], type := fls, value := intro,
                   hints := .abbrev, safety := .safe, all := [`badDef] }]
  ]
  if results.all id then
    IO.println "All parallel replay kernel tests passed."
    return 0
  else
    IO.println "Some parallel replay kernel tests FAILED."
    return 1
