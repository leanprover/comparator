/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Environment

namespace Comparator

def runForUsedConsts [Monad m] (info : Lean.ConstantInfo) (f : Lean.Name → m Unit) : m Unit := do
  info.type.getUsedConstants.forM f
  f info.name
  if let some val := info.value? (allowOpaque := true) then
    val.getUsedConstants.forM f

  match info with
  | .axiomInfo .. | .quotInfo .. | .defnInfo .. | .thmInfo .. | .opaqueInfo .. => return ()
  | .inductInfo info =>
    info.ctors.forM f
    info.all.forM f
  | .ctorInfo info =>
    f info.induct
  | .recInfo info =>
    info.rules.forM fun rule => do
      f rule.ctor
      rule.rhs.getUsedConstants.forM f

/--
The names in `constMap` that `roots` depend on, transitively and including `roots` themselves.
-/
partial def dependencyClosure (constMap : Std.HashMap Lean.Name Lean.ConstantInfo)
    (roots : Array Lean.Name) : Lean.NameSet :=
  (roots.forM visit).run {} |>.snd
where
  visit (n : Lean.Name) : StateM Lean.NameSet Unit := do
    if (← get).contains n then return
    let some info := constMap[n]? | return
    modify (·.insert n)
    runForUsedConsts info visit
    -- The kernel needs `Eq` to add `Quot`, without `Quot` mentioning it.
    if info matches .quotInfo .. then visit ``Eq

end Comparator
