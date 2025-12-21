/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.ExportedEnv

namespace Comparator

namespace Parser

structure State where
  nameMap : Std.HashMap Nat Lean.Name
  levelMap : Std.HashMap Nat Lean.Level
  exprMap : Std.HashMap Nat Lean.Expr
  recursorRuleMap : Std.HashMap Nat Lean.RecursorRule
  constMap : Std.HashMap Lean.Name Lean.ConstantInfo
  constOrder : Array Lean.Name
  input : String.Legacy.Iterator
  deriving Inhabited

abbrev M := StateT State <| Except String

def M.run (x : M α) (input : String) : Except String (α × State) := do
  let initial := {
    nameMap := { (0, .anonymous) }
    levelMap := { (0, .zero) }
    exprMap := {}
    recursorRuleMap := {}
    constMap := {}
    constOrder := #[],
    input := String.Legacy.iter input
  }
  StateT.run x initial

@[inline]
def getName (nidx : Nat) : M Lean.Name := do
  let some n := (← get).nameMap[nidx]? | throw s!"Name not found {nidx}"
  return n

@[inline]
def addName (nidx : Nat) (n : Lean.Name) : M Unit := do
  modify fun s => { s with nameMap := s.nameMap.insert nidx n }

@[inline]
def getLevel (uidx : Nat) : M Lean.Level := do
  let some l := (← get).levelMap[uidx]? | throw s!"Level not found {uidx}"
  return l

@[inline]
def addLevel (uidx : Nat) (l : Lean.Level) : M Unit := do
  modify fun s => { s with levelMap := s.levelMap.insert uidx l }

@[inline]
def getExpr (eidx : Nat) : M Lean.Expr := do
  let some e := (← get).exprMap[eidx]? | throw s!"Expr not found {eidx}"
  return e

@[inline]
def addExpr (eidx : Nat) (e : Lean.Expr) : M Unit := do
  modify fun s => { s with exprMap := s.exprMap.insert eidx e }

@[inline]
def getRecursorRule (ridx : Nat) : M Lean.RecursorRule := do
  let some r := (← get).recursorRuleMap[ridx]? | throw s!"RecursorRule not found {ridx}"
  return r

@[inline]
def addRecursorRule (ridx : Nat) (r : Lean.RecursorRule) : M Unit := do
  modify fun s => { s with recursorRuleMap := s.recursorRuleMap.insert ridx r }

@[inline]
def addConst (name : Lean.Name) (d : Lean.ConstantInfo) : M Unit := do
  modify fun s => {
    s with
      constMap := s.constMap.insert name d
      constOrder := s.constOrder.push name
    }


abbrev LineM := StateT (List String) M

@[inline]
def M.runWithNextLine (x : LineM α) : M α := do
  let mut input := (← get).input
  let mut s := ""
  let mut acc := []
  while true do
    if h : input.hasNext then
      let char := input.curr' h
      if char == ' ' then
        if s != "" then
          acc := s :: acc
          s := ""
      else if char == '\n' then
        if s != "" then
          acc := s :: acc
        break
      else
        s := s.push char
      input := input.next
    else
      break

  if input.curr == '\n' then
    input := input.next

  modify fun s => { s with input }

  acc := acc.reverse
  x.run' acc

def LineM.next? : LineM (Option String) := do
  match (← get) with
  | [] => return none
  | s :: s' =>
    set s'
    return some s

@[inline]
def LineM.next! : LineM String := do
  let some next ← LineM.next? | throw "Line empty"
  return next

@[inline]
def LineM.eol : LineM Bool := do
  return (← get).isEmpty

@[inline]
def parseDigits? : LineM (Option Nat) := do
  let some str ← LineM.next? | return none
  let some nat := String.toNat? str | throw s!"'{str}' is not a Nat"
  return nat

@[inline]
def parseDigits : LineM Nat := do
  let str ← LineM.next!
  let some nat := String.toNat? str | throw s!"'{str}' is not a Nat"
  return nat

@[inline]
def parseBool : LineM Bool := do
  return (← parseDigits) == 1

@[specialize]
partial def parseTrailing [ToString α] (x : LineM α) : LineM (Array α) :=
  go x #[]
where
  @[specialize]
  go (x : LineM α) (acc : Array α) : LineM (Array α) := do
    if ← LineM.eol then
      return acc
    else
      go x <| acc.push (← x)

@[inline]
def parseNameIdx : LineM Lean.Name := do
  let name ← parseDigits
  getName name

@[inline]
def parseExprIdx : LineM Lean.Expr := do
  let expr ← parseDigits
  getExpr expr

@[inline]
def parseLevelIdx : LineM Lean.Level := do
  let level ← parseDigits
  getLevel level

@[inline]
def parseRecursorRuleIdx : LineM Lean.RecursorRule := do
  let rr ← parseDigits
  getRecursorRule rr

@[inline]
def parseLevelParams : LineM (List Lean.Name) := do
  let levelParams ← parseTrailing parseDigits
  return (← levelParams.mapM (liftM ∘ getName)).toList

@[inline]
def parseUniverses : LineM (List Lean.Level) := do
  let us ← parseTrailing parseDigits
  return (← us.mapM (liftM ∘ getLevel)).toList

def parseAxiom : LineM Unit := do
  let name ← parseNameIdx
  let type ← parseExprIdx
  let levelParams ← parseLevelParams

  addConst name (.axiomInfo { name, type, levelParams, isUnsafe := false })

def parseHints : LineM Lean.ReducibilityHints := do
  let tok ← LineM.next!
  match tok with
  | "O" => return .opaque
  | "A" => return .abbrev
  | "R" =>
    let n ← parseDigits
    return .regular n.toUInt32
  | _ => throw s!"Invalid hint: '{tok}'"

def parseDef : LineM Unit :=  do
  let name ← parseNameIdx
  let type ← parseExprIdx
  let value ← parseExprIdx
  let hints ← parseHints
  let levelParams ← parseLevelParams

  addConst name (.defnInfo { name, type, value, levelParams, hints, safety := .safe })

def parseOpaque : LineM Unit := do
  let name ← parseNameIdx
  let type ← parseExprIdx
  let value ← parseExprIdx
  let levelParams ← parseLevelParams

  addConst name (.opaqueInfo { name, type, value, levelParams, isUnsafe := false })

def parseQuot : LineM Unit := do
  let name ← parseNameIdx
  let type ← parseExprIdx
  let levelParams ← parseLevelParams

  let kind :=
    match name with
    | `Quot => some .type
    | `Quot.mk => some .ctor
    | `Quot.lift => some .lift
    | `Quot.ind => some .ind
    | _ => none

  let some kind := kind | throw s!"Invalid quot kind: {name}"
  addConst name (.quotInfo { name, type, levelParams, kind })

def parseThm : LineM Unit := do
  let name ← parseNameIdx
  let type ← parseExprIdx
  let value ← parseExprIdx
  let levelParams ← parseLevelParams

  addConst name (.thmInfo { name, type, value, levelParams })

@[specialize]
def exactlyN (p : LineM α) (n : Nat) : LineM (List α) := do
  go p n []
where
  @[specialize]
  go (p : LineM α) (n : Nat) (acc : List α) : LineM (List α) := do
    match n with
    | 0 => return acc.reverse
    | n + 1 =>
      let x ← p
      go p n (x :: acc)


def parseInd : LineM Unit := do
  let name ← parseNameIdx
  let type ← parseExprIdx
  let isReflexive ← parseBool
  let isRec ← parseBool
  let numNested ← parseDigits
  let numParams ← parseDigits
  let numIndices ← parseDigits
  let numInductives ← parseDigits
  let all ← exactlyN parseNameIdx numInductives
  let numCtors ← parseDigits
  let ctors ← exactlyN parseNameIdx numCtors
  let levelParams ← parseLevelParams

  addConst name (.inductInfo {
    name,
    type,
    numParams,
    numIndices,
    all,
    ctors,
    isRec,
    levelParams,
    numNested
    isReflexive
    isUnsafe := false,
  })

def parseCtor : LineM Unit := do
  let name ← parseNameIdx
  let type ← parseExprIdx
  let induct ← parseNameIdx
  let cidx ← parseDigits
  let numParams ← parseDigits
  let numFields ← parseDigits
  let levelParams ← parseLevelParams

  addConst name (.ctorInfo {
    name,
    type,
    induct,
    levelParams,
    cidx,
    numParams,
    numFields,
    isUnsafe := false
  })

def parseRecursorRule (idx : Nat) (tok : String) : LineM Unit := do
  match tok with
  | "#RR" =>
    let ctor ← parseNameIdx
    let nfields ← parseDigits
    let rhs ← parseExprIdx

    addRecursorRule idx { ctor, nfields, rhs }
  | _ => throw s!"Invalid recursor rule: '{tok}'"

def parseRec : LineM Unit := do
  let name ← parseNameIdx
  let type ← parseExprIdx
  let numInductives ← parseDigits
  let all ← exactlyN parseNameIdx numInductives
  let numParams ← parseDigits
  let numIndices ← parseDigits
  let numMotives ← parseDigits
  let numMinors ← parseDigits
  let numRules ← parseDigits
  let rules ← exactlyN parseRecursorRuleIdx numRules
  let k ← parseBool
  let levelParams ← parseLevelParams

  addConst name (.recInfo {
    name,
    type,
    all,
    numParams,
    numIndices,
    numMotives,
    numMinors,
    rules,
    k,
    levelParams,
    isUnsafe := false
  })


def parseBinderInfo : LineM Lean.BinderInfo := do
  let tok ← LineM.next!
  match tok with
  | "#BD" => return .default
  | "#BI" => return .implicit
  | "#BS" => return .strictImplicit
  | "#BC" => return .instImplicit
  | _ => throw s!"Invalid binder info: '{tok}'"

def parseExpr (idx : Nat) (tok : String) : LineM Unit := do
  match tok with
  | "#EV" =>
    let bidx ← parseDigits

    addExpr idx (.bvar bidx)
  | "#ES" =>
    let u ← parseLevelIdx

    addExpr idx (.sort u)
  | "#EC" =>
    let name ← parseNameIdx
    let us ← parseUniverses

    addExpr idx (.const name us)
  | "#EA" =>
    let f ← parseExprIdx
    let a ← parseExprIdx

    addExpr idx (.app f a)
  | "#EL" =>
    let bi ← parseBinderInfo
    let n ← parseNameIdx
    let d ← parseExprIdx
    let b ← parseExprIdx

    addExpr idx (.lam n d b bi)
  | "#EP" =>
    let bi ← parseBinderInfo
    let n ← parseNameIdx
    let d ← parseExprIdx
    let b ← parseExprIdx

    addExpr idx (.forallE n d b bi)
  | "#EZ" =>
    let n ← parseNameIdx
    let d ← parseExprIdx
    let v ← parseExprIdx
    let b ← parseExprIdx

    addExpr idx (.letE n d v b false)
  | "#EJ" =>
    let pname ← parseNameIdx
    let pidx ← parseDigits
    let expr ← parseExprIdx

    addExpr idx (.proj pname pidx expr)
  | "#ELN" =>
    let lit ← parseDigits

    addExpr idx (.lit <| .natVal lit)
  | "#ELS" =>
    let hexToU8 (c : Char) : M UInt8 :=
      if ('0' ≤ c ∧ c ≤ '9') then
        return c.toUInt8 - '0'.toUInt8
      else if ('a' ≤ c ∧ c ≤ 'f') then
        return c.toUInt8 - 'a'.toUInt8 + 10
      else if ('A' ≤ c ∧ c ≤ 'F') then
        return c.toUInt8 - 'A'.toUInt8 + 10
      else
        throw s!"Invalid hex char '{c}'"

    let u8 : LineM UInt8 := do
      let next ← LineM.next!
      if next.utf8ByteSize != 2 then
        throw s!"Invalid hex part of string lit: '{next}'"

      let d1 ← hexToU8 <| String.Pos.Raw.mk 0 |>.get next
      let d2 ← hexToU8 <| String.Pos.Raw.mk 1 |>.get next
      return (d1 <<< 4) ||| d2
    let bytes ← parseTrailing u8
    let some str := String.fromUTF8? (.mk bytes)
      | throw s!"Failed to convert bytes to string '{bytes}'"

    addExpr idx (.lit <| .strVal str)
  | _ => throw s!"invalid expression variant '{tok}'"

def parseUniverse (idx : Nat) (tok : String) : LineM Unit := do
  match tok with
  | "#US" =>
    let parent ← parseLevelIdx

    addLevel idx (.succ parent)
  | "#UM" =>
    let lhs ← parseLevelIdx
    let rhs ← parseLevelIdx

    addLevel idx (.max lhs rhs)
  | "#UIM" =>
    let lhs ← parseLevelIdx
    let rhs ← parseLevelIdx

    addLevel idx (.imax lhs rhs)
  | "#UP" =>
    let name ← parseNameIdx

    addLevel idx (.param name)
  | _ => throw s!"invalid universe variant '{tok}'"

def parseName (idx : Nat) (tok : String) : LineM Unit := do
  match tok with
  | "#NS" =>
    let parent ← parseNameIdx
    let name ← LineM.next!

    addName idx (.str parent name)
  | "#NI" =>
    let parent ← parseNameIdx
    let name ← parseDigits

    addName idx (.num parent name)
  | _ => throw s!"invalid name variant: '{tok}'"

def parsePrimitive (idx : String) : LineM Unit := do
  let some idx := String.toNat? idx | throw s!"Invalid index '{idx}'"
  let tok ← LineM.next!
  if (String.Pos.Raw.mk 0).get! tok != '#' then throw s!"Invalid primitive kind '{tok}'"
  match (String.Pos.Raw.mk 1).get! tok with
  | 'N' => parseName idx tok
  | 'U' => parseUniverse idx tok
  | 'E' => parseExpr idx tok
  | 'R' => parseRecursorRule idx tok
  | _ => throw s!"Invalid primitive kind: '{tok}'"

def parseItem : LineM Unit := do
  let headTok ← LineM.next!
  match headTok with
  | "#AX" => parseAxiom
  | "#DEF" => parseDef
  | "#OPAQ" => parseOpaque
  | "#QUOT" => parseQuot
  | "#THM" => parseThm
  | "#IND" => parseInd
  | "#CTOR" => parseCtor
  | "#REC" => parseRec
  | idx => parsePrimitive idx


partial def parseItems : M Unit :=
  go
where
  go : M Unit := do
    if !(← get).input.hasNext then
      return ()
    else
      M.runWithNextLine parseItem
      go

def parseVersion : LineM (Nat × Nat × Nat) := do
  let ver ← LineM.next!
  let some parts := (ver.splitOn "." |>.mapM String.toNat? : Option _) |
    throw s!"Version invalid: '{ver}'"
  if parts.length != 3 then
    throw "Version invalid: '{ver}'"
  return (parts[0]!, parts[1]!, parts[2]!)

def parseFile : M Unit := do
  let version ← M.runWithNextLine parseVersion
  if version != (2, 0, 0) then
    throw s!"unsupported version: {version}"
  parseItems

end Parser


def parse (input : String) : Except String ExportedEnv := do
  let (_, state) ← Parser.M.run Parser.parseFile input
  let { constMap, constOrder, .. } := state
  return {
    constMap,
    constOrder,
  }

end Comparator
