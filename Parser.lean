import Std.Internal.Parsec.String
import Std.Data.HashMap
import Lean.Expr

open Std.Internal.Parsec
open Std.Internal.Parsec.String

namespace Parser

structure State where
  nameMap : Std.HashMap Nat Lean.Name
  levelMap : Std.HashMap Nat Lean.Level
  exprMap : Std.HashMap Nat Lean.Expr
  deriving Inhabited, Repr

abbrev M := StateT State Parser

def M.run (x : M α) (input : String) : Except String (α × State) := do
  let initial := { nameMap := { (0, .anonymous) }, levelMap := { (0, .zero) }, exprMap := {} }
  Parser.run (StateT.run x initial) input

@[inline]
def getName (nidx : Nat) : M Lean.Name := do
  let some n := (← get).nameMap[nidx]? | (fail s!"Name not found {nidx}" : Parser _)
  return n

@[inline]
def addName (nidx : Nat) (n : Lean.Name) : M Unit := do
  modify fun s => { s with nameMap := s.nameMap.insert nidx n }

@[inline]
def getLevel (uidx : Nat) : M Lean.Level := do
  let some l := (← get).levelMap[uidx]? | (fail s!"Level not found {uidx}" : Parser _)
  return l

@[inline]
def addLevel (uidx : Nat) (l : Lean.Level) : M Unit := do
  modify fun s => { s with levelMap := s.levelMap.insert uidx l }

@[inline]
def getExpr (eidx : Nat) : M Lean.Expr := do
  let some e := (← get).exprMap[eidx]? | (fail s!"Expr not found {eidx}" : Parser _)
  return e

@[inline]
def addExpr (eidx : Nat) (e : Lean.Expr) : M Unit := do
  modify fun s => { s with exprMap := s.exprMap.insert eidx e }

@[inline]
def readToken : Parser String := do
  let tok ← many1Chars <| satisfy fun c => c != ' '
  skipChar ' '
  return tok

-- TODO
def parseAxiom : M Unit := return ()
def parseDef : M Unit := return ()
def parseOpaque : M Unit := return ()
def parseQuot : M Unit := return ()
def parseThm : M Unit := return ()
def parseInd : M Unit := return ()
def parseCtor : M Unit := return ()
def parseRec : M Unit := return ()

def parseBinderInfo : Parser Lean.BinderInfo := do
  let tok ← many1Chars <| satisfy fun c => c != ' '
  match tok with
  | "#BD" => return .default
  | "#BI" => return .implicit
  | "#BS" => return .strictImplicit
  | "#BC" => return .instImplicit
  | _ => fail s!"Invalid binder info: '{tok}'"

def parseExpr (idx : Nat) (tok : String) : M Unit := do
  match tok with
  | "#EV" =>
    let bidx ← digits

    addExpr idx (.bvar bidx)
  | "#ES" =>
    let uidx ← digits

    let u ← getLevel uidx
    addExpr idx (.sort u)
  | "#EC" =>
    let nidx ← digits
    skipChar ' '

    let uidxs ← many do
      let idx ← digits
      if (← (peek? : Parser _)) == some ' ' then
        skipChar ' '
      return idx
    
    let name ← getName nidx
    let us ← uidxs.mapM getLevel
    addExpr idx (.const name us.toList)
  | "#EA" =>
    let fidx ← digits
    skipChar ' '
    let aidx ← digits

    let f ← getExpr fidx
    let a ← getExpr aidx
    addExpr idx (.app f a)
  | "#EL" =>
    let bi ← parseBinderInfo
    skipChar ' '
    let nidx ← digits
    skipChar ' '
    let didx ← digits
    skipChar ' '
    let bidx ← digits

    let n ← getName nidx
    let d ← getExpr didx
    let b ← getExpr bidx
    addExpr idx (.lam n d b bi)
  | "#EP" =>
    let bi ← parseBinderInfo
    skipChar ' '
    let nidx ← digits
    skipChar ' '
    let didx ← digits
    skipChar ' '
    let bidx ← digits

    let n ← getName nidx
    let d ← getExpr didx
    let b ← getExpr bidx
    addExpr idx (.forallE n d b bi)
  | "#EZ" =>
    let nidx ← digits
    skipChar ' '
    let didx ← digits
    skipChar ' '
    let vidx ← digits
    skipChar ' '
    let bidx ← digits

    let n ← getName nidx
    let d ← getExpr didx
    let v ← getExpr vidx
    let b ← getExpr bidx
    addExpr idx (.letE n d v b false)
  | "#EJ" =>
    let pname ← digits
    skipChar ' '
    let pidx ← digits
    skipChar ' '
    let eidx ← digits

    let pname ← getName pname
    let expr ← getExpr eidx
    addExpr idx (.proj pname pidx expr)
  | "#ELN" =>
    let lit ← digits

    addExpr idx (.lit <| .natVal lit)
  | "#ELS" =>
    let hexToU8 (c : Char) : UInt8 :=
      if ('0' ≤ c ∧ c ≤ '9') then
        c.toUInt8 - '0'.toUInt8
      else if ('a' ≤ c ∧ c ≤ 'f') then
        c.toUInt8 - 'a'.toUInt8
      else if ('A' ≤ c ∧ c ≤ 'F') then
        c.toUInt8 - 'A'.toUInt8
      else
        0

    let u8 : Parser UInt8 := do
      let d1 := hexToU8 (← hexDigit)
      let d2 := hexToU8 (← hexDigit)
      if (← (peek? : Parser _)) == some ' ' then
        skipChar ' '
      return (d1 <<< 4) ||| d2
    let bytes ← many u8
    let some str := String.fromUTF8? (.mk bytes) | (fail s!"Failed to convert bytes to string '{bytes}'" : Parser _)

    addExpr idx (.lit <| .strVal str)
  | _ => (fail s!"invalid expression variant '{tok}'" : Parser _)

def parseUniverse (idx : Nat) (tok : String) : M Unit := do
  match tok with
  | "#US" =>
    let parent ← digits

    let parent ← getLevel parent
    addLevel idx (.succ parent)
  | "#UM" =>
    let lhs ← digits
    skipChar ' '
    let rhs ← digits

    let lhs ← getLevel lhs
    let rhs ← getLevel rhs
    addLevel idx (.max lhs rhs)
  | "#UIM" =>
    let lhs ← digits
    skipChar ' '
    let rhs ← digits

    let lhs ← getLevel lhs
    let rhs ← getLevel rhs
    addLevel idx (.imax lhs rhs)
  | "#UP" =>
    let name ← digits

    let name ← getName name
    addLevel idx (.param name)
  | _ => (fail s!"invalid universe variant '{tok}'" : Parser _)

def parseName (idx : Nat) (tok : String) : M Unit := do
  match tok with
  | "#NS" =>
    let parent ← digits
    skipChar ' '
    let name ← (many1Chars <| satisfy fun c => c != '\n' : Parser _)

    let parent ← getName parent
    addName idx (.str parent name)
  | "#NI" =>
    let parent ← digits
    skipChar ' '
    let name ← digits

    let parent ← getName parent
    addName idx (.num parent name)
  | _ => (fail s!"invalid name variant: '{tok}'" : Parser _)

def parsePrimitive (idx : String) : M Unit := do
  let some idx := String.toNat? idx | (fail s!"Invalid index '{idx}'" : Parser _)
  let tok ← readToken
  if tok.startsWith "#N" then
    parseName idx tok
  else if tok.startsWith "#U" then
    parseUniverse idx tok
  else if tok.startsWith "#E" then
    parseExpr idx tok
  else
    (fail s!"Invalid primitive kind: '{tok}'" : Parser _)

def parseItem : M Unit := do
  let headTok ← readToken
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
  dbg_trace s!"hello? {← (peek! : Parser _)}"
  skipChar '\n'


partial def parseItems : M Unit :=
  go
where
  go : M Unit := do
    if ← (isEof : Parser Bool) then
      return ()
    else
      parseItem
      go

def parseVersion : M (Nat × Nat × Nat) := sorry

def parseFile : M Unit := do
  let version ← parseVersion
  if version != (1, 2, 0) then
    (fail "unsupported version" : Parser Unit)
  parseItems

def input : String :=
"1 #NS 0 Nat
0 #EC 1 0 0 0
2 #NS 1 zero
1 #EC 2 
2 #EV 0
3 #NS 0 x
3 #EZ 3 0 1 2
"

end Parser

