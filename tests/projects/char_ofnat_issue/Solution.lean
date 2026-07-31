prelude
set_option genCtorIdx false
set_option linter.all false

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

inductive False : Prop

inductive True' : Prop where
  | intro : True'

inductive Unit'' where
  | intro : Unit''

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

-- `Char` is a structure whose field is a PROOF OF FALSE, so `Char.n : Char → False`.
-- Char is uninhabited; we never build one.
structure Char : Type where
  mk ::
  n : False

-- `Box` is a structure with an INHABITED field.
structure Box : Type where
  mk ::
  f : True'

inductive List (α : Type u) where
  | nil : List α
  | cons (hd : α) (tl : List α) : List α

structure String where
  ofList ::
  data : List Char

-- THE MISSING CHECK: the kernel never verifies `Char.ofNat : Nat → Char`.
-- We declare it returning `Box` instead.
noncomputable def Char.ofNat (n : Nat) : Box := Box.mk True'.intro

-- motive: `M nil = Unit''`, `M (cons ..) = Char`, so `head` needs no `Char` for the nil case
noncomputable def M (l : List Char) : Type :=
  @List.rec Char (fun _ => Type) Unit'' (fun _ _ _ => Char) l

noncomputable def head (l : List Char) : M l :=
  @List.rec Char M Unit''.intro (fun hd _ _ => hd) l

-- `String.data "\x02"` projects the literal.  reduceProj expands it to
--   String.ofList (List.cons (Char.ofNat 2) List.nil)
-- and returns the list, which `inferProj` types as `List Char`.
-- Its head is really a `Box`, but the kernel types it as `Char`.
noncomputable def confused : Char := head (String.data "\x02")

-- `Char.n` is `proj Char 0`, so it hands back Box's field -- typed as `False`.
theorem boom : False := Char.n confused
