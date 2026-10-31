/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Regular
public import HtmlModel.Names

@[expose] public section

namespace HtmlModel

open Regular

/-- What is known at compile time about a run of an element's children: one node, an optional
node, a list of unknown length, a nonempty list, a list of unknown length of groups each made of
segments, a choice between two runs of segments, or whitespace. -/
inductive SegK (C : Type) where
  | one (c : C)
  | opt (c : C)
  | many (c : C)
  | many1 (c : C)
  | groups (ks : List (SegK C))
  | alt (l r : List (SegK C))
  | ws
  deriving Repr

/-- An element's content model: a grammar over the categories of its children, and whether
whitespace may stand between them without counting as text. -/
structure Spec (C : Type) where
  grammar : Regex C
  ws : Bool
  deriving DecidableEq

/-- A set of elements and the categories that say where each may appear. -/
structure Vocabulary where
  Elem : Type
  Cat : Type
  [decEqElem : DecidableEq Elem]
  [decEqCat : DecidableEq Cat]
  ns : Elem → Namespace
  name : Elem → String
  /-- The categories `c` is valid wherever: every one, transitively, not only the nearest. -/
  above : Cat → List Cat
  cats : Elem → List Cat
  spec : Elem → Cat → Spec Cat
  text : Cat

namespace Vocabulary

variable (V : Vocabulary)

instance : DecidableEq V.Elem := V.decEqElem
instance : DecidableEq V.Cat := V.decEqCat

/-- Whether a node of category `c` is valid wherever one of category `d` is. -/
def widens (c d : V.Cat) : Bool := c == d || (V.above c).contains d

/-- A child of category `c`. Where whitespace is admitted, a text child is optional, since a
whitespace-only one is then inter-element whitespace and drops out of the children checked. -/
def letter (ws : Bool) (c : V.Cat) : Regex V.Cat :=
  if ws && c == V.text then Shape.opt c else Shape.one c

/-- Children of category `c`, one or more. Where whitespace is admitted, text ones may all drop
out, as for `letter`. -/
def letters1 (ws : Bool) (c : V.Cat) : Regex V.Cat :=
  if ws && c == V.text then Shape.many c else Shape.many1 c

mutual
/-- Whitespace drops out where it is admitted, and is text elsewhere. -/
def segShape (ws : Bool) : SegK V.Cat → Regex V.Cat
  | .one c => V.letter ws c
  | .opt c => Shape.opt c
  | .many c => Shape.many c
  | .many1 c => V.letters1 ws c
  | .groups ks => .star (shape ws ks)
  | .alt l r => .alt (shape ws l) (shape ws r)
  | .ws => if ws then .eps else Shape.one V.text

/-- `Regex.seq` of each segment's shape, written out so that it recurses with `segShape`. -/
def shape (ws : Bool) : List (SegK V.Cat) → Regex V.Cat
  | [] => .eps
  | k :: ks => .cat (segShape ws k) (shape ws ks)
end

/-- Children of these kinds are valid in element `e` of category `c`. -/
def Admits (e : V.Elem) (c : V.Cat) (ks : List (SegK V.Cat)) : Prop :=
  Accepts V.widens (V.spec e c).grammar (V.shape (V.spec e c).ws ks)

instance (e : V.Elem) (c : V.Cat) (ks : List (SegK V.Cat)) : Decidable (V.Admits e c ks) :=
  inferInstanceAs (Decidable (Accepts _ _ _))

/-- Children are admitted if the coarser `Shape.kinds` of their shape is, so that children whose
kinds coarsen alike can share one proof. Reusing a proof of `Admits` for children of exactly the
same kinds is cheaper, since it needs no evaluation to match; this is for those that differ. -/
theorem admits_of_kinds {e : V.Elem} {c : V.Cat} {ks : List (SegK V.Cat)}
    (h : Accepts V.widens (V.spec e c).grammar (Shape.kinds (V.shape (V.spec e c).ws ks))) :
    V.Admits e c ks :=
  Accepts.of_coarse (Shape.accepts_kinds _) h

end Vocabulary

end HtmlModel
