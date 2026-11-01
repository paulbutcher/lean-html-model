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
segments, or a choice between two runs of segments. -/
inductive SegK (C : Type) where
  | one (c : C)
  | opt (c : C)
  | many (c : C)
  | many1 (c : C)
  | groups (ks : List (SegK C))
  | alt (l r : List (SegK C))
  deriving Repr

/-- An element's content model: a grammar over the categories of its children, and whether
whitespace may stand between them without counting as text. -/
structure Spec (C : Type) where
  grammar : Regex C
  ws : Bool
  deriving DecidableEq

/-- What nodes and erased trees need of a vocabulary. Its rules are propositions, which compile to
nothing, so that building and erasing a tree reaches none of the vocabulary's tables at run time. -/
structure Signature where
  Elem : Type
  Cat : Type
  ns : Elem → Namespace
  name : Elem → String
  text : Cat
  ws : Cat
  /-- Element `e` may be checked as category `c`. -/
  Takes : Elem → Cat → Prop
  Admits : Elem → Cat → List (SegK Cat) → Prop
  Widens : Cat → Cat → Prop

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
  /-- Inter-element whitespace, which is text, and may stand wherever whitespace drops out. -/
  ws : Cat
  above_trans : ∀ {c d e : Cat}, d ∈ above c → e ∈ above d → e ∈ above c
  text_above_ws : text ∈ above ws
  /-- Nothing else is valid only where whitespace is, so that whitespace alone drops out. -/
  ws_least : ∀ c, ws ∉ above c

namespace Vocabulary

variable (V : Vocabulary)

instance : DecidableEq V.Elem := V.decEqElem
instance : DecidableEq V.Cat := V.decEqCat

/-- Whether a node of category `c` is valid wherever one of category `d` is. -/
def widens (c d : V.Cat) : Bool := c == d || (V.above c).contains d

theorem widens_refl (c : V.Cat) : V.widens c c = true := by simp [widens]

theorem widens_trans {c d e : V.Cat} (hcd : V.widens c d = true) (hde : V.widens d e = true) :
    V.widens c e = true := by
  simp only [widens, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at *
  rcases hcd with rfl | hcd
  · exact hde
  · rcases hde with rfl | hde
    · exact .inr hcd
    · exact .inr (V.above_trans hcd hde)

theorem ws_widens_text : V.widens V.ws V.text = true := by
  simp [widens, V.text_above_ws]

theorem eq_ws_of_widens {c : V.Cat} (h : V.widens c V.ws = true) : c = V.ws := by
  simpa [widens, V.ws_least c] using h

theorem text_ne_ws : V.text ≠ V.ws := fun h => V.ws_least V.ws (h ▸ V.text_above_ws)

/-- Whether children of category `c` drop out entirely: whitespace, where it is admitted. -/
def drops (ws : Bool) (c : V.Cat) : Bool := ws && c == V.ws

/-- A child of category `c`. Where whitespace is admitted and may be of category `c`, the child is
optional, since whitespace-only text then drops out of the children checked. -/
def letter (ws : Bool) (c : V.Cat) : Regex V.Cat :=
  if V.drops ws c then .eps else if ws && V.widens V.ws c then Shape.opt c else Shape.one c

/-- Children of category `c`, one or more, which may all drop out as for `letter`. -/
def letters1 (ws : Bool) (c : V.Cat) : Regex V.Cat :=
  if V.drops ws c then .eps else if ws && V.widens V.ws c then Shape.many c else Shape.many1 c

mutual
def segShape (ws : Bool) : SegK V.Cat → Regex V.Cat
  | .one c => V.letter ws c
  | .opt c => if V.drops ws c then .eps else Shape.opt c
  | .many c => if V.drops ws c then .eps else Shape.many c
  | .many1 c => V.letters1 ws c
  | .groups ks => .star (shape ws ks)
  | .alt l r => .alt (shape ws l) (shape ws r)

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

/-- The signature nodes of this vocabulary are built on. It is inlined, so that compiled code
keeps only the names and categories it holds. -/
@[reducible, inline] def sig : Signature where
  Elem := V.Elem
  Cat := V.Cat
  ns := V.ns
  name := V.name
  text := V.text
  ws := V.ws
  Takes e c := c ∈ V.cats e
  Admits := V.Admits
  Widens c d := V.widens c d = true

end Vocabulary

end HtmlModel
