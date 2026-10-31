/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Engine.Vocabulary
public import HtmlModel.Engine.Tactic

@[expose] public section

namespace HtmlModel

variable (V : Vocabulary)

-- The kernel rejects `List` or `Option` nested over a family indexed by category, so lists,
-- options and groups of nodes have types of their own.
mutual
/-- A node valid where category `c` is, carrying a payload of type `α` on each element. -/
inductive Node (α : Type) : V.Cat → Type where
  /-- Raw text, never escaped. -/
  | text (s : String) : Node α V.text
  /-- Markup emitted as it stands, valid anywhere. -/
  | verbatim {c : V.Cat} (s : String) : Node α c
  | elem (e : V.Elem) (c : V.Cat) (p : α) {ks : List (SegK V.Cat)} (segs : Segs α ks)
      (hc : c ∈ V.cats e := by decide +kernel) (ok : V.Admits e c ks := by admits) : Node α c
  /-- An element the vocabulary lacks, or whose content model it has wrong. Its children are
  checked; it is not. -/
  | unchecked (ns : Namespace) (name : String) (c : V.Cat) (p : α) (children : Frag α)
      (hname : ns.validName name = true := by decide +kernel) : Node α c
inductive Nodes (α : Type) : V.Cat → Type where
  | nil {c : V.Cat} : Nodes α c
  | cons {c : V.Cat} (n : Node α c) (ns : Nodes α c) : Nodes α c
inductive Group (α : Type) : List V.Cat → Type where
  | nil : Group α []
  | cons {c : V.Cat} {cs : List V.Cat} (n : Node α c) (g : Group α cs) : Group α (c :: cs)
inductive Groups (α : Type) : List V.Cat → Type where
  | nil {cs : List V.Cat} : Groups α cs
  | cons {cs : List V.Cat} (g : Group α cs) (gs : Groups α cs) : Groups α cs
inductive Seg (α : Type) : SegK V.Cat → Type where
  | one {c : V.Cat} (n : Node α c) : Seg α (.one c)
  | none {c : V.Cat} : Seg α (.opt c)
  | some {c : V.Cat} (n : Node α c) : Seg α (.opt c)
  | many {c : V.Cat} (ns : Nodes α c) : Seg α (.many c)
  | groups {cs : List V.Cat} (gs : Groups α cs) : Seg α (.groups cs)
  | ws (s : String) (h : isWhitespace s = true := by decide +kernel) : Seg α .ws
inductive Segs (α : Type) : List (SegK V.Cat) → Type where
  | nil : Segs α []
  | cons {k : SegK V.Cat} {ks : List (SegK V.Cat)} (x : Seg α k) (xs : Segs α ks) :
      Segs α (k :: ks)
/-- Nodes of any categories. -/
inductive Frag (α : Type) : Type where
  | nil : Frag α
  | cons {c : V.Cat} (n : Node α c) (f : Frag α) : Frag α
end

/-- Nodes of any categories, as a list. -/
abbrev Fragment (α : Type) := List ((c : V.Cat) × Node V α c)

variable {V}

def Nodes.ofList {α : Type} {c : V.Cat} : List (Node V α c) → Nodes V α c
  | [] => .nil
  | n :: ns => .cons n (Nodes.ofList ns)

def Groups.ofList {α : Type} {cs : List V.Cat} : List (Group V α cs) → Groups V α cs
  | [] => .nil
  | g :: gs => .cons g (Groups.ofList gs)

/-- `c` is explicit, because `none` alone would leave it unknown. -/
def Seg.ofOption {α : Type} (c : V.Cat) : Option (Node V α c) → Seg V α (.opt c)
  | .none => .none
  | .some n => .some n

/-- `c` is explicit, because an empty list alone would leave it unknown. -/
def Seg.ofList {α : Type} (c : V.Cat) (ns : List (Node V α c)) : Seg V α (.many c) :=
  .many (Nodes.ofList ns)

/-- Segments whose kinds are known only from the list itself, as a macro builds them. -/
def Segs.ofList {α : Type} : (l : List ((k : SegK V.Cat) × Seg V α k)) → Segs V α (l.map (·.1))
  | [] => .nil
  | ⟨_, x⟩ :: l => .cons x (Segs.ofList l)

/-- One segment per node, each of the node's own category. -/
def Segs.ofFragment {α : Type} : (f : Fragment V α) → Segs V α (f.map fun n => .one n.1)
  | [] => .nil
  | ⟨_, n⟩ :: f => .cons (.one n) (Segs.ofFragment f)

def Frag.ofList {α : Type} : Fragment V α → Frag V α
  | [] => .nil
  | ⟨_, n⟩ :: ns => .cons n (Frag.ofList ns)

/-- `segs![a, b]` is `Segs.cons a (Segs.cons b Segs.nil)`. -/
syntax "segs![" term,* "]" : term
macro_rules
  | `(segs![]) => `(Segs.nil)
  | `(segs![$x]) => `(Segs.cons $x Segs.nil)
  | `(segs![$x, $xs,*]) => `(Segs.cons $x segs![$xs,*])

section Map

variable {α β : Type}

mutual
def Node.map (f : α → β) {c : V.Cat} : Node V α c → Node V β c
  | .text s => .text s
  | .verbatim s => .verbatim s
  | .elem e c p segs hc ok => .elem e c (f p) (Segs.map f segs) hc ok
  | .unchecked ns name c p ch h => .unchecked ns name c (f p) (Frag.map f ch) h
def Nodes.map (f : α → β) {c : V.Cat} : Nodes V α c → Nodes V β c
  | .nil => .nil
  | .cons n ns => .cons (Node.map f n) (Nodes.map f ns)
def Group.map (f : α → β) {cs : List V.Cat} : Group V α cs → Group V β cs
  | .nil => .nil
  | .cons n g => .cons (Node.map f n) (Group.map f g)
def Groups.map (f : α → β) {cs : List V.Cat} : Groups V α cs → Groups V β cs
  | .nil => .nil
  | .cons g gs => .cons (Group.map f g) (Groups.map f gs)
def Seg.map (f : α → β) {k : SegK V.Cat} : Seg V α k → Seg V β k
  | .one n => .one (Node.map f n)
  | .none => .none
  | .some n => .some (Node.map f n)
  | .many ns => .many (Nodes.map f ns)
  | .groups gs => .groups (Groups.map f gs)
  | .ws s h => .ws s h
def Segs.map (f : α → β) {ks : List (SegK V.Cat)} : Segs V α ks → Segs V β ks
  | .nil => .nil
  | .cons x xs => .cons (Seg.map f x) (Segs.map f xs)
def Frag.map (f : α → β) : Frag V α → Frag V β
  | .nil => .nil
  | .cons n fr => .cons (Node.map f n) (Frag.map f fr)
end

mutual
theorem Node.map_id {c : V.Cat} : (n : Node V α c) → Node.map id n = n
  | .text _ | .verbatim _ => rfl
  | .elem _ _ _ segs _ _ => by simp only [Node.map, Segs.map_id segs]; rfl
  | .unchecked _ _ _ _ ch _ => by simp only [Node.map, Frag.map_id ch]; rfl
theorem Nodes.map_id {c : V.Cat} : (ns : Nodes V α c) → Nodes.map id ns = ns
  | .nil => rfl
  | .cons n ns => by simp only [Nodes.map, Node.map_id n, Nodes.map_id ns]
theorem Group.map_id {cs : List V.Cat} : (g : Group V α cs) → Group.map id g = g
  | .nil => rfl
  | .cons n g => by simp only [Group.map, Node.map_id n, Group.map_id g]
theorem Groups.map_id {cs : List V.Cat} : (gs : Groups V α cs) → Groups.map id gs = gs
  | .nil => rfl
  | .cons g gs => by simp only [Groups.map, Group.map_id g, Groups.map_id gs]
theorem Seg.map_id {k : SegK V.Cat} : (x : Seg V α k) → Seg.map id x = x
  | .one n | .some n => by simp only [Seg.map, Node.map_id n]
  | .none | .ws _ _ => rfl
  | .many ns => by simp only [Seg.map, Nodes.map_id ns]
  | .groups gs => by simp only [Seg.map, Groups.map_id gs]
theorem Segs.map_id {ks : List (SegK V.Cat)} : (xs : Segs V α ks) → Segs.map id xs = xs
  | .nil => rfl
  | .cons x xs => by simp only [Segs.map, Seg.map_id x, Segs.map_id xs]
theorem Frag.map_id : (fr : Frag V α) → Frag.map id fr = fr
  | .nil => rfl
  | .cons n fr => by simp only [Frag.map, Node.map_id n, Frag.map_id fr]
end

variable {γ : Type} (f : α → β) (g : β → γ)

mutual
theorem Node.map_comp {c : V.Cat} : (n : Node V α c) → Node.map (g ∘ f) n = Node.map g (Node.map f n)
  | .text _ | .verbatim _ => rfl
  | .elem _ _ _ segs _ _ => by simp only [Node.map, Segs.map_comp segs]; rfl
  | .unchecked _ _ _ _ ch _ => by simp only [Node.map, Frag.map_comp ch]; rfl
theorem Nodes.map_comp {c : V.Cat} :
    (ns : Nodes V α c) → Nodes.map (g ∘ f) ns = Nodes.map g (Nodes.map f ns)
  | .nil => rfl
  | .cons n ns => by simp only [Nodes.map, Node.map_comp n, Nodes.map_comp ns]
theorem Group.map_comp {cs : List V.Cat} :
    (x : Group V α cs) → Group.map (g ∘ f) x = Group.map g (Group.map f x)
  | .nil => rfl
  | .cons n x => by simp only [Group.map, Node.map_comp n, Group.map_comp x]
theorem Groups.map_comp {cs : List V.Cat} :
    (gs : Groups V α cs) → Groups.map (g ∘ f) gs = Groups.map g (Groups.map f gs)
  | .nil => rfl
  | .cons x gs => by simp only [Groups.map, Group.map_comp x, Groups.map_comp gs]
theorem Seg.map_comp {k : SegK V.Cat} : (x : Seg V α k) → Seg.map (g ∘ f) x = Seg.map g (Seg.map f x)
  | .one n | .some n => by simp only [Seg.map, Node.map_comp n]
  | .none | .ws _ _ => rfl
  | .many ns => by simp only [Seg.map, Nodes.map_comp ns]
  | .groups gs => by simp only [Seg.map, Groups.map_comp gs]
theorem Segs.map_comp {ks : List (SegK V.Cat)} :
    (xs : Segs V α ks) → Segs.map (g ∘ f) xs = Segs.map g (Segs.map f xs)
  | .nil => rfl
  | .cons x xs => by simp only [Segs.map, Seg.map_comp x, Segs.map_comp xs]
theorem Frag.map_comp : (fr : Frag V α) → Frag.map (g ∘ f) fr = Frag.map g (Frag.map f fr)
  | .nil => rfl
  | .cons n fr => by simp only [Frag.map, Node.map_comp n, Frag.map_comp fr]
end

end Map

variable (V) in
/-- `Node` with the payload last, so that it is a `Functor`. -/
abbrev NodeF (c : V.Cat) (α : Type) : Type := Node V α c

instance {c : V.Cat} : Functor (NodeF V c) where
  map f n := Node.map f n

instance {c : V.Cat} : LawfulFunctor (NodeF V c) where
  map_const := rfl
  id_map := Node.map_id
  comp_map f g := Node.map_comp f g

end HtmlModel
