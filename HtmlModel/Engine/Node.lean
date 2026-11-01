/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Engine.Vocabulary
public import HtmlModel.Engine.Tactic

@[expose] public section

namespace HtmlModel

variable (S : Signature)

-- The kernel rejects `List` or `Option` nested over a family indexed by category, so lists,
-- options and groups of segments have types of their own.
mutual
/-- A node valid where category `c` is, carrying a payload of type `α` on each element. -/
inductive Node (α : Type) : S.Cat → Type where
  /-- Raw text, never escaped. -/
  | text (s : String) : Node α S.text
  /-- Inter-element whitespace. -/
  | ws (s : String) (h : isWhitespace s = true := by decide +kernel) : Node α S.ws
  /-- Markup emitted as it stands, valid anywhere. -/
  | verbatim {c : S.Cat} (s : String) : Node α c
  /-- Element `e` checked as category `c`, which decides its content model. -/
  | elem (e : S.Elem) (c : S.Cat) (p : α) {ks : List (SegK S.Cat)} (segs : Segs α ks)
      (hc : S.Takes e c := by decide +kernel) (ok : S.Admits e c ks := by admits) : Node α c
  /-- An element the vocabulary lacks, or whose content model it has wrong. Its children are
  checked; it is not. -/
  | unchecked (ns : Namespace) (name : String) (c : S.Cat) (p : α) (children : Frag α)
      (hname : ns.validName name = true := by decide +kernel) : Node α c
  /-- `n`, placed where category `d` is valid. -/
  | widen {c d : S.Cat} (n : Node α c) (h : S.Widens c d := by decide +kernel) : Node α d
inductive Nodes (α : Type) : S.Cat → Type where
  | nil {c : S.Cat} : Nodes α c
  | cons {c : S.Cat} (n : Node α c) (ns : Nodes α c) : Nodes α c
inductive Groups (α : Type) : List (SegK S.Cat) → Type where
  | nil {ks : List (SegK S.Cat)} : Groups α ks
  | cons {ks : List (SegK S.Cat)} (g : Segs α ks) (gs : Groups α ks) : Groups α ks
inductive Seg (α : Type) : SegK S.Cat → Type where
  | one {c : S.Cat} (n : Node α c) : Seg α (.one c)
  | none {c : S.Cat} : Seg α (.opt c)
  | some {c : S.Cat} (n : Node α c) : Seg α (.opt c)
  | many {c : S.Cat} (ns : Nodes α c) : Seg α (.many c)
  | many1 {c : S.Cat} (n : Node α c) (ns : Nodes α c) : Seg α (.many1 c)
  | groups {ks : List (SegK S.Cat)} (gs : Groups α ks) : Seg α (.groups ks)
  | inl {l r : List (SegK S.Cat)} (xs : Segs α l) : Seg α (.alt l r)
  | inr {l r : List (SegK S.Cat)} (xs : Segs α r) : Seg α (.alt l r)
inductive Segs (α : Type) : List (SegK S.Cat) → Type where
  | nil : Segs α []
  | cons {k : SegK S.Cat} {ks : List (SegK S.Cat)} (x : Seg α k) (xs : Segs α ks) :
      Segs α (k :: ks)
/-- Nodes of any categories. -/
inductive Frag (α : Type) : Type where
  | nil : Frag α
  | cons {c : S.Cat} (n : Node α c) (f : Frag α) : Frag α
end

/-- Nodes of any categories, as a list. -/
abbrev Fragment (α : Type) := List ((c : S.Cat) × Node S α c)

variable {S}

def Nodes.ofList {α : Type} {c : S.Cat} : List (Node S α c) → Nodes S α c
  | [] => .nil
  | n :: ns => .cons n (Nodes.ofList ns)

def Groups.ofList {α : Type} {ks : List (SegK S.Cat)} : List (Segs S α ks) → Groups S α ks
  | [] => .nil
  | g :: gs => .cons g (Groups.ofList gs)

/-- `c` is explicit, because `none` alone would leave it unknown. -/
def Seg.ofOption {α : Type} (c : S.Cat) : Option (Node S α c) → Seg S α (.opt c)
  | .none => .none
  | .some n => .some n

/-- `c` is explicit, because an empty list alone would leave it unknown. -/
def Seg.ofList {α : Type} (c : S.Cat) (ns : List (Node S α c)) : Seg S α (.many c) :=
  .many (Nodes.ofList ns)

/-- Segments whose kinds are known only from the list itself, as a macro builds them. -/
def Segs.ofList {α : Type} : (l : List ((k : SegK S.Cat) × Seg S α k)) → Segs S α (l.map (·.1))
  | [] => .nil
  | ⟨_, x⟩ :: l => .cons x (Segs.ofList l)

/-- One segment per node, each of the node's own category. -/
def Segs.ofFragment {α : Type} : (f : Fragment S α) → Segs S α (f.map fun n => .one n.1)
  | [] => .nil
  | ⟨_, n⟩ :: f => .cons (.one n) (Segs.ofFragment f)

def Frag.ofList {α : Type} : Fragment S α → Frag S α
  | [] => .nil
  | ⟨_, n⟩ :: ns => .cons n (Frag.ofList ns)

def Segs.append {α : Type} {ks ls : List (SegK S.Cat)} :
    Segs S α ks → Segs S α ls → Segs S α (ks ++ ls)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (Segs.append xs ys)

/-- `segs![a, b]` is `Segs.cons a (Segs.cons b Segs.nil)`. -/
syntax "segs![" term,* "]" : term
macro_rules
  | `(segs![]) => `(Segs.nil)
  | `(segs![$x]) => `(Segs.cons $x Segs.nil)
  | `(segs![$x, $xs,*]) => `(Segs.cons $x segs![$xs,*])

section Map

variable {α β : Type}

mutual
def Node.map (f : α → β) {c : S.Cat} : Node S α c → Node S β c
  | .text s => .text s
  | .ws s h => .ws s h
  | .verbatim s => .verbatim s
  | .elem e c p segs hc ok => .elem e c (f p) (Segs.map f segs) hc ok
  | .unchecked ns name c p ch h => .unchecked ns name c (f p) (Frag.map f ch) h
  | .widen n h => .widen (Node.map f n) h
def Nodes.map (f : α → β) {c : S.Cat} : Nodes S α c → Nodes S β c
  | .nil => .nil
  | .cons n ns => .cons (Node.map f n) (Nodes.map f ns)
def Groups.map (f : α → β) {ks : List (SegK S.Cat)} : Groups S α ks → Groups S β ks
  | .nil => .nil
  | .cons g gs => .cons (Segs.map f g) (Groups.map f gs)
def Seg.map (f : α → β) {k : SegK S.Cat} : Seg S α k → Seg S β k
  | .one n => .one (Node.map f n)
  | .none => .none
  | .some n => .some (Node.map f n)
  | .many ns => .many (Nodes.map f ns)
  | .many1 n ns => .many1 (Node.map f n) (Nodes.map f ns)
  | .groups gs => .groups (Groups.map f gs)
  | .inl xs => .inl (Segs.map f xs)
  | .inr xs => .inr (Segs.map f xs)
def Segs.map (f : α → β) {ks : List (SegK S.Cat)} : Segs S α ks → Segs S β ks
  | .nil => .nil
  | .cons x xs => .cons (Seg.map f x) (Segs.map f xs)
def Frag.map (f : α → β) : Frag S α → Frag S β
  | .nil => .nil
  | .cons n fr => .cons (Node.map f n) (Frag.map f fr)
end

mutual
theorem Node.map_id {c : S.Cat} : (n : Node S α c) → Node.map id n = n
  | .text _ | .ws _ _ | .verbatim _ => rfl
  | .elem _ _ _ segs _ _ => by simp only [Node.map, Segs.map_id segs]; rfl
  | .unchecked _ _ _ _ ch _ => by simp only [Node.map, Frag.map_id ch]; rfl
  | .widen n _ => by simp only [Node.map, Node.map_id n]
theorem Nodes.map_id {c : S.Cat} : (ns : Nodes S α c) → Nodes.map id ns = ns
  | .nil => rfl
  | .cons n ns => by simp only [Nodes.map, Node.map_id n, Nodes.map_id ns]
theorem Groups.map_id {ks : List (SegK S.Cat)} : (gs : Groups S α ks) → Groups.map id gs = gs
  | .nil => rfl
  | .cons g gs => by simp only [Groups.map, Segs.map_id g, Groups.map_id gs]
theorem Seg.map_id {k : SegK S.Cat} : (x : Seg S α k) → Seg.map id x = x
  | .one n | .some n => by simp only [Seg.map, Node.map_id n]
  | .none => rfl
  | .many ns => by simp only [Seg.map, Nodes.map_id ns]
  | .many1 n ns => by simp only [Seg.map, Node.map_id n, Nodes.map_id ns]
  | .groups gs => by simp only [Seg.map, Groups.map_id gs]
  | .inl xs | .inr xs => by simp only [Seg.map, Segs.map_id xs]
theorem Segs.map_id {ks : List (SegK S.Cat)} : (xs : Segs S α ks) → Segs.map id xs = xs
  | .nil => rfl
  | .cons x xs => by simp only [Segs.map, Seg.map_id x, Segs.map_id xs]
theorem Frag.map_id : (fr : Frag S α) → Frag.map id fr = fr
  | .nil => rfl
  | .cons n fr => by simp only [Frag.map, Node.map_id n, Frag.map_id fr]
end

variable {γ : Type} (f : α → β) (g : β → γ)

mutual
theorem Node.map_comp {c : S.Cat} : (n : Node S α c) → Node.map (g ∘ f) n = Node.map g (Node.map f n)
  | .text _ | .ws _ _ | .verbatim _ => rfl
  | .elem _ _ _ segs _ _ => by simp only [Node.map, Segs.map_comp segs]; rfl
  | .unchecked _ _ _ _ ch _ => by simp only [Node.map, Frag.map_comp ch]; rfl
  | .widen n _ => by simp only [Node.map, Node.map_comp n]
theorem Nodes.map_comp {c : S.Cat} :
    (ns : Nodes S α c) → Nodes.map (g ∘ f) ns = Nodes.map g (Nodes.map f ns)
  | .nil => rfl
  | .cons n ns => by simp only [Nodes.map, Node.map_comp n, Nodes.map_comp ns]
theorem Groups.map_comp {ks : List (SegK S.Cat)} :
    (gs : Groups S α ks) → Groups.map (g ∘ f) gs = Groups.map g (Groups.map f gs)
  | .nil => rfl
  | .cons x gs => by simp only [Groups.map, Segs.map_comp x, Groups.map_comp gs]
theorem Seg.map_comp {k : SegK S.Cat} : (x : Seg S α k) → Seg.map (g ∘ f) x = Seg.map g (Seg.map f x)
  | .one n | .some n => by simp only [Seg.map, Node.map_comp n]
  | .none => rfl
  | .many ns => by simp only [Seg.map, Nodes.map_comp ns]
  | .many1 n ns => by simp only [Seg.map, Node.map_comp n, Nodes.map_comp ns]
  | .groups gs => by simp only [Seg.map, Groups.map_comp gs]
  | .inl xs | .inr xs => by simp only [Seg.map, Segs.map_comp xs]
theorem Segs.map_comp {ks : List (SegK S.Cat)} :
    (xs : Segs S α ks) → Segs.map (g ∘ f) xs = Segs.map g (Segs.map f xs)
  | .nil => rfl
  | .cons x xs => by simp only [Segs.map, Seg.map_comp x, Segs.map_comp xs]
theorem Frag.map_comp : (fr : Frag S α) → Frag.map (g ∘ f) fr = Frag.map g (Frag.map f fr)
  | .nil => rfl
  | .cons n fr => by simp only [Frag.map, Node.map_comp n, Frag.map_comp fr]
end

end Map

variable (S) in
/-- `Node` with the payload last, so that it is a `Functor`. -/
abbrev NodeF (c : S.Cat) (α : Type) : Type := Node S α c

instance {c : S.Cat} : Functor (NodeF S c) where
  map f n := Node.map f n

instance {c : S.Cat} : LawfulFunctor (NodeF S c) where
  map_const := rfl
  id_map := Node.map_id
  comp_map f g := Node.map_comp f g

namespace Vocabulary

variable (V : Vocabulary) {α : Type}

/-- `Node.elem` with the vocabulary given, so that dotted names in its arguments resolve. -/
abbrev elem (e : V.Elem) (c : V.Cat) (p : α) {ks : List (SegK V.Cat)} (segs : Segs V.sig α ks)
    (hc : c ∈ V.cats e := by decide +kernel) (ok : V.Admits e c ks := by admits) :
    Node V.sig α c :=
  .elem e c p segs hc ok

/-- `Node.unchecked` with the vocabulary given. -/
abbrev unchecked (ns : Namespace) (name : String) (c : V.Cat) (p : α) (children : Frag V.sig α)
    (hname : ns.validName name = true := by decide +kernel) : Node V.sig α c :=
  .unchecked ns name c p children hname

/-- `Node.ws` with the vocabulary given. -/
abbrev whitespace (s : String) (h : isWhitespace s = true := by decide +kernel) :
    Node V.sig α V.ws :=
  .ws s h

/-- `Node.widen` with the vocabulary given. -/
abbrev widen {c d : V.Cat} (n : Node V.sig α c) (h : V.widens c d = true := by decide +kernel) :
    Node V.sig α d :=
  .widen n h

end Vocabulary

end HtmlModel
