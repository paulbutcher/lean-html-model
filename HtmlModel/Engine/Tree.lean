/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Engine.Node

@[expose] public section

namespace HtmlModel

open Regular

variable (V : Vocabulary)

/-- A node with its typing erased. An element keeps its category, which says which of its
element's specs it was checked against. -/
inductive Tree (α : Type) where
  | text (s : String)
  | verbatim (c : V.Cat) (s : String)
  | elem (e : V.Elem) (c : V.Cat) (p : α) (children : List (Tree α))
  | unchecked (ns : Namespace) (name : String) (c : V.Cat) (p : α) (children : List (Tree α))

variable {V} {α β : Type}

namespace Tree

def cat : Tree V α → V.Cat
  | .text _ => V.text
  | .verbatim c _ | .elem _ c _ _ | .unchecked _ _ c _ _ => c

/-- The namespace and name a renderer emits an element as. -/
def tag : Tree V α → Option (Namespace × String)
  | .elem e _ _ _ => some (V.ns e, V.name e)
  | .unchecked ns name _ _ _ => some (ns, name)
  | .text _ | .verbatim _ _ => none

/-- What a child contributes to the word its parent's grammar checks. -/
def letter (ws : Bool) : Tree V α → List V.Cat
  | .text s => if ws && isWhitespace s then [] else [V.text]
  | t => [t.cat]

def letters (ws : Bool) (ts : List (Tree V α)) : List V.Cat := ts.flatMap (letter ws)

@[simp] theorem letters_nil (ws : Bool) : letters ws ([] : List (Tree V α)) = [] := rfl

@[simp] theorem letters_cons (ws : Bool) (t : Tree V α) (ts : List (Tree V α)) :
    letters ws (t :: ts) = letter ws t ++ letters ws ts := rfl

@[simp] theorem letters_append (ws : Bool) (ts us : List (Tree V α)) :
    letters ws (ts ++ us) = letters ws ts ++ letters ws us := List.flatMap_append

/-- Every element's children are in the language of its spec, and an unchecked element's name is
valid. An unchecked element's own children are not checked against anything, but theirs are. -/
inductive Valid : Tree V α → Prop where
  | text {s : String} : Valid (.text s)
  | verbatim {c : V.Cat} {s : String} : Valid (.verbatim c s)
  | elem {e : V.Elem} {c : V.Cat} {p : α} {children : List (Tree V α)} :
      c ∈ V.cats e →
      Matches V.widens (V.spec e c).grammar (letters (V.spec e c).ws children) →
      (∀ t ∈ children, Valid t) → Valid (.elem e c p children)
  | unchecked {ns : Namespace} {name : String} {c : V.Cat} {p : α}
      {children : List (Tree V α)} :
      ns.validName name = true → (∀ t ∈ children, Valid t) →
      Valid (.unchecked ns name c p children)

mutual
def map (f : α → β) : Tree V α → Tree V β
  | .text s => .text s
  | .verbatim c s => .verbatim c s
  | .elem e c p ch => .elem e c (f p) (mapList f ch)
  | .unchecked ns name c p ch => .unchecked ns name c (f p) (mapList f ch)
def mapList (f : α → β) : List (Tree V α) → List (Tree V β)
  | [] => []
  | t :: ts => map f t :: mapList f ts
end

@[simp] theorem mapList_eq (f : α → β) (ts : List (Tree V α)) : mapList f ts = ts.map (map f) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [mapList, ih]

mutual
def hasUnchecked : Tree V α → Bool
  | .text _ | .verbatim _ _ => false
  | .elem _ _ _ ch => anyUnchecked ch
  | .unchecked .. => true
def anyUnchecked : List (Tree V α) → Bool
  | [] => false
  | t :: ts => hasUnchecked t || anyUnchecked ts
end

mutual
def hasVerbatim : Tree V α → Bool
  | .text _ => false
  | .verbatim _ _ => true
  | .elem _ _ _ ch | .unchecked _ _ _ _ ch => anyVerbatim ch
def anyVerbatim : List (Tree V α) → Bool
  | [] => false
  | t :: ts => hasVerbatim t || anyVerbatim ts
end

end Tree

section Erase

open Tree

mutual
def Node.erase {c : V.Cat} : Node V α c → Tree V α
  | .text s => .text s
  | .verbatim s => .verbatim c s
  | .elem e c p segs _ _ => .elem e c p (Segs.erase segs)
  | .unchecked ns name c p ch _ => .unchecked ns name c p (Frag.erase ch)
def Nodes.erase {c : V.Cat} : Nodes V α c → List (Tree V α)
  | .nil => []
  | .cons n ns => Node.erase n :: Nodes.erase ns
def Groups.erase {ks : List (SegK V.Cat)} : Groups V α ks → List (Tree V α)
  | .nil => []
  | .cons g gs => Segs.erase g ++ Groups.erase gs
def Seg.erase {k : SegK V.Cat} : Seg V α k → List (Tree V α)
  | .one n | .some n => [Node.erase n]
  | .none => []
  | .many ns => Nodes.erase ns
  | .many1 n ns => Node.erase n :: Nodes.erase ns
  | .groups gs => Groups.erase gs
  | .inl xs | .inr xs => Segs.erase xs
  | .ws s _ => [.text s]
def Segs.erase {ks : List (SegK V.Cat)} : Segs V α ks → List (Tree V α)
  | .nil => []
  | .cons x xs => Seg.erase x ++ Segs.erase xs
def Frag.erase : Frag V α → List (Tree V α)
  | .nil => []
  | .cons n fr => Node.erase n :: Frag.erase fr
end

/-- A fragment erases to a list of trees, one per node. -/
def Fragment.erase (f : Fragment V α) : List (Tree V α) := f.map (·.2.erase)

/-- Whether `n` contains an unchecked element, so that a consumer can refuse it. -/
def Node.hasUnchecked {c : V.Cat} (n : Node V α c) : Bool := n.erase.hasUnchecked

/-- Whether `n` contains verbatim markup, so that a consumer can refuse it. -/
def Node.hasVerbatim {c : V.Cat} (n : Node V α c) : Bool := n.erase.hasVerbatim

theorem Node.cat_erase {c : V.Cat} (n : Node V α c) : n.erase.cat = c := by
  cases n <;> rfl

/-- A node contributes its category to its parent's word, unless it is whitespace that drops out
where whitespace is admitted. -/
theorem Node.letter_erase (ws : Bool) {c : V.Cat} (n : Node V α c) :
    letter ws n.erase = [c] ∨ (letter ws n.erase = [] ∧ ws = true ∧ c = V.text) := by
  cases n with
  | text s =>
    simp only [Node.erase, letter]
    by_cases h : (ws && isWhitespace s) = true
    · simp only [Bool.and_eq_true] at h
      simp [h]
    · simp [h]
  | _ => left; rfl

private theorem matches_sym_self (c : V.Cat) : Matches (· == ·) (.sym c) [c] :=
  .sym (by simp)

private theorem matches_letter (ws : Bool) {c : V.Cat} (n : Node V α c) :
    Matches (· == ·) (V.letter ws c) (letter ws n.erase) := by
  unfold Vocabulary.letter
  rcases n.letter_erase ws with h | ⟨h, rfl, rfl⟩
  · rw [h]
    split
    · exact .altRight (matches_sym_self c)
    · exact matches_sym_self c
  · rw [h]
    simp only [Bool.true_and, beq_self_eq_true, ↓reduceIte]
    exact .altLeft .eps

private theorem matches_opt_letter (ws : Bool) {c : V.Cat} (n : Node V α c) :
    Matches (· == ·) (Shape.opt c) (letter ws n.erase) := by
  rcases n.letter_erase ws with h | ⟨h, -, -⟩ <;> rw [h]
  · exact .altRight (matches_sym_self c)
  · exact .altLeft .eps

private theorem matches_star_cons {r : Regex V.Cat} {u v : List V.Cat}
    (hu : Matches (· == ·) r u ∨ u = []) (hv : Matches (· == ·) (.star r) v) :
    Matches (· == ·) (.star r) (u ++ v) := by
  rcases hu with hu | rfl
  · exact .starCons hu hv
  · exact hv

mutual
private theorem Nodes.matches_erase (ws : Bool) {c : V.Cat} :
    (ns : Nodes V α c) → Matches (· == ·) (Shape.many c) (letters ws (Nodes.erase ns))
  | .nil => .starNil
  | .cons n ns => by
    simp only [Nodes.erase, letters_cons]
    refine matches_star_cons ?_ (Nodes.matches_erase ws ns)
    rcases n.letter_erase ws with h | ⟨h, -⟩ <;> rw [h]
    · exact .inl (matches_sym_self c)
    · exact .inr rfl
private theorem Groups.matches_erase (ws : Bool) {ks : List (SegK V.Cat)} :
    (gs : Groups V α ks) → Matches (· == ·) (.star (V.shape ws ks)) (letters ws (Groups.erase gs))
  | .nil => .starNil
  | .cons g gs => by
    simp only [Groups.erase, letters_append]
    exact .starCons (Segs.matches_erase ws g) (Groups.matches_erase ws gs)
private theorem Seg.matches_erase (ws : Bool) {k : SegK V.Cat} :
    (x : Seg V α k) → Matches (· == ·) (V.segShape ws k) (letters ws (Seg.erase x))
  | .one n => by simpa [Seg.erase, Vocabulary.segShape] using matches_letter ws n
  | .none => .altLeft .eps
  | .some n => by simpa [Seg.erase, Vocabulary.segShape] using matches_opt_letter ws n
  | .many ns => Nodes.matches_erase ws ns
  | .many1 n ns => by
    simp only [Vocabulary.segShape, Vocabulary.letters1]
    split
    · exact Nodes.matches_erase ws (.cons n ns)
    · rename_i hne
      rcases n.letter_erase ws with h | ⟨-, rfl, rfl⟩
      · simp only [Seg.erase, letters_cons, h, Shape.many1, Regex.plus]
        exact .cat (matches_sym_self _) (Nodes.matches_erase ws ns)
      · simp at hne
  | .groups gs => Groups.matches_erase ws gs
  | .inl xs => .altLeft (Segs.matches_erase ws xs)
  | .inr xs => .altRight (Segs.matches_erase ws xs)
  | .ws s h => by
    simp only [Seg.erase, letters_cons, letters_nil, List.append_nil, letter, h, Bool.and_true,
      Vocabulary.segShape]
    cases ws
    · exact matches_sym_self V.text
    · exact .eps
private theorem Segs.matches_erase (ws : Bool) {ks : List (SegK V.Cat)} :
    (xs : Segs V α ks) → Matches (· == ·) (V.shape ws ks) (letters ws (Segs.erase xs))
  | .nil => .eps
  | .cons x xs => by
    simp only [Segs.erase, letters_append, Vocabulary.shape]
    exact .cat (Seg.matches_erase ws x) (Segs.matches_erase ws xs)
end

mutual
/-- **Erasure preserves validity:** a typed node erases to a tree valid by `Tree.Valid` alone,
so a consumer of the erased tree can rely on it without the typed one. -/
theorem Node.valid_erase {c : V.Cat} : (n : Node V α c) → n.erase.Valid
  | .text _ => .text
  | .verbatim _ => .verbatim
  | .elem _ _ _ segs hc ok =>
    .elem hc (ok _ (Segs.matches_erase _ segs)) (Segs.valid_erase segs)
  | .unchecked _ _ _ _ ch h => .unchecked h (Frag.valid_erase ch)
theorem Nodes.valid_erase {c : V.Cat} : (ns : Nodes V α c) → ∀ t ∈ Nodes.erase ns, t.Valid
  | .nil => nofun
  | .cons n ns => by
    simp only [Nodes.erase, List.mem_cons, forall_eq_or_imp]
    exact ⟨n.valid_erase, Nodes.valid_erase ns⟩
theorem Groups.valid_erase {ks : List (SegK V.Cat)} :
    (gs : Groups V α ks) → ∀ t ∈ Groups.erase gs, t.Valid
  | .nil => nofun
  | .cons g gs => by
    simp only [Groups.erase, List.mem_append]
    rintro t (h | h)
    · exact Segs.valid_erase g t h
    · exact Groups.valid_erase gs t h
theorem Seg.valid_erase {k : SegK V.Cat} : (x : Seg V α k) → ∀ t ∈ Seg.erase x, t.Valid
  | .one n | .some n => by simp only [Seg.erase, List.mem_singleton]; rintro t rfl; exact n.valid_erase
  | .none => nofun
  | .many ns => Nodes.valid_erase ns
  | .many1 n ns => by
    simp only [Seg.erase, List.mem_cons, forall_eq_or_imp]
    exact ⟨n.valid_erase, Nodes.valid_erase ns⟩
  | .groups gs => Groups.valid_erase gs
  | .inl xs | .inr xs => Segs.valid_erase xs
  | .ws _ _ => by simp only [Seg.erase, List.mem_singleton]; rintro t rfl; exact .text
theorem Segs.valid_erase {ks : List (SegK V.Cat)} : (xs : Segs V α ks) → ∀ t ∈ Segs.erase xs, t.Valid
  | .nil => nofun
  | .cons x xs => by
    simp only [Segs.erase, List.mem_append]
    rintro t (h | h)
    · exact Seg.valid_erase x t h
    · exact Segs.valid_erase xs t h
theorem Frag.valid_erase : (fr : Frag V α) → ∀ t ∈ Frag.erase fr, t.Valid
  | .nil => nofun
  | .cons n fr => by
    simp only [Frag.erase, List.mem_cons, forall_eq_or_imp]
    exact ⟨n.valid_erase, Frag.valid_erase fr⟩
end

theorem Fragment.valid_erase (f : Fragment V α) : ∀ t ∈ Fragment.erase f, t.Valid := by
  simp only [Fragment.erase, List.mem_map]
  rintro t ⟨⟨_, n⟩, -, rfl⟩
  exact n.valid_erase

variable (f : α → β)

mutual
/-- **The payload map commutes with erasure.** -/
theorem Node.erase_map {c : V.Cat} : (n : Node V α c) → (Node.map f n).erase = n.erase.map f
  | .text _ | .verbatim _ => rfl
  | .elem _ _ _ segs _ _ => by
    simp only [Node.map, Node.erase, Tree.map, mapList_eq, Segs.erase_map segs]
  | .unchecked _ _ _ _ ch _ => by
    simp only [Node.map, Node.erase, Tree.map, mapList_eq, Frag.erase_map ch]
theorem Nodes.erase_map {c : V.Cat} :
    (ns : Nodes V α c) → Nodes.erase (Nodes.map f ns) = (Nodes.erase ns).map (Tree.map f)
  | .nil => rfl
  | .cons n ns => by simp only [Nodes.map, Nodes.erase, List.map_cons, n.erase_map, Nodes.erase_map ns]
theorem Groups.erase_map {ks : List (SegK V.Cat)} :
    (gs : Groups V α ks) → Groups.erase (Groups.map f gs) = (Groups.erase gs).map (Tree.map f)
  | .nil => rfl
  | .cons g gs => by
    simp only [Groups.map, Groups.erase, List.map_append, Segs.erase_map g, Groups.erase_map gs]
theorem Seg.erase_map {k : SegK V.Cat} :
    (x : Seg V α k) → Seg.erase (Seg.map f x) = (Seg.erase x).map (Tree.map f)
  | .one n | .some n => by simp only [Seg.map, Seg.erase, List.map_cons, List.map_nil, n.erase_map]
  | .none | .ws _ _ => rfl
  | .many ns => Nodes.erase_map ns
  | .many1 n ns => by
    simp only [Seg.map, Seg.erase, List.map_cons, n.erase_map, Nodes.erase_map ns]
  | .groups gs => Groups.erase_map gs
  | .inl xs | .inr xs => Segs.erase_map xs
theorem Segs.erase_map {ks : List (SegK V.Cat)} :
    (xs : Segs V α ks) → Segs.erase (Segs.map f xs) = (Segs.erase xs).map (Tree.map f)
  | .nil => rfl
  | .cons x xs => by
    simp only [Segs.map, Segs.erase, List.map_append, Seg.erase_map x, Segs.erase_map xs]
theorem Frag.erase_map :
    (fr : Frag V α) → Frag.erase (Frag.map f fr) = (Frag.erase fr).map (Tree.map f)
  | .nil => rfl
  | .cons n fr => by simp only [Frag.map, Frag.erase, List.map_cons, n.erase_map, Frag.erase_map fr]
end

end Erase

end HtmlModel
