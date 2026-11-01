/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Engine.Node

@[expose] public section

namespace HtmlModel

open Regular

variable (S : Signature)

/-- A node with its typing erased. An element keeps the category it was checked as, which says
which of its element's specs it was checked against. -/
inductive Tree (α : Type) where
  | text (s : String)
  | verbatim (c : S.Cat) (s : String)
  | elem (e : S.Elem) (c : S.Cat) (p : α) (children : List (Tree α))
  | unchecked (ns : Namespace) (name : String) (c : S.Cat) (p : α) (children : List (Tree α))

variable {S} {α β : Type}

namespace Tree

def cat : Tree S α → S.Cat
  | .text _ => S.text
  | .verbatim c _ | .elem _ c _ _ | .unchecked _ _ c _ _ => c

/-- The namespace and name a renderer emits an element as. -/
def tag : Tree S α → Option (Namespace × String)
  | .elem e _ _ _ => some (S.ns e, S.name e)
  | .unchecked ns name _ _ _ => some (ns, name)
  | .text _ | .verbatim _ _ => none

section Letters

variable {V : Vocabulary}

/-- What a child contributes to the word its parent's grammar checks. Where whitespace is
admitted, whitespace-only text and anything of the whitespace category drop out; elsewhere,
whitespace-only text is whitespace. -/
def letter (ws : Bool) : Tree V.sig α → List V.Cat
  | .text s => if isWhitespace s then (if ws then [] else [V.ws]) else [V.text]
  | t => if V.drops ws t.cat then [] else [t.cat]

def letters (ws : Bool) (ts : List (Tree V.sig α)) : List V.Cat := ts.flatMap (letter ws)

@[simp] theorem letters_nil (ws : Bool) : letters ws ([] : List (Tree V.sig α)) = [] := rfl

@[simp] theorem letters_cons (ws : Bool) (t : Tree V.sig α) (ts : List (Tree V.sig α)) :
    letters ws (t :: ts) = letter ws t ++ letters ws ts := rfl

@[simp] theorem letters_append (ws : Bool) (ts us : List (Tree V.sig α)) :
    letters ws (ts ++ us) = letters ws ts ++ letters ws us := List.flatMap_append

end Letters

/-- Every element's children are in the language of its spec, and an unchecked element's name is
valid. An unchecked element's own children are not checked against anything, but theirs are. -/
inductive Valid {V : Vocabulary} : Tree V.sig α → Prop where
  | text {s : String} : Valid (.text s)
  | verbatim {c : V.Cat} {s : String} : Valid (.verbatim c s)
  | elem {e : V.Elem} {c : V.Cat} {p : α} {children : List (Tree V.sig α)} :
      c ∈ V.cats e →
      Matches V.widens (V.spec e c).grammar (letters (V.spec e c).ws children) →
      (∀ t ∈ children, Valid t) → Valid (.elem e c p children)
  | unchecked {ns : Namespace} {name : String} {c : V.Cat} {p : α}
      {children : List (Tree V.sig α)} :
      ns.validName name = true → (∀ t ∈ children, Valid t) →
      Valid (.unchecked ns name c p children)

mutual
def map (f : α → β) : Tree S α → Tree S β
  | .text s => .text s
  | .verbatim c s => .verbatim c s
  | .elem e c p ch => .elem e c (f p) (mapList f ch)
  | .unchecked ns name c p ch => .unchecked ns name c (f p) (mapList f ch)
def mapList (f : α → β) : List (Tree S α) → List (Tree S β)
  | [] => []
  | t :: ts => map f t :: mapList f ts
end

@[simp] theorem mapList_eq (f : α → β) (ts : List (Tree S α)) : mapList f ts = ts.map (map f) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [mapList, ih]

mutual
def hasUnchecked : Tree S α → Bool
  | .text _ | .verbatim _ _ => false
  | .elem _ _ _ ch => anyUnchecked ch
  | .unchecked .. => true
def anyUnchecked : List (Tree S α) → Bool
  | [] => false
  | t :: ts => hasUnchecked t || anyUnchecked ts
end

mutual
def hasVerbatim : Tree S α → Bool
  | .text _ => false
  | .verbatim _ _ => true
  | .elem _ _ _ ch | .unchecked _ _ _ _ ch => anyVerbatim ch
def anyVerbatim : List (Tree S α) → Bool
  | [] => false
  | t :: ts => hasVerbatim t || anyVerbatim ts
end

end Tree

section Erase

open Tree

mutual
def Node.erase {c : S.Cat} : Node S α c → Tree S α
  | .text s | .ws s _ => .text s
  | .verbatim s => .verbatim c s
  | .elem e c p segs _ _ => .elem e c p (Segs.erase segs)
  | .unchecked ns name c p ch _ => .unchecked ns name c p (Frag.erase ch)
  | .widen n _ => Node.erase n
def Nodes.erase {c : S.Cat} : Nodes S α c → List (Tree S α)
  | .nil => []
  | .cons n ns => Node.erase n :: Nodes.erase ns
def Groups.erase {ks : List (SegK S.Cat)} : Groups S α ks → List (Tree S α)
  | .nil => []
  | .cons g gs => Segs.erase g ++ Groups.erase gs
def Seg.erase {k : SegK S.Cat} : Seg S α k → List (Tree S α)
  | .one n | .some n => [Node.erase n]
  | .none => []
  | .many ns => Nodes.erase ns
  | .many1 n ns => Node.erase n :: Nodes.erase ns
  | .groups gs => Groups.erase gs
  | .inl xs | .inr xs => Segs.erase xs
def Segs.erase {ks : List (SegK S.Cat)} : Segs S α ks → List (Tree S α)
  | .nil => []
  | .cons x xs => Seg.erase x ++ Segs.erase xs
def Frag.erase : Frag S α → List (Tree S α)
  | .nil => []
  | .cons n fr => Node.erase n :: Frag.erase fr
end

/-- A fragment erases to a list of trees, one per node. -/
def Fragment.erase (f : Fragment S α) : List (Tree S α) := f.map (·.2.erase)

/-- Whether `n` contains an unchecked element, so that a consumer can refuse it. -/
def Node.hasUnchecked {c : S.Cat} (n : Node S α c) : Bool := n.erase.hasUnchecked

/-- Whether `n` contains verbatim markup, so that a consumer can refuse it. -/
def Node.hasVerbatim {c : S.Cat} (n : Node S α c) : Bool := n.erase.hasVerbatim

variable {V : Vocabulary}

/-- `w` is a word of `r` with each letter replaced by one that widens to it, which a grammar
accepting `r` accepts too, since widening is transitive. -/
def Below (r : Regex V.Cat) (w : List V.Cat) : Prop :=
  ∃ ps : List {p : V.Cat × V.Cat // V.widens p.1 p.2 = true},
    Matches (· == ·) r (ps.map (·.1.2)) ∧ w = ps.map (·.1.1)

namespace Below

theorem eps : Below (V := V) .eps [] := ⟨[], .eps, rfl⟩

theorem sym {l c : V.Cat} (h : V.widens l c = true) : Below (.sym c) [l] :=
  ⟨[⟨(l, c), h⟩], .sym (by simp), rfl⟩

theorem cat {r s : Regex V.Cat} {u v : List V.Cat} (hu : Below r u) (hv : Below s v) :
    Below (.cat r s) (u ++ v) := by
  obtain ⟨ps, hps, rfl⟩ := hu
  obtain ⟨qs, hqs, rfl⟩ := hv
  exact ⟨ps ++ qs, by simpa using Matches.cat hps hqs, by simp⟩

theorem altLeft {r s : Regex V.Cat} {w : List V.Cat} (h : Below r w) : Below (.alt r s) w :=
  let ⟨ps, hps, hw⟩ := h; ⟨ps, .altLeft hps, hw⟩

theorem altRight {r s : Regex V.Cat} {w : List V.Cat} (h : Below s w) : Below (.alt r s) w :=
  let ⟨ps, hps, hw⟩ := h; ⟨ps, .altRight hps, hw⟩

theorem starNil {r : Regex V.Cat} : Below (.star r) [] := ⟨[], .starNil, rfl⟩

/-- A part that may drop out entirely, as whitespace does. -/
theorem starCons {r : Regex V.Cat} {u v : List V.Cat} (hu : Below r u ∨ u = [])
    (hv : Below (.star r) v) : Below (.star r) (u ++ v) := by
  rcases hu with ⟨ps, hps, rfl⟩ | rfl
  · obtain ⟨qs, hqs, rfl⟩ := hv
    exact ⟨ps ++ qs, by simpa using Matches.starCons hps hqs, by simp⟩
  · exact hv

theorem accepted {g r : Regex V.Cat} {w : List V.Cat} (h : Accepts V.widens g r) (hw : Below r w) :
    Matches V.widens g w := by
  obtain ⟨ps, hps, rfl⟩ := hw
  have hg := Regex.matches_comap (m := V.widens) (f := fun p : {p : V.Cat × V.Cat // V.widens p.1 p.2 = true} => p.1.2) |>.2 (h _ hps)
  exact Regex.matches_comap.1 (hg.mono fun p _ hs => V.widens_trans p.2 hs)

end Below

theorem Vocabulary.drops_of_widens {ws : Bool} {c d : V.Cat} (h : V.widens c d = true)
    (hd : V.drops ws d = true) : V.drops ws c = true := by
  simp only [Vocabulary.drops, Bool.and_eq_true, beq_iff_eq] at *
  obtain ⟨hws, rfl⟩ := hd
  exact ⟨hws, V.eq_ws_of_widens h⟩

/-- A node contributes a category that widens to its own to its parent's word, unless it is
whitespace that drops out where whitespace is admitted. -/
theorem Node.letter_erase (ws : Bool) {c : V.Cat} : (n : Node V.sig α c) →
    (letter ws n.erase = [] ∧ ws = true ∧ V.widens V.ws c = true) ∨
      ∃ l, letter ws n.erase = [l] ∧ V.widens l c = true ∧ V.drops ws c = false
  | .text s => by
    by_cases h : isWhitespace s = true
    · cases ws
      · exact .inr ⟨V.ws, by simp [Node.erase, letter, h], V.ws_widens_text, rfl⟩
      · exact .inl ⟨by simp [Node.erase, letter, h], rfl, V.ws_widens_text⟩
    · exact .inr ⟨V.text, by simp [Node.erase, letter, h], V.widens_refl _,
        by simp [Vocabulary.drops, V.text_ne_ws]⟩
  | .ws s h => by
    cases ws
    · exact .inr ⟨V.ws, by simp [Node.erase, letter, h], V.widens_refl _, rfl⟩
    · exact .inl ⟨by simp [Node.erase, letter, h], rfl, V.widens_refl _⟩
  | .verbatim _ | .elem .. | .unchecked .. => by
    cases hd : V.drops ws c
    · exact .inr ⟨c, by simp [Node.erase, letter, Tree.cat, hd], V.widens_refl _, rfl⟩
    · simp only [Vocabulary.drops, Bool.and_eq_true, beq_iff_eq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact .inl ⟨by simp [Node.erase, letter, Tree.cat, Vocabulary.drops], rfl, V.widens_refl _⟩
  | .widen n h => by
    rcases Node.letter_erase ws n with ⟨hl, hws, hw⟩ | ⟨l, hl, hw, hd⟩
    · exact .inl ⟨hl, hws, V.widens_trans hw h⟩
    · refine .inr ⟨l, hl, V.widens_trans hw h, ?_⟩
      cases hd' : V.drops ws _
      · rfl
      · simp [V.drops_of_widens h hd'] at hd

private theorem below_letter (ws : Bool) {c : V.Cat} (n : Node V.sig α c) :
    Below (V.letter ws c) (letter ws n.erase) := by
  unfold Vocabulary.letter
  rcases n.letter_erase ws with ⟨h, rfl, hw⟩ | ⟨l, h, hw, hd⟩ <;> rw [h]
  · split
    · exact Below.eps
    · simp only [hw, Bool.and_self, ↓reduceIte]
      exact Below.altLeft Below.eps
  · simp only [hd, Bool.false_eq_true, ↓reduceIte]
    split
    · exact Below.altRight (Below.sym hw)
    · exact Below.sym hw

private theorem below_opt (ws : Bool) {c : V.Cat} (n : Node V.sig α c) :
    Below (if V.drops ws c then .eps else Shape.opt c) (letter ws n.erase) := by
  rcases n.letter_erase ws with ⟨h, -⟩ | ⟨l, h, hw, hd⟩ <;> rw [h]
  · split
    · exact Below.eps
    · exact Below.altLeft Below.eps
  · simp only [hd, Bool.false_eq_true, ↓reduceIte]
    exact Below.altRight (Below.sym hw)

private theorem Nodes.letters_drop (ws : Bool) {c : V.Cat} (hd : V.drops ws c = true) :
    (ns : Nodes V.sig α c) → letters ws (Nodes.erase ns) = []
  | .nil => rfl
  | .cons n ns => by
    simp only [Nodes.erase, letters_cons, Nodes.letters_drop ws hd ns, List.append_nil]
    rcases n.letter_erase ws with ⟨h, -⟩ | ⟨_, -, -, hd'⟩
    · exact h
    · simp [hd] at hd'

private theorem Nodes.below_erase (ws : Bool) {c : V.Cat} :
    (ns : Nodes V.sig α c) → Below (Shape.many c) (letters ws (Nodes.erase ns))
  | .nil => Below.starNil
  | .cons n ns => by
    simp only [Nodes.erase, letters_cons]
    refine Below.starCons ?_ (Nodes.below_erase ws ns)
    rcases n.letter_erase ws with ⟨h, -⟩ | ⟨l, h, hw, -⟩ <;> rw [h]
    · exact .inr rfl
    · exact .inl (Below.sym hw)

private theorem below_many (ws : Bool) {c : V.Cat} (ns : Nodes V.sig α c) :
    Below (if V.drops ws c then .eps else Shape.many c) (letters ws (Nodes.erase ns)) := by
  split
  · rw [Nodes.letters_drop ws ‹_› ns]
    exact Below.eps
  · exact Nodes.below_erase ws ns

private theorem below_many1 (ws : Bool) {c : V.Cat} (n : Node V.sig α c) (ns : Nodes V.sig α c) :
    Below (V.letters1 ws c) (letters ws (Nodes.erase (.cons n ns))) := by
  unfold Vocabulary.letters1
  split
  · rw [Nodes.letters_drop ws ‹_› (.cons n ns)]
    exact Below.eps
  · split
    · exact Nodes.below_erase ws (.cons n ns)
    · rename_i hne
      rcases n.letter_erase ws with ⟨-, rfl, hw⟩ | ⟨l, h, hw, -⟩
      · simp [hw] at hne
      · simp only [Nodes.erase, letters_cons, h, Shape.many1, Regex.plus]
        exact Below.cat (Below.sym hw) (Nodes.below_erase ws ns)

mutual
private theorem Groups.below_erase (ws : Bool) {ks : List (SegK V.Cat)} :
    (gs : Groups V.sig α ks) → Below (.star (V.shape ws ks)) (letters ws (Groups.erase gs))
  | .nil => Below.starNil
  | .cons g gs => by
    simp only [Groups.erase, letters_append]
    exact Below.starCons (.inl (Segs.below_erase ws g)) (Groups.below_erase ws gs)
private theorem Seg.below_erase (ws : Bool) {k : SegK V.Cat} :
    (x : Seg V.sig α k) → Below (V.segShape ws k) (letters ws (Seg.erase x))
  | .one n => by simpa [Seg.erase, Vocabulary.segShape] using below_letter ws n
  | .none => by
    simp only [Vocabulary.segShape, Seg.erase, letters_nil]
    split
    · exact Below.eps
    · exact Below.altLeft Below.eps
  | .some n => by simpa [Seg.erase, Vocabulary.segShape] using below_opt ws n
  | .many ns => below_many ws ns
  | .many1 n ns => below_many1 ws n ns
  | .groups gs => Groups.below_erase ws gs
  | .inl xs => Below.altLeft (Segs.below_erase ws xs)
  | .inr xs => Below.altRight (Segs.below_erase ws xs)
private theorem Segs.below_erase (ws : Bool) {ks : List (SegK V.Cat)} :
    (xs : Segs V.sig α ks) → Below (V.shape ws ks) (letters ws (Segs.erase xs))
  | .nil => Below.eps
  | .cons x xs => by
    simp only [Segs.erase, letters_append, Vocabulary.shape]
    exact Below.cat (Seg.below_erase ws x) (Segs.below_erase ws xs)
end

mutual
/-- **Erasure preserves validity:** a typed node erases to a tree valid by `Tree.Valid` alone,
so a consumer of the erased tree can rely on it without the typed one. -/
theorem Node.valid_erase {c : V.Cat} : (n : Node V.sig α c) → n.erase.Valid
  | .text _ | .ws _ _ => .text
  | .verbatim _ => .verbatim
  | .elem _ _ _ segs hc ok =>
    .elem hc (Below.accepted ok (Segs.below_erase _ segs)) (Segs.valid_erase segs)
  | .unchecked _ _ _ _ ch h => .unchecked h (Frag.valid_erase ch)
  | .widen n _ => Node.valid_erase n
theorem Nodes.valid_erase {c : V.Cat} : (ns : Nodes V.sig α c) → ∀ t ∈ Nodes.erase ns, t.Valid
  | .nil => nofun
  | .cons n ns => by
    simp only [Nodes.erase, List.mem_cons, forall_eq_or_imp]
    exact ⟨n.valid_erase, Nodes.valid_erase ns⟩
theorem Groups.valid_erase {ks : List (SegK V.Cat)} :
    (gs : Groups V.sig α ks) → ∀ t ∈ Groups.erase gs, t.Valid
  | .nil => nofun
  | .cons g gs => by
    simp only [Groups.erase, List.mem_append]
    rintro t (h | h)
    · exact Segs.valid_erase g t h
    · exact Groups.valid_erase gs t h
theorem Seg.valid_erase {k : SegK V.Cat} : (x : Seg V.sig α k) → ∀ t ∈ Seg.erase x, t.Valid
  | .one n | .some n => by simp only [Seg.erase, List.mem_singleton]; rintro t rfl; exact n.valid_erase
  | .none => nofun
  | .many ns => Nodes.valid_erase ns
  | .many1 n ns => by
    simp only [Seg.erase, List.mem_cons, forall_eq_or_imp]
    exact ⟨n.valid_erase, Nodes.valid_erase ns⟩
  | .groups gs => Groups.valid_erase gs
  | .inl xs | .inr xs => Segs.valid_erase xs
theorem Segs.valid_erase {ks : List (SegK V.Cat)} :
    (xs : Segs V.sig α ks) → ∀ t ∈ Segs.erase xs, t.Valid
  | .nil => nofun
  | .cons x xs => by
    simp only [Segs.erase, List.mem_append]
    rintro t (h | h)
    · exact Seg.valid_erase x t h
    · exact Segs.valid_erase xs t h
theorem Frag.valid_erase : (fr : Frag V.sig α) → ∀ t ∈ Frag.erase fr, t.Valid
  | .nil => nofun
  | .cons n fr => by
    simp only [Frag.erase, List.mem_cons, forall_eq_or_imp]
    exact ⟨n.valid_erase, Frag.valid_erase fr⟩
end

theorem Fragment.valid_erase (f : Fragment V.sig α) : ∀ t ∈ Fragment.erase f, t.Valid := by
  simp only [Fragment.erase, List.mem_map]
  rintro t ⟨⟨_, n⟩, -, rfl⟩
  exact n.valid_erase

variable (f : α → β)

mutual
/-- **The payload map commutes with erasure.** -/
theorem Node.erase_map {c : S.Cat} : (n : Node S α c) → (Node.map f n).erase = n.erase.map f
  | .text _ | .ws _ _ | .verbatim _ => rfl
  | .elem _ _ _ segs _ _ => by
    simp only [Node.map, Node.erase, Tree.map, mapList_eq, Segs.erase_map segs]
  | .unchecked _ _ _ _ ch _ => by
    simp only [Node.map, Node.erase, Tree.map, mapList_eq, Frag.erase_map ch]
  | .widen n _ => by simp only [Node.map, Node.erase, Node.erase_map n]
theorem Nodes.erase_map {c : S.Cat} :
    (ns : Nodes S α c) → Nodes.erase (Nodes.map f ns) = (Nodes.erase ns).map (Tree.map f)
  | .nil => rfl
  | .cons n ns => by simp only [Nodes.map, Nodes.erase, List.map_cons, n.erase_map, Nodes.erase_map ns]
theorem Groups.erase_map {ks : List (SegK S.Cat)} :
    (gs : Groups S α ks) → Groups.erase (Groups.map f gs) = (Groups.erase gs).map (Tree.map f)
  | .nil => rfl
  | .cons g gs => by
    simp only [Groups.map, Groups.erase, List.map_append, Segs.erase_map g, Groups.erase_map gs]
theorem Seg.erase_map {k : SegK S.Cat} :
    (x : Seg S α k) → Seg.erase (Seg.map f x) = (Seg.erase x).map (Tree.map f)
  | .one n | .some n => by simp only [Seg.map, Seg.erase, List.map_cons, List.map_nil, n.erase_map]
  | .none => rfl
  | .many ns => Nodes.erase_map ns
  | .many1 n ns => by
    simp only [Seg.map, Seg.erase, List.map_cons, n.erase_map, Nodes.erase_map ns]
  | .groups gs => Groups.erase_map gs
  | .inl xs | .inr xs => Segs.erase_map xs
theorem Segs.erase_map {ks : List (SegK S.Cat)} :
    (xs : Segs S α ks) → Segs.erase (Segs.map f xs) = (Segs.erase xs).map (Tree.map f)
  | .nil => rfl
  | .cons x xs => by
    simp only [Segs.map, Segs.erase, List.map_append, Seg.erase_map x, Segs.erase_map xs]
theorem Frag.erase_map :
    (fr : Frag S α) → Frag.erase (Frag.map f fr) = (Frag.erase fr).map (Tree.map f)
  | .nil => rfl
  | .cons n fr => by simp only [Frag.map, Frag.erase, List.map_cons, n.erase_map, Frag.erase_map fr]
end

end Erase

end HtmlModel
