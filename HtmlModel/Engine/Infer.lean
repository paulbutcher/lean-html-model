/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Engine.Vocabulary

@[expose] public section

namespace HtmlModel

open Regular

namespace Vocabulary

variable (V : Vocabulary)

/-- The categories element `e` may take with children `ks` inside a parent whose grammar is
`parent`: those whose spec admits the children and which widen to a symbol of the parent. -/
def candidates (e : V.Elem) (ks : List (SegK V.Cat)) (parent : Regex V.Cat) : List V.Cat :=
  (V.cats e).filter fun c => decide (V.Admits e c ks) && parent.letters.any (V.widens c)

/-- The least candidate, which widens to every other, so that a macro can place an element where
no type says which category it takes: `a` takes phrasing or flow from its children, `link`
metadata or phrasing from its parent. `none` if there is no candidate, or no least one. -/
def infer (e : V.Elem) (ks : List (SegK V.Cat)) (parent : Regex V.Cat) : Option V.Cat :=
  let cs := V.candidates e ks parent
  cs.find? fun c => cs.all (V.widens c)

theorem infer_spec {e : V.Elem} {ks : List (SegK V.Cat)} {parent : Regex V.Cat} {c : V.Cat}
    (h : V.infer e ks parent = some c) : c ∈ V.cats e ∧ V.Admits e c ks := by
  have hc := List.mem_of_find?_eq_some h
  simp only [candidates, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨hc.1, hc.2.1⟩

end Vocabulary

end HtmlModel
