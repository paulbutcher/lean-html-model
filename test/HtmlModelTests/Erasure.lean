/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModelTests.Helpers

namespace HtmlModelTests.Erasure

open HtmlModel Web

def page : N (.html .flow) :=
  el .div .flow segs![.one (ws "\n"), .one (el .p .paragraph segs![.one (txt "a < b")]),
    .one (el .ul .flow segs![nodes [el .li .listItem segs![]], .one (el .script .scriptSupporting segs![])])]

-- Erasure keeps every child, whitespace included, and each element's category.
example : page.erase.tag = some (.html, "div") := by decide +kernel
example : (match page.erase with | .elem _ c _ ch => (c, ch.length) | _ => (.text, 0)) = (.html .flow, 3) := by
  decide +kernel
example : (match page.erase with | .elem _ _ _ (.text s :: _) => s | _ => "") = "\n" := by decide +kernel
example : page.hasVerbatim = false ∧ page.hasUnchecked = false := by decide +kernel

-- A widened element keeps the category it was checked as.
example : (Web.widen (el .p .paragraph segs![]) : N (.html .flow)).erase.cat = .html .paragraph := by
  decide +kernel

-- Verbatim markup and unchecked elements are found at any depth.
def withVerbatim : N (.html .flow) :=
  el .div .flow segs![.one (el .p .paragraph segs![.one (.verbatim "<b>x</b>" : N (.html .phrasing))])]
example : withVerbatim.hasVerbatim = true ∧ withVerbatim.hasUnchecked = false := by decide +kernel

def withUnchecked : N (.html .flow) :=
  el .div .flow segs![.one (el .select .phrasing segs![.one (Web.unchecked .html "selectedcontent" (.html .selectChild) ()
    (Frag.ofList [⟨_, el .span .phrasing segs![]⟩]))])]
example : withUnchecked.hasUnchecked = true ∧ withUnchecked.hasVerbatim = false := by decide +kernel

-- An unchecked element's name must survive a round trip through an HTML parser.
/--
error: could not synthesize default value for parameter 'hname' using tactics
---
error: Tactic `decide` proved that the proposition
  Namespace.html.validName "selectedContent" = true
is false
-/
#guard_msgs in
example : N (.html .phrasing) := Web.unchecked .html "selectedContent" (.html .phrasing) () .nil

-- An unchecked element's children are checked as usual.
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <p> as Cat.html Html.Cat.paragraph does not admit its children: segment 1, of category Cat.html Html.Cat.flow, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .phrasing) :=
  Web.unchecked .html "fencedframe" (.html .phrasing) ()
    (Frag.ofList [⟨_, el .p .paragraph segs![.one (el .div .flow segs![])]⟩])

-- A custom element has the content model its vocabulary declares for it.
abbrev cards : Vocabulary := vocabWith [("my-card", [.html .flow], [(.html .flow, phrasingSpec)])]

def card : Elem := .custom "my-card" (by decide)

abbrev C (c : Cat) := HtmlModel.Node cards.sig Unit c

abbrev ce (e : Elem) (c : Cat) {ks : List (SegK Cat)} (segs : Segs cards.sig Unit ks)
    (hc : c ∈ cards.cats e := by decide +kernel) (ok : cards.Admits e c ks := by admits) : C c :=
  .elem e c () segs hc ok

example : C (.html .flow) :=
  ce card (.html .flow) segs![.one (.text "x"), .one (ce (.html .span) (.html .phrasing) segs![])]

/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <my-card> as Cat.html Html.Cat.flow does not admit its children: segment 1, of category Cat.html Html.Cat.paragraph, cannot follow the segments before it
-/
#guard_msgs in
example : C (.html .flow) := ce card (.html .flow) segs![.one (ce (.html .p) (.html .paragraph) segs![])]

-- Its nodes coerce as the default vocabulary's do.
example : List (C (.html .flow)) := [ce (.html .span) (.html .phrasing) segs![], (.text "x" : C .text)]

-- Undeclared, it has the standard's: transparent, as phrasing or flow content.
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <my-card> as Cat.html Html.Cat.phrasing does not admit its children: segment 1, of category Cat.html Html.Cat.paragraph, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .phrasing) := Web.elem card (.html .phrasing) () segs![.one (el .p .paragraph segs![])]

-- A fragment of any categories erases to a list of trees, as an htmx response of rows and an
-- out-of-band swap needs.
def response : Web.Fragment Unit :=
  [⟨_, el .tr .tableRow segs![]⟩, ⟨_, el .tr .tableRow segs![]⟩, ⟨_, el .div .flow segs![]⟩]
example : (Fragment.erase response).map Tree.cat = [.html .tableRow, .html .tableRow, .html .flow] := by
  decide +kernel

-- The payload map reaches every element and leaves the rest alone.
mutual
def payloads : Web.Tree Nat → List Nat
  | .elem _ _ p ch | .unchecked _ _ _ p ch => p :: payloadsAll ch
  | _ => []
def payloadsAll : List (Web.Tree Nat) → List Nat
  | [] => []
  | t :: ts => payloads t ++ payloadsAll ts
end

def numbered : Web.Node Nat (.html .flow) :=
  Web.elem (.html .div) (.html .flow) 1 segs![.one (Web.elem (.html .p) (.html .paragraph) 2 segs![.one (.text "x")]),
    .one (Web.elem (.html .hr) (.html .flow) 3 segs![])]

example : payloads numbered.erase = [1, 2, 3] := by decide +kernel
example : payloads (Node.map (· * 10) numbered).erase = [10, 20, 30] := by decide +kernel
example : payloads (Functor.map (f := NodeF vocab.sig (.html .flow)) (· + 1) numbered).erase = [2, 3, 4] := by
  decide +kernel

end HtmlModelTests.Erasure
