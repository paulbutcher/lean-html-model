/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModel
meta import HtmlModel

/-! The examples in the README, which must compile as they appear there. -/

namespace HtmlModelTests.Readme

open HtmlModel Web

/-- An HTML element with no payload. -/
abbrev el (e : Html.Elem) (c : Html.Cat) {ks : List (SegK Cat)} (segs : Segs vocab Unit ks)
    (hc : Cat.html c ∈ vocab.cats (.html e) := by decide +kernel)
    (ok : vocab.Admits (.html e) (.html c) ks := by admits) : Web.Node Unit (.html c) :=
  Web.elem (.html e) (.html c) () segs hc ok

def txt (s : String) : Web.Node Unit .text := .text s

/-- A list whose items are known only at run time, after inter-element whitespace. -/
def list (items : List String) : Web.Node Unit (.html .flow) :=
  el .ul .flow segs![.ws "\n",
    .many (Nodes.ofList (items.map fun i => el .li .listItem segs![.one (txt i)]))]

/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <p> as Cat.html Html.Cat.paragraph does not admit its children: segment 2, of category Cat.html Html.Cat.flow, cannot follow the segments before it
-/
#guard_msgs in
example : Web.Node Unit (.html .paragraph) :=
  el .p .paragraph segs![.one (txt "Hi"), .one (el .div .flow segs![])]

def picker : Web.Node Unit (.html .phrasing) :=
  el .select .phrasing segs![
    .one (Web.unchecked .html "selectedcontent" (.html .selectChild) () .nil),
    .one (el .option .option segs![.one (txt "A")])]

def rows : Web.Fragment Unit :=
  [⟨_, el .tr .tableRow segs![]⟩, ⟨_, el .tr .tableRow segs![]⟩, ⟨_, el .div .flow segs![]⟩]

example : (list ["a"]).erase.Valid := (list ["a"]).valid_erase

/-- info: some (HtmlModel.Namespace.html, "ul") -/
#guard_msgs in
#eval (list ["a", "b"]).erase.tag

/-- info: 3 -/
#guard_msgs in
#eval (Fragment.erase rows).length

/-- info: true -/
#guard_msgs in
#eval picker.hasUnchecked

end HtmlModelTests.Readme
