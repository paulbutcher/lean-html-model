/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel

@[expose] public section

namespace HtmlModelTests

open HtmlModel Web

abbrev N := Web.Node Unit

/-- An HTML element with no payload. -/
abbrev el (e : Html.Elem) (c : Html.Cat) {ks : List (SegK Cat)} (segs : Segs vocab Unit ks)
    (hc : Cat.html c ∈ vocab.cats (.html e) := by decide +kernel)
    (ok : vocab.Admits (.html e) (.html c) ks := by admits) : N (.html c) :=
  Web.elem (.html e) (.html c) () segs hc ok

def txt (s : String) : N .text := .text s

def nodes {c : Html.Cat} (ns : List (N (.html c))) : Seg vocab Unit (.many (.html c)) :=
  .many (Nodes.ofList ns)

end HtmlModelTests
