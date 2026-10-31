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

/-- An SVG element taking its own category, with no payload. -/
abbrev sv (e : Svg.Elem) {ks : List (SegK Cat)} (segs : Segs vocab Unit ks)
    (hc : Cat.svg (.el e) ∈ vocab.cats (.svg e) := by decide +kernel)
    (ok : vocab.Admits (.svg e) (.svg (.el e)) ks := by admits) : N (.svg (.el e)) :=
  Web.elem (.svg e) (.svg (.el e)) () segs hc ok

/-- An SVG `a`, which takes the category of the content model it stands in. -/
abbrev sa (c : Svg.Cat) {ks : List (SegK Cat)} (segs : Segs vocab Unit ks)
    (hc : Cat.svg c ∈ vocab.cats (.svg .a) := by decide +kernel)
    (ok : vocab.Admits (.svg .a) (.svg c) ks := by admits) : N (.svg c) :=
  Web.elem (.svg .a) (.svg c) () segs hc ok

/-- An `svg` element standing in HTML phrasing content. -/
abbrev inlineSvg {ks : List (SegK Cat)} (segs : Segs vocab Unit ks)
    (ok : vocab.Admits (.svg .svg) (.html .phrasing) ks := by admits) : N (.html .phrasing) :=
  Web.elem (.svg .svg) (.html .phrasing) () segs (by decide +kernel) ok

def txt (s : String) : N .text := .text s

def nodes {c : Html.Cat} (ns : List (N (.html c))) : Seg vocab Unit (.many (.html c)) :=
  .many (Nodes.ofList ns)

end HtmlModelTests
