/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModelTests.Helpers

namespace HtmlModelTests.Mathml

open HtmlModel Web

def mn (s : String) : N (.mathml .expr) := mx .mn .expr segs![.one (txt s)]
def mi (s : String) : N (.mathml .expr) := mx .mi .expr segs![.one (txt s)]
def mo (s : String) : N (.mathml .expr) := mx .mo .expr segs![.one (txt s)]

-- `math` is phrasing content in HTML. After MathML Core's `mrow` example, "(1 + 2/3)^5".
example : N (.html .paragraph) :=
  el .p .paragraph segs![.one (txt "Thus "), .one (inlineMath segs![
    .one (mx .msup .expr segs![
      .one (mx .mrow .expr segs![.one (mo "("), .one (mn "1"), .one (mo "+"),
        .one (mx .mfrac .expr segs![.one (mn "2"), .one (ws " "), .one (mn "3")]), .one (mo ")")]),
      .one (mn "5")])])]

-- The fixed arities.
example : N (.mathml .expr) := mx .mroot .expr segs![.one (mx .msqrt .expr segs![.one (mi "x"), .one (mi "y")]), .one (mn "3")]
example : N (.mathml .expr) := mx .msubsup .expr segs![.one (mi "x"), .one (mn "1"), .one (mn "2")]
example : N (.mathml .expr) := mx .munderover .expr segs![.one (mo "∑"), .one (mi "i"), .one (mi "n")]
example : N (.mathml .expr) := mx .munder .expr segs![.one (mo "lim"), .one (mi "x")]
example : N (.mathml .expr) := mx .mover .expr segs![.one (mi "x"), .one (mo "^")]

-- After MathML Core's `mmultiscripts` example: a base, two pairs of postscripts, `mprescripts`,
-- and two pairs of prescripts, empty `mrow`s marking absent scripts.
example : N (.mathml .expr) :=
  mx .mmultiscripts .expr segs![.one (mn "1"), .one (mn "2"), .one (mn "3"), .one (mx .mrow .expr segs![]),
    .one (mn "5"), .one (mx .mprescripts .prescripts segs![]), .one (mn "6"), .one (mx .mrow .expr segs![]),
    .one (mn "8"), .one (mn "9")]

-- Pairs of scripts known only at run time.
example (pairs : List (String × String)) : N (.mathml .expr) :=
  mx .mmultiscripts .expr segs![.one (mi "R"), .groups (Groups.ofList (pairs.map fun (b, p) =>
    segs![.one (mi b), .one (mi p)]))]

-- Tables, and token elements holding HTML phrasing content.
example : N (.mathml .expr) :=
  mx .mtable .expr segs![.one (mx .mtr .row segs![.one (mx .mtd .cell segs![.one (mi "a")]),
    .one (mx .mtd .cell segs![.one (mi "b")])])]
example : N (.mathml .expr) := mx .mtext .expr segs![.one (txt "where "), .one (el .em .phrasing segs![.one (txt "x")])]

-- After MathML Core's `semantics` example: one half, annotated as TeX, as content MathML the
-- library does not model, and as HTML.
example : N (.mathml .expr) :=
  mx .semantics .expr segs![.one (mx .mfrac .expr segs![.one (mn "1"), .one (mn "2")]),
    .one (mx .annotation .annotation segs![.one (txt "\\frac{1}{2}")]),
    .one (mx .annotationXml .annotationXml segs![.one (Web.unchecked .mathml "apply" (.mathml .expr) () .nil)]),
    .one (mx .annotationXml .annotationXmlHtml segs![.one (el .p .paragraph segs![.one (txt "one half")])])]

-- MathML in an SVG `foreignObject`.
example : N (.svg (.el .foreignObject)) := sv .foreignObject segs![.one (inlineMath segs![.one (mi "r")])]

-- a fraction with one child
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <mfrac> as Cat.mathml Mathml.Cat.expr does not admit its children: they end before it is complete
-/
#guard_msgs in
example : N (.mathml .expr) := mx .mfrac .expr segs![.one (mx .mn .expr segs![])]

-- a fraction with three children
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <mfrac> as Cat.mathml Mathml.Cat.expr does not admit its children: segment 3, of category Cat.mathml Mathml.Cat.expr, cannot follow the segments before it
-/
#guard_msgs in
example : N (.mathml .expr) := mx .mfrac .expr segs![.one (mx .mn .expr segs![]), .one (mx .mn .expr segs![]), .one (mx .mn .expr segs![])]

-- msubsup with two children
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <msubsup> as Cat.mathml Mathml.Cat.expr does not admit its children: they end before it is complete
-/
#guard_msgs in
example : N (.mathml .expr) := mx .msubsup .expr segs![.one (mx .mi .expr segs![]), .one (mx .mn .expr segs![])]

-- an odd number of postscripts
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <mmultiscripts> as Cat.mathml Mathml.Cat.expr does not admit its children: they end before it is complete
-/
#guard_msgs in
example : N (.mathml .expr) := mx .mmultiscripts .expr segs![.one (mx .mi .expr segs![]), .one (mx .mn .expr segs![])]

-- two mprescripts
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <mmultiscripts> as Cat.mathml Mathml.Cat.expr does not admit its children: segment 3, of category Cat.mathml Mathml.Cat.prescripts, cannot follow the segments before it
-/
#guard_msgs in
example : N (.mathml .expr) := mx .mmultiscripts .expr segs![.one (mx .mi .expr segs![]), .one (mx .mprescripts .prescripts segs![]), .one (mx .mprescripts .prescripts segs![])]

-- mprescripts outside mmultiscripts
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <mrow> as Cat.mathml Mathml.Cat.expr does not admit its children: segment 1, of category Cat.mathml Mathml.Cat.prescripts, cannot follow the segments before it
-/
#guard_msgs in
example : N (.mathml .expr) := mx .mrow .expr segs![.one (mx .mprescripts .prescripts segs![])]

-- a cell directly in a table
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <mtable> as Cat.mathml Mathml.Cat.expr does not admit its children: segment 1, of category Cat.mathml Mathml.Cat.cell, cannot follow the segments before it
-/
#guard_msgs in
example : N (.mathml .expr) := mx .mtable .expr segs![.one (mx .mtd .cell segs![])]

-- an expression directly in a row
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <mtr> as Cat.mathml Mathml.Cat.row does not admit its children: segment 1, of category Cat.mathml Mathml.Cat.expr, cannot follow the segments before it
-/
#guard_msgs in
example : N (.mathml .row) := mx .mtr .row segs![.one (mx .mi .expr segs![])]

-- flow content in a token
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <mi> as Cat.mathml Mathml.Cat.expr does not admit its children: segment 1, of category Cat.html Html.Cat.flow, cannot follow the segments before it
-/
#guard_msgs in
example : N (.mathml .expr) := mx .mi .expr segs![.one (el .div .flow segs![])]

-- an annotation before the annotated expression
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <semantics> as Cat.mathml Mathml.Cat.expr does not admit its children: segment 1, of category Cat.mathml Mathml.Cat.annotation, cannot follow the segments before it
-/
#guard_msgs in
example : N (.mathml .expr) := mx .semantics .expr segs![.one (mx .annotation .annotation segs![]), .one (mx .mi .expr segs![])]

-- HTML directly in an mrow
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <mrow> as Cat.mathml Mathml.Cat.expr does not admit its children: segment 1, of category Cat.html Html.Cat.paragraph, cannot follow the segments before it
-/
#guard_msgs in
example : N (.mathml .expr) := mx .mrow .expr segs![.one (el .p .paragraph segs![])]

-- an annotation outside semantics
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <mrow> as Cat.mathml Mathml.Cat.expr does not admit its children: segment 1, of category Cat.mathml Mathml.Cat.annotationXmlHtml, cannot follow the segments before it
-/
#guard_msgs in
example : N (.mathml .expr) := mx .mrow .expr segs![.one (mx .annotationXml .annotationXmlHtml segs![])]

-- MathML outside math
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <p> as Cat.html Html.Cat.paragraph does not admit its children: segment 1, of category Cat.mathml Mathml.Cat.expr, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .paragraph) := el .p .paragraph segs![.one (mx .mfrac .expr segs![.one (mx .mn .expr segs![]), .one (mx .mn .expr segs![])])]

-- children in mspace
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <mspace> as Cat.mathml Mathml.Cat.expr does not admit its children: segment 1, of category Cat.mathml Mathml.Cat.expr, cannot follow the segments before it
-/
#guard_msgs in
example : N (.mathml .expr) := mx .mspace .expr segs![.one (mx .mi .expr segs![])]

-- MathML in an HTML annotation
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <annotation-xml> as Cat.mathml Mathml.Cat.annotationXmlHtml does not admit its children: segment 1, of category Cat.mathml Mathml.Cat.expr, cannot follow the segments before it
-/
#guard_msgs in
example : N (.mathml .annotationXmlHtml) := mx .annotationXml .annotationXmlHtml segs![.one (mx .mi .expr segs![])]

def grammarOf (e : Elem) (c : Cat) := (vocab.spec e c).grammar

-- `math` takes phrasing content's place, and `annotation-xml` its category from what it holds.
example : vocab.infer (.mathml .math) [] (grammarOf (.html .div) (.html .flow)) = some (.html .phrasing) := by
  decide +kernel
example : vocab.infer (.mathml .annotationXml) [.one (.html .paragraph)] (grammarOf (.mathml .semantics) (.mathml .expr))
    = some (.mathml .annotationXmlHtml) := by
  decide +kernel
example : vocab.infer (.mathml .annotationXml) [.one (.mathml .expr)] (grammarOf (.mathml .semantics) (.mathml .expr))
    = some (.mathml .annotationXml) := by
  decide +kernel

example : (mx .mi .expr segs![]).erase.tag = some (.mathml, "mi") := by decide +kernel
example : (mx .annotationXml .annotationXml segs![]).erase.tag = some (.mathml, "annotation-xml") := by decide +kernel

-- Whitespace renders within a token element, and nowhere else in MathML.
example : (mi "x").erase.keepsWhitespace = true := by decide +kernel
example : (mx .mrow .expr segs![]).erase.keepsWhitespace = false := by decide +kernel
example : (mi "x").erase.isInline = false := by decide +kernel
example : (inlineMath segs![]).erase.isInline = true := by decide +kernel

end HtmlModelTests.Mathml
