/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModelTests.Helpers
meta import HtmlModelTests.Helpers

namespace HtmlModelTests.Infer

open HtmlModel Web

def grammarOf (e : Html.Elem) (c : Html.Cat) := (vocab.spec (.html e) (.html c)).grammar

-- A transparent element takes phrasing or flow from what it holds.
example : vocab.infer (.html .a) [.one .text] (grammarOf .div .flow) = some (.html .phrasing) := by
  decide +kernel
example : vocab.infer (.html .a) [.one (.html .paragraph)] (grammarOf .div .flow) = some (.html .flow) := by
  decide +kernel
example : vocab.infer (.html .a) [.one (.html .paragraph)] (grammarOf .p .paragraph) = none := by
  decide +kernel

-- `source` and `noscript` take their category from their parent; `link` has one, which widens to
-- both head and body content.
example : vocab.infer (.html .link) [] (grammarOf .head .head) = some (.html .phrasingMetadata) := by
  decide +kernel
example : vocab.infer (.html .link) [] (grammarOf .body .body) = some (.html .phrasingMetadata) := by
  decide +kernel
example : vocab.infer (.html .source) [] (grammarOf .picture .phrasing) = some (.html .pictureSource) := by
  decide +kernel
example : vocab.infer (.html .source) [] (grammarOf .video .flow) = some (.html .source) := by
  decide +kernel
example : vocab.infer (.html .noscript) [.one (.html .noscriptMetadata)] (grammarOf .head .head)
    = some (.html .metadata) := by
  decide +kernel

-- A `div` is a group of terms and descriptions only where it holds one.
example : vocab.infer (.html .div) [.one (.html .term), .one (.html .description)] (grammarOf .dl .flow)
    = some (.html .descriptionGroup) := by
  decide +kernel
example : vocab.infer (.html .div) [.one (.html .term), .one (.html .description)] (grammarOf .body .body)
    = none := by
  decide +kernel

-- Wherever an element with no children may stand, inference finds its category.
#guard Html.Elem.all.all fun e => Html.Elem.all.all fun parent => parent.cats.all fun pc =>
  let g := grammarOf parent pc
  (vocab.candidates (.html e) [] g).isEmpty || (vocab.infer (.html e) [] g).isSome

end HtmlModelTests.Infer
