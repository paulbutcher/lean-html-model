/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModelTests.Helpers

namespace HtmlModelTests.Vocabulary

open HtmlModel Web

theorem Html.Elem.mem_all (e : Html.Elem) : e ∈ Html.Elem.all := by cases e <;> decide

theorem Html.Elem.ofName?_name : Html.Elem.all.all (fun e => Html.Elem.ofName? e.name == some e) := by
  decide +kernel

def allCats : List Cat :=
  .text :: ([.flow, .phrasing, .phrasingOrHeading, .heading, .headingGroup, .paragraph, .image,
    .metadata, .noscriptMetadata, .title, .base, .document, .head, .body, .listItem, .term,
    .description, .descriptionGroup, .figureCaption, .summary, .legend, .source, .pictureSource,
    .track, .rubyText, .rubyParenthesis, .option, .selectChild, .tableCaption, .tableColumnGroup,
    .tableColumn, .tableHead, .tableBody, .tableFoot, .tableRow, .tableCell, .scriptSupporting,
    .template] : List Html.Cat).map .html

theorem mem_allCats (c : Cat) : c ∈ allCats := by
  rcases c with _ | c
  · decide
  · cases c <;> decide

-- `above` is transitively closed, so that `widens` is a preorder.
theorem above_closed :
    allCats.all (fun c => (Cat.above c).all fun d => (Cat.above d).all ((Cat.above c).contains ·)) := by
  decide +kernel

-- Every element takes some category, and has a content model at each.
theorem cats_nonempty : Html.Elem.all.all (fun e => !e.cats.isEmpty) := by decide +kernel

end HtmlModelTests.Vocabulary
