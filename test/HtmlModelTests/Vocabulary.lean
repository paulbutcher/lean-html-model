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
  .text :: .any ::
  (([.expr, .prescripts, .row, .cell, .annotation, .annotationXmlHtml, .annotationXml] : List Mathml.Cat).map .mathml) ++
  (Svg.Elem.all.map (Cat.svg ∘ .el)) ++
  ([.animation, .descriptive, .paintServer, .gradient, .shape, .structural, .textContentChild,
    .filterPrimitive, .transferFunction, .lightSource] : List Svg.Group).map (Cat.svg ∘ .group) ++
  [.svg .aContainer, .svg .aText, .svg .aTspan, .svg .aTextPath] ++ ([.flow, .phrasing, .phrasingOrHeading, .heading, .headingGroup, .paragraph, .image,
    .metadata, .noscriptMetadata, .title, .base, .document, .head, .body, .listItem, .term,
    .description, .descriptionGroup, .figureCaption, .summary, .legend, .source, .pictureSource,
    .track, .rubyText, .rubyParenthesis, .option, .selectChild, .tableCaption, .tableColumnGroup,
    .tableColumn, .tableHead, .tableBody, .tableFoot, .tableRow, .tableCell, .scriptSupporting,
    .template] : List Html.Cat).map .html

theorem mem_allCats (c : Cat) : c ∈ allCats := by
  rcases c with _ | c | c | c | _
  · decide
  · cases c <;> decide
  · rcases c with e | g | _ | _ | _ | _
    · cases e <;> decide
    · cases g <;> decide
    all_goals decide
  · cases c <;> decide
  · decide

-- `above` is transitively closed, so that `widens` is a preorder.
theorem above_closed :
    allCats.all (fun c => (Cat.above c).all fun d => (Cat.above d).all ((Cat.above c).contains ·)) := by
  decide +kernel

theorem Svg.Elem.mem_all (e : Svg.Elem) : e ∈ Svg.Elem.all := by cases e <;> decide

theorem Svg.Elem.ofName?_name : Svg.Elem.all.all (fun e => Svg.Elem.ofName? e.name == some e) := by
  decide +kernel

theorem Mathml.Elem.mem_all (e : Mathml.Elem) : e ∈ Mathml.Elem.all := by cases e <;> decide

theorem Mathml.Elem.ofName?_name :
    Mathml.Elem.all.all (fun e => Mathml.Elem.ofName? e.name == some e) := by
  decide +kernel

-- Every element takes some category, and has a content model at each.
theorem cats_nonempty : Html.Elem.all.all (fun e => !e.cats.isEmpty) := by decide +kernel

end HtmlModelTests.Vocabulary
