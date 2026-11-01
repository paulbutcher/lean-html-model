/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModelTests.Helpers

namespace HtmlModelTests.Vocabulary

open HtmlModel Web Regular

theorem Html.Elem.mem_all (e : Html.Elem) : e ∈ Html.Elem.all := by cases e <;> decide

theorem Html.Elem.ofName?_name : Html.Elem.all.all (fun e => Html.Elem.ofName? e.name == some e) := by
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
def elems : List Elem :=
  Html.Elem.all.map .html ++ Svg.Elem.all.map .svg ++ Mathml.Elem.all.map .mathml

def specs : List (Spec Cat) := elems.flatMap fun e => (vocab.cats e).map (vocab.spec e)

mutual
/-- The symbols outside any repetition, each of which fills a position some word must fill. -/
def unrepeated : Regex Cat → List Cat
  | .sym c => [c]
  | .cat r s | .alt r s | .interleave r s => unrepeated r ++ unrepeated s
  | .nonEmpty r => unrepeated r
  | .allOf rs => unrepeatedAll rs
  | .empty | .eps | .star _ => []
def unrepeatedAll : List (Regex Cat) → List Cat
  | [] => []
  | r :: rs => unrepeated r ++ unrepeatedAll rs
end

/-- Whether `c` stands somewhere, and only repeated where whitespace may stand, as inter-element
whitespace or as text. -/
def onlyWhereWhitespace (c : Cat) : Bool :=
  specs.any (·.grammar.letters.contains c) &&
    specs.all fun sp => !sp.grammar.letters.contains c ||
      (!(unrepeated sp.grammar).contains c && (sp.ws || vocab.widens .text c))

-- Whitespace widens to exactly those categories, so that it never stands in for a required child.
theorem ws_widens_exactly :
    Cat.all.all (fun c => c == .ws || vocab.widens .ws c == onlyWhereWhitespace c) := by
  decide +kernel

/-- Whether no repetition is of a choice, so that each run of children has one category. -/
def repeatsOne : Regex Cat → Bool
  | .star (.alt _ _) => false
  | .star r | .nonEmpty r => repeatsOne r
  | .cat r s | .alt r s | .interleave r s => repeatsOne r && repeatsOne s
  | _ => true

theorem lists_have_one_category : specs.all (repeatsOne ·.grammar) := by decide +kernel

end HtmlModelTests.Vocabulary
