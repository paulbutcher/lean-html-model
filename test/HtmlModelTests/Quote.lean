/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

meta import HtmlModel.Quote

namespace HtmlModelTests.Quote

open Lean Meta HtmlModel

/-- Throws unless each of `xs` quotes to a term of the type `toTypeExpr` gives that evaluates back
to it. -/
meta unsafe def roundTrip {α : Type} [ToExpr α] [BEq α] [Repr α] (xs : List α) : MetaM Unit := do
  for x in xs do
    let e := toExpr x
    check e
    unless ← isDefEq (← inferType e) (toTypeExpr α) do
      throwError "{repr x} quotes to a term of type {← inferType e}"
    unless (← evalExpr α (toTypeExpr α) e) == x do
      throwError "{repr x} does not evaluate back from {e}"

meta def custom : Web.Elem := .custom "my-card" (by decide)

meta instance : Repr Web.Elem := ⟨fun e _ => repr (Web.vocab.name e)⟩

#eval roundTrip Web.Cat.all
#eval roundTrip (custom :: Html.Elem.all.map .html ++ Svg.Elem.all.map .svg ++
  Mathml.Elem.all.map .mathml)
#eval roundTrip Html.Elem.all
#eval roundTrip Svg.Elem.all
#eval roundTrip Mathml.Elem.all

end HtmlModelTests.Quote
