/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Web
public meta import Lean.Elab.Deriving.ToExpr

public meta section

namespace HtmlModel

open Lean

-- One command naming several of these fails to find the instances for the nested types.
deriving instance ToExpr for Html.Elem
deriving instance ToExpr for Html.Cat
deriving instance ToExpr for Svg.Elem
deriving instance ToExpr for Svg.Group
deriving instance ToExpr for Svg.Model
deriving instance ToExpr for Svg.Cat
deriving instance ToExpr for Mathml.Elem
deriving instance ToExpr for Mathml.Cat
deriving instance ToExpr for Web.Cat

/-- A custom element's proof that its name is valid is quoted as `Eq.refl true`, which the kernel
checks by evaluating `isCustomElementName`. -/
instance : ToExpr Web.Elem where
  toExpr
    | .html e => mkApp (mkConst ``Web.Elem.html) (toExpr e)
    | .svg e => mkApp (mkConst ``Web.Elem.svg) (toExpr e)
    | .mathml e => mkApp (mkConst ``Web.Elem.mathml) (toExpr e)
    | .custom name _ =>
      mkApp2 (mkConst ``Web.Elem.custom) (toExpr name)
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  toTypeExpr := mkConst ``Web.Elem

end HtmlModel
