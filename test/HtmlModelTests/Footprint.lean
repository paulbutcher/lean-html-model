/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

meta import HtmlModelTests.LasmTerms
meta import HtmlModelTests.LeanHtml
meta import Lean.Compiler.IR.EmitUtil

/-! Building and erasing a tree runs nothing else: from views compiled as lasm and lean-html compile
them, no part of acceptance, no grammar, and no vocabulary table is reachable in compiled code. -/

namespace HtmlModelTests.Footprint

open Lean IR

/-- Every declaration compiled code reachable from `roots` may call. -/
meta def reachable (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  -- Each step adds a declaration to `seen` or drops one already there, so this bounds the walk.
  for _ in [0:100000] do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      unless seen.contains n do
        seen := seen.insert n
        if let some d := findEnvDecl env n then
          todo := (collectUsedDecls env [d]).toList ++ todo
  return seen

/-- Declarations, with whatever the compiler derives from them, that only acceptance needs. -/
meta def forbidden : List Name :=
  [`Regular, ``HtmlModel.Vocabulary, `HtmlModel.Web, ``HtmlModel.Html.Cat.whitespace,
    ``HtmlModel.Html.Cat.scriptMixtures, ``HtmlModel.Svg.Elem.groups,
    ``HtmlModel.Html.Elem.cats, ``HtmlModel.Html.Cat.above, ``HtmlModel.Svg.Elem.cats,
    ``HtmlModel.Svg.Cat.above, ``HtmlModel.Mathml.Elem.cats, ``HtmlModel.Mathml.Cat.above]

#eval show CoreM Unit from do
  let used := reachable (← getEnv)
    [``LasmTerms.render, ``LasmTerms.renderEmbedded, ``LeanHtml.page, ``LeanHtml.list,
      ``LeanHtml.rows, ``LeanHtml.kanji, ``HtmlModel.Tree.isInlineIn,
      ``HtmlModel.Tree.childrenInline]
  unless used.toList.any (``HtmlModel.Node.erase).isPrefixOf do
    throwError "the walk did not reach erasure"
  let bad := used.toList.filter fun n => forbidden.any (·.isPrefixOf n)
  unless bad.isEmpty do throwError "reachable at run time: {bad}"

end HtmlModelTests.Footprint
