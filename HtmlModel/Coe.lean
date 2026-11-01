/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Web
meta import HtmlModel.Web
public meta import Lean.Elab.Command

@[expose] public section

namespace HtmlModel.Web

/-- `c` widens to `d`, so that a node of the one coerces to the other. Instance search cannot
decide widening, so there is an instance for every such pair. -/
class Widens (c d : Cat) : Prop where
  widens : vocab.widens c d = true

instance {decls : Declarations} {α : Type} {c d : Cat} [h : Widens c d]
    (n : HtmlModel.Node (vocabWith decls).sig α c) :
    CoeT (HtmlModel.Node (vocabWith decls).sig α c) n (HtmlModel.Node (vocabWith decls).sig α d) :=
  ⟨.widen n h.widens⟩

open Lean Elab Command in
local elab "widens_instances" : command => do
  let pairs := Cat.all.flatMap fun c => (Cat.above c).map (c, ·)
  let term (c : Cat) : CommandElabM Term := do
    match Parser.runParserCategory (← getEnv) `term (reprStr c) with
    | .ok stx => pure ⟨stx⟩
    | .error e => throwError e
  for (c, d) in pairs, i in [0:pairs.length] do
    let name := mkIdent (.mkStr2 "Widens" s!"of{i}")
    elabCommand (← `(instance $name:ident : Widens $(← term c) $(← term d) := ⟨by decide +kernel⟩))

widens_instances

end HtmlModel.Web
