/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel
meta import HtmlModel

/-! Terms shaped as lasm's `html!` would generate them, and erasure onto a copy of the shape of
`Lasm.UI.Html Msg`, keys and attributes taken from each element's payload. -/

@[expose] public section

namespace HtmlModelTests.LasmTerms

open HtmlModel Web Lean Elab Term Meta

/-- The category `Vocabulary.infer` finds for element `e` with children of kinds `ks` in a parent
whose grammar is `parent`, as `html!` would find it while elaborating. -/
syntax (name := inferCat) "infer_cat% " term:max term:max term:max : term

@[term_elab inferCat] meta def elabInferCat : TermElab := fun stx _ => do
  let call ← elabTerm (← `(Vocabulary.infer Web.vocab $(⟨stx[1]⟩) $(⟨stx[2]⟩) $(⟨stx[3]⟩)))
    (some (mkApp (mkConst ``Option [0]) (mkConst ``Web.Cat)))
  synthesizeSyntheticMVarsNoPostponing
  match (← kernelNormalize 64 (← instantiateMVars call)).getAppFnArgs with
  | (``Option.some, #[_, c]) => return c
  | _ => throwError "no category for this element here"

inductive Ns where
  | html | svg | mathml
  deriving DecidableEq

def Ns.of : Namespace → Ns
  | .html => .html
  | .svg => .svg
  | .mathml => .mathml

inductive Attr (Msg : Type) where
  | attr (name value : String)
  | on (event : String) (msg : Msg)

def Attr.map {α β : Type} (f : α → β) : Attr α → Attr β
  | .attr n v => .attr n v
  | .on e m => .on e (f m)

inductive Html (Msg : Type) where
  | text (s : String)
  | elem (ns : Ns) (tag : String) (key : Option String) (attrs : List (Attr Msg))
      (children : List (Html Msg))

mutual
def Html.map {α β : Type} (f : α → β) : Html α → Html β
  | .text s => .text s
  | .elem ns tag key attrs ch => .elem ns tag key (attrs.map (Attr.map f)) (Html.mapList f ch)
def Html.mapList {α β : Type} (f : α → β) : List (Html α) → List (Html β)
  | [] => []
  | h :: hs => Html.map f h :: Html.mapList f hs
end

structure Payload (Msg : Type) where
  key : Option String := none
  attrs : List (Attr Msg) := []

def Payload.map {α β : Type} (f : α → β) (p : Payload α) : Payload β :=
  { key := p.key, attrs := p.attrs.map (Attr.map f) }

abbrev View (Msg : Type) (c : Cat) := Web.Node (Payload Msg) c

mutual
def toHtml {Msg : Type} : Web.Tree (Payload Msg) → Html Msg
  | .text s | .verbatim _ s => .text s
  | .elem e _ p ch => .elem (Ns.of (vocab.sig.ns e)) (vocab.sig.name e) p.key p.attrs (toHtmlList ch)
  | .unchecked ns name _ p ch => .elem (Ns.of ns) name p.key p.attrs (toHtmlList ch)
def toHtmlList {Msg : Type} : List (Web.Tree (Payload Msg)) → List (Html Msg)
  | [] => []
  | t :: ts => toHtml t :: toHtmlList ts
end

mutual
theorem toHtml_map {α β : Type} (f : α → β) :
    (t : Web.Tree (Payload α)) → toHtml (t.map (Payload.map f)) = (toHtml t).map f
  | .text _ | .verbatim _ _ => rfl
  | .elem _ _ _ ch | .unchecked _ _ _ _ ch => by
    simp only [Tree.map, toHtml, Html.map, Payload.map, toHtmlList_map f ch]
theorem toHtmlList_map {α β : Type} (f : α → β) : (ts : List (Web.Tree (Payload α))) →
    toHtmlList (Tree.mapList (Payload.map f) ts) = Html.mapList f (toHtmlList ts)
  | [] => rfl
  | t :: ts => by
    simp only [Tree.mapList, toHtmlList, Html.mapList, toHtml_map f t, toHtmlList_map f ts]
end

/-- Mapping a view's messages and then erasing it is erasing it and then mapping its messages. -/
theorem toHtml_erase_map {α β : Type} (f : α → β) {c : Cat} (v : View α c) :
    toHtml (Node.map (Payload.map f) v).erase = (toHtml v.erase).map f := by
  rw [Node.erase_map, toHtml_map]

inductive Msg where
  | increment
  | select (i : Nat)

structure Model where
  title : String
  count : Nat
  items : List String
  tags : Array String
  note : Option String

/-- A helper returning mixed flow content for a `{children}` splice, each item written as `html!`
against the list's element type. -/
def summary (m : Model) : List (View Msg (.html .flow)) :=
  [Web.widen (Web.elem (.html .p) (.html .paragraph) {} segs![
      .one (.text "Count: "), .one (.text (toString m.count))]),
    Web.widen (Web.elem (.html .span) (.html .phrasing) {} segs![.one (.text "items")])]

def item (i : Nat) (s : String) : View Msg (.html .listItem) :=
  Web.elem (.html .li) (.html .listItem) { key := some (toString i), attrs := [.on "click" (.select i)] }
    segs![.one (.text s)]

def view (m : Model) : View Msg (.html .flow) :=
  Web.elem (.html .div) (.html .flow) { attrs := [.attr "class" "app"] } segs![
    .one (Web.elem (.html .h1) (.html .heading) {} segs![.one (.text m.title)]),
    .one (Web.elem (.html .p) (.html .paragraph) {} segs![
      .one (.text "See "),
      .one (Web.elem (.html .a)
        (infer_cat% (.html .a) [.one .text] (vocab.spec (.html .p) (.html .paragraph)).grammar)
        { attrs := [.attr "href" "/help"] } segs![.one (.text "help")]),
      .one (.text " or press "),
      .one (Web.elem (.html .button) (.html .phrasing) { attrs := [.on "click" .increment] }
        segs![.one (.text "+")])]),
    .one (Web.elem (.html .a)
      (infer_cat% (.html .a) [.one (.html .paragraph)] (vocab.spec (.html .div) (.html .flow)).grammar)
      { attrs := [.attr "href" "/"] } segs![
        .one (Web.elem (.html .p) (.html .paragraph) {} segs![.one (.text "Home")])]),
    .many (Nodes.ofList (summary m)),
    .one (Web.elem (.html .ul) (.html .flow) {} segs![
      .one (item 0 "first"), .one (Web.ws " "), .one (item 1 "second"),
      .many (Nodes.ofList (m.items.mapIdx fun i s => item (i + 2) s))]),
    .one (Web.elem (.html .p) (.html .paragraph) {} segs![
      .many (Nodes.ofList (m.tags.map fun t =>
        Web.elem (.html .code) (.html .phrasing) {} segs![.one (.text t)]).toList),
      .one (.text m.title),
      .one (.text (toString m.count))]),
    Seg.ofOption _ (m.note.map fun n => Web.elem (.html .aside) (.html .flow) {} segs![.one (.text n)]),
    .one (Web.elem (.custom "my-card" (by decide))
      (infer_cat% (.custom "my-card" (by decide)) [.one (.html .paragraph)]
        (vocab.spec (.html .div) (.html .flow)).grammar)
      { key := some "card" } segs![
        .one (Web.elem (.html .p) (.html .paragraph) {} segs![.one (.text "Inside a card")])]),
    .one (Web.elem (.svg .svg) (.html .phrasing) {} segs![
      .one (Web.elem (.svg .foreignObject) (.svg (.el .foreignObject)) {} segs![
        .one (Web.elem (.html .p) (.html .paragraph) {} segs![.one (.text "HTML in SVG")])])])]

example (m : Model) : (view m).erase.Valid := (view m).valid_erase

/-- The view as lasm renders it. -/
def render (m : Model) : Html Msg := toHtml (view m).erase

/-- The view embedded in a parent component, its messages mapped into the parent's. -/
def embed (m : Model) : View (Option Msg) (.html .flow) := Node.map (Payload.map some) (view m)

def renderEmbedded (m : Model) : Html (Option Msg) := toHtml (embed m).erase

example (m : Model) : renderEmbedded m = (render m).map some := toHtml_erase_map some (view m)

end HtmlModelTests.LasmTerms
