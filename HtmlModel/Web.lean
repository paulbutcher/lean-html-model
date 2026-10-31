/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Engine.Tree
public import HtmlModel.Html

@[expose] public section

namespace HtmlModel.Web

open Regular Regex

inductive Cat where
  /-- Character data, which every vocabulary shares. -/
  | text
  | html (c : Html.Cat)
  deriving DecidableEq, Repr

def Cat.above : Cat → List Cat
  | .text => [.html .phrasing, .html .flow, .html .phrasingOrHeading]
  | .html c => c.above.map .html

inductive Elem where
  | html (e : Html.Elem)
  /-- An autonomous custom element, whose categories and content model its caller supplies. -/
  | custom (name : String) (h : isCustomElementName name = true) (cats : List Cat)
      (specs : List (Cat × Spec Cat))
  deriving DecidableEq

def hs (c : Html.Cat) : Regex Cat := .sym (.html c)

/-- Script-supporting elements anywhere among the children `r` describes. -/
def withScripts (r : Regex Cat) : Regex Cat := .interleave r (.star (hs .scriptSupporting))

def flowSpec : Spec Cat := ⟨.star (hs .flow), true⟩
def phrasingSpec : Spec Cat := ⟨.star (hs .phrasing), false⟩
def textSpec : Spec Cat := ⟨.star (.sym .text), false⟩
def voidSpec : Spec Cat := ⟨.eps, false⟩

/-- A transparent element takes the content model of the category it is placed as. -/
def transparentSpec (c : Html.Cat) : Spec Cat := ⟨.star (hs c), c == .flow⟩

def dtDdGroup : Regex Cat := seq [plus (hs .term), plus (hs .description)]

def htmlSpec : Html.Elem → Html.Cat → Spec Cat
  | .html, _ => ⟨seq [hs .head, hs .body], true⟩
  | .head, _ =>
    ⟨.interleave (.interleave (hs .title) (opt (hs .base))) (.star (hs .metadata)), true⟩
  | .title, _ | .style, _ | .script, _ | .textarea, _ | .option, _ => textSpec
  | .base, _ | .link, _ | .meta, _ | .hr, _ | .br, _ | .wbr, _ | .img, _ | .input, _
  | .source, _ | .track, _ | .col, _ | .area, _ | .iframe, _ | .embed, _ => voidSpec
  | .div, .descriptionGroup => ⟨withScripts dtDdGroup, true⟩
  | .body, _ | .article, _ | .section, _ | .nav, _ | .aside, _ | .header, _ | .footer, _
  | .address, _ | .blockquote, _ | .main, _ | .search, _ | .form, _ | .dialog, _ | .div, _
  | .li, _ | .dt, _ | .dd, _ | .figcaption, _ | .caption, _ | .td, _ | .th, _
  | .template, _ => flowSpec
  | .p, _ | .h1, _ | .h2, _ | .h3, _ | .h4, _ | .h5, _ | .h6, _ | .pre, _ | .rt, _ | .rp, _
  | .em, _ | .strong, _ | .small, _ | .s, _ | .cite, _ | .q, _ | .dfn, _ | .abbr, _
  | .data, _ | .time, _ | .code, _ | .var, _ | .samp, _ | .kbd, _ | .sub, _ | .sup, _
  | .i, _ | .b, _ | .u, _ | .mark, _ | .bdi, _ | .bdo, _ | .span, _ | .label, _
  | .button, _ | .output, _ | .progress, _ | .meter, _ => phrasingSpec
  | .legend, _ | .summary, _ => ⟨.star (hs .phrasingOrHeading), false⟩
  | .hgroup, _ =>
    ⟨withScripts (seq [.star (hs .paragraph), hs .heading, .star (hs .paragraph)]), true⟩
  | .ul, _ | .ol, _ | .menu, _ => ⟨withScripts (.star (hs .listItem)), true⟩
  | .dl, _ => ⟨withScripts (.alt (.star dtDdGroup) (.star (hs .descriptionGroup))), true⟩
  | .figure, _ =>
    ⟨.alt (seq [hs .figureCaption, .star (hs .flow)]) (seq [.star (hs .flow), opt (hs .figureCaption)]),
      true⟩
  | .ruby, _ =>
    ⟨plus (seq [.star (hs .phrasing),
      .alt (plus (hs .rubyText))
        (seq [hs .rubyParenthesis, plus (seq [hs .rubyText, hs .rubyParenthesis])])]), false⟩
  | .noscript, .metadata => ⟨.star (hs .noscriptMetadata), true⟩
  | .a, c | .ins, c | .del, c | .object, c | .map, c | .slot, c | .canvas, c
  | .noscript, c => transparentSpec c
  | .video, c | .audio, c => ⟨seq [.star (hs .source), .star (hs .track), .star (hs c)], true⟩
  | .picture, _ => ⟨withScripts (seq [.star (hs .pictureSource), hs .image]), true⟩
  | .select, _ => ⟨withScripts (.star (hs .selectChild)), true⟩
  | .optgroup, _ => ⟨withScripts (.star (hs .option)), true⟩
  | .datalist, _ => ⟨.alt (.star (hs .phrasing)) (withScripts (.star (hs .option))), true⟩
  | .fieldset, _ => ⟨seq [opt (hs .legend), .star (hs .flow)], true⟩
  | .details, _ => ⟨seq [hs .summary, .star (hs .flow)], true⟩
  | .table, _ =>
    ⟨withScripts (seq [opt (hs .tableCaption), .star (hs .tableColumnGroup), opt (hs .tableHead),
      .alt (.star (hs .tableBody)) (plus (hs .tableRow)), opt (hs .tableFoot)]), true⟩
  | .colgroup, _ => ⟨.star (.alt (hs .tableColumn) (hs .template)), true⟩
  | .thead, _ | .tbody, _ | .tfoot, _ => ⟨withScripts (.star (hs .tableRow)), true⟩
  | .tr, _ => ⟨withScripts (.star (hs .tableCell)), true⟩

/-- The empty language, for a category an element cannot take. -/
def noSpec : Spec Cat := ⟨.empty, false⟩

def Elem.spec : Elem → Cat → Spec Cat
  | .html e, .html c => htmlSpec e c
  | .html _, .text => noSpec
  | .custom _ _ _ specs, c => (specs.lookup c).getD noSpec

def Elem.cats : Elem → List Cat
  | .html e => e.cats.map .html
  | .custom _ _ cats _ => cats

/-- The vocabulary of HTML, with custom elements. -/
abbrev vocab : Vocabulary where
  Elem := Elem
  Cat := Cat
  ns _ := .html
  name
    | .html e => e.name
    | .custom name .. => name
  above := Cat.above
  cats := Elem.cats
  spec := Elem.spec
  text := .text

abbrev Node (α : Type) (c : Cat) := HtmlModel.Node vocab α c
abbrev Tree (α : Type) := HtmlModel.Tree vocab α
abbrev Fragment (α : Type) := HtmlModel.Fragment vocab α

/-- `Node.elem` with the vocabulary fixed, so that `.html` and the like resolve in its arguments. -/
abbrev elem {α : Type} (e : Elem) (c : Cat) (p : α) {ks : List (SegK Cat)} (segs : Segs vocab α ks)
    (hc : c ∈ vocab.cats e := by decide +kernel) (ok : vocab.Admits e c ks := by admits) :
    Node α c :=
  HtmlModel.Node.elem e c p segs hc ok

/-- `Node.unchecked` with the vocabulary fixed. -/
abbrev unchecked {α : Type} (ns : Namespace) (name : String) (c : Cat) (p : α)
    (children : Frag vocab α) (hname : ns.validName name = true := by decide +kernel) : Node α c :=
  HtmlModel.Node.unchecked ns name c p children hname

end HtmlModel.Web
