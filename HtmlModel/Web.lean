/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Engine.Tree
public import HtmlModel.Html
public import HtmlModel.Svg

@[expose] public section

namespace HtmlModel.Web

open Regular Regex

inductive Cat where
  /-- Character data, which every vocabulary shares. -/
  | text
  | html (c : Html.Cat)
  | svg (c : Svg.Cat)
  /-- What every category is valid wherever: the content of an element admitting any elements or
  character data. -/
  | any
  deriving DecidableEq, Repr

def Cat.above : Cat → List Cat
  | .text => [.html .phrasing, .html .flow, .html .phrasingOrHeading, .any]
  | .html c => c.above.map .html ++ [.any]
  | .svg c => c.above.map .svg ++ [.any]
  | .any => []

inductive Elem where
  | html (e : Html.Elem)
  | svg (e : Svg.Elem)
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

def se (e : Svg.Elem) : Regex Cat := .sym (.svg (.el e))
def sg (g : Svg.Group) : Regex Cat := .sym (.svg (.group g))
def anyOf (rs : List (Regex Cat)) : Regex Cat := .star (oneOf rs)

/-- What a container such as `g` holds, with or without `a`, which may not hold another. -/
def containerContent (a : Bool) : List (Regex Cat) :=
  [sg .animation, sg .descriptive, sg .paintServer, sg .shape, sg .structural, se .clipPath,
    se .filter, se .foreignObject, se .image, se .marker, se .mask, se .script, se .style,
    se .switch, se .text, se .view] ++ if a then [.sym (.svg .aContainer)] else []

def textContent (a : Bool) : List (Regex Cat) :=
  [.sym .text, sg .animation, sg .descriptive, sg .paintServer, sg .textContentChild, se .clipPath,
    se .marker, se .mask, se .script, se .style] ++ if a then [.sym (.svg .aText)] else []

def tspanContent (a : Bool) : List (Regex Cat) :=
  [.sym .text, sg .descriptive, sg .paintServer, se .animate, se .script, se .set, se .style,
    se .tspan] ++ if a then [.sym (.svg .aTspan)] else []

def textPathContent (a : Bool) : List (Regex Cat) :=
  [.sym .text, sg .descriptive, sg .paintServer, se .animate, se .clipPath, se .marker, se .mask,
    se .script, se .set, se .style, se .tspan] ++ if a then [.sym (.svg .aTextPath)] else []

def svgSpec : Svg.Elem → Svg.Cat → Spec Cat
  | .svg, _ | .g, _ | .defs, _ | .symbol, _ | .marker, _ | .pattern, _ | .mask, _ =>
    ⟨anyOf (containerContent true), true⟩
  | .a, .aContainer => ⟨anyOf (containerContent false), true⟩
  | .a, .aText => ⟨anyOf (textContent false), false⟩
  | .a, .aTspan => ⟨anyOf (tspanContent false), false⟩
  | .a, .aTextPath => ⟨anyOf (textPathContent false), false⟩
  | .a, _ => noSpec
  | .text, _ => ⟨anyOf (textContent true), false⟩
  | .tspan, _ => ⟨anyOf (tspanContent true), false⟩
  | .textPath, _ => ⟨anyOf (textPathContent true), false⟩
  | .clipPath, _ =>
    ⟨anyOf [sg .descriptive, sg .animation, sg .shape, se .text, se .use, se .script], true⟩
  | .use, _ | .image, _ =>
    ⟨anyOf [sg .animation, sg .descriptive, se .clipPath, se .mask, se .script, se .style], true⟩
  | .switch, _ =>
    ⟨anyOf [sg .animation, sg .shape, .sym (.svg .aContainer), se .foreignObject, se .g,
      se .image, se .svg, se .switch, se .text, se .use], true⟩
  | .title, _ | .desc, _ | .metadata, _ => ⟨.star (.sym .any), false⟩
  | .foreignObject, _ => ⟨.star (.sym .any), true⟩
  | .circle, _ | .ellipse, _ | .line, _ | .path, _ | .polygon, _ | .polyline, _ | .rect, _ =>
    ⟨anyOf [sg .animation, sg .descriptive, sg .paintServer, se .clipPath, se .marker, se .mask,
      se .script, se .style], true⟩
  | .linearGradient, _ | .radialGradient, _ =>
    ⟨anyOf [sg .descriptive, se .animate, se .animateTransform, se .script, se .set, se .stop,
      se .style], true⟩
  | .stop, _ => ⟨anyOf [se .animate, se .script, se .set, se .style], true⟩
  | .view, _ => ⟨anyOf [sg .animation, sg .descriptive, se .script, se .style], true⟩
  | .script, _ | .style, _ => textSpec
  | .animate, _ | .set, _ | .animateTransform, _ | .mpath, _ =>
    ⟨anyOf [sg .descriptive, se .script], true⟩
  | .animateMotion, _ => ⟨.interleave (opt (se .mpath)) (anyOf [sg .descriptive, se .script]), true⟩
  | .filter, _ =>
    ⟨anyOf [sg .descriptive, sg .filterPrimitive, se .animate, se .script, se .set], true⟩
  | .feComponentTransfer, _ => ⟨anyOf [sg .descriptive, sg .transferFunction, se .script], true⟩
  | .feDiffuseLighting, _ | .feSpecularLighting, _ =>
    ⟨.interleave (sg .lightSource) (anyOf [sg .descriptive, se .script]), true⟩
  | .feMerge, _ => ⟨anyOf [sg .descriptive, se .feMergeNode, se .script], true⟩
  | .feImage, _ =>
    ⟨anyOf [sg .descriptive, se .animate, se .animateTransform, se .script, se .set], true⟩
  | .feBlend, _ | .feColorMatrix, _ | .feComposite, _ | .feConvolveMatrix, _
  | .feDisplacementMap, _ | .feDropShadow, _ | .feFlood, _ | .feGaussianBlur, _
  | .feMorphology, _ | .feOffset, _ | .feTile, _ | .feTurbulence, _ | .feFuncA, _ | .feFuncB, _
  | .feFuncG, _ | .feFuncR, _ | .feMergeNode, _ | .feDistantLight, _ | .fePointLight, _
  | .feSpotLight, _ => ⟨anyOf [sg .descriptive, se .animate, se .script, se .set], true⟩

def Elem.spec : Elem → Cat → Spec Cat
  | .html e, .html c => htmlSpec e c
  | .svg .svg, .html .phrasing => svgSpec .svg (.el .svg)
  | .svg e, .svg c => svgSpec e c
  | .html _, _ | .svg _, _ => noSpec
  | .custom _ _ _ specs, c => (specs.lookup c).getD noSpec

def Elem.cats : Elem → List Cat
  | .html e => e.cats.map .html
  | .svg .svg => [.html .phrasing, .svg (.el .svg)]
  | .svg e => e.cats.map .svg
  | .custom _ _ cats _ => cats

/-- The vocabulary of HTML and SVG, with custom elements. -/
abbrev vocab : Vocabulary where
  Elem := Elem
  Cat := Cat
  ns
    | .svg _ => .svg
    | _ => .html
  name
    | .html e => e.name
    | .svg e => e.name
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
