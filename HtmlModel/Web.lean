/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Engine.Tree
public import HtmlModel.Html
public import HtmlModel.Svg
public import HtmlModel.Mathml

@[expose] public section

namespace HtmlModel.Web

open Regular Regex

inductive Cat where
  /-- Character data, which every vocabulary shares. -/
  | text
  /-- Inter-element whitespace. -/
  | ws
  | html (c : Html.Cat)
  | svg (c : Svg.Cat)
  | mathml (c : Mathml.Cat)
  /-- What every category is valid wherever: the content of an element admitting any elements or
  character data. -/
  | any
  deriving DecidableEq, Repr

def Cat.all : List Cat :=
  [.text, .ws, .any] ++ Html.Cat.all.map .html ++ Svg.Cat.all.map .svg ++
    Mathml.Cat.all.map .mathml

theorem Cat.mem_all (c : Cat) : c ∈ Cat.all := by
  cases c with
  | html c => simp [Cat.all, Html.Cat.mem_all]
  | svg c => simp [Cat.all, Svg.Cat.mem_all]
  | mathml c => simp [Cat.all, Mathml.Cat.mem_all]
  | _ => simp [Cat.all]

def hs (c : Html.Cat) : Regex Cat := .sym (.html c)

def flowSpec : Spec Cat := ⟨.star (hs .flow), true⟩
def phrasingSpec : Spec Cat := ⟨.star (hs .phrasing), false⟩
def textSpec : Spec Cat := ⟨.star (.sym .text), false⟩
def voidSpec : Spec Cat := ⟨.eps, false⟩

/-- A transparent element takes the content model of the category it is placed as. -/
def transparentSpec (c : Html.Cat) : Spec Cat := ⟨.star (hs c), c == .flow⟩

inductive Elem where
  | html (e : Html.Elem)
  | svg (e : Svg.Elem)
  | mathml (e : Mathml.Elem)
  /-- An autonomous custom element, whose categories and content model are those its vocabulary
  declares for its name, or else the standard's. -/
  | custom (name : String) (h : isCustomElementName name = true)
  deriving DecidableEq

/-- The categories and content models of custom elements, by name. They belong to the vocabulary
rather than to each element, so that no node holds a grammar at run time. -/
abbrev Declarations := List (String × List Cat × List (Cat × Spec Cat))

/-- The standard's content model for an autonomous custom element: flow and phrasing content, with
a transparent content model. -/
def undeclared : List Cat × List (Cat × Spec Cat) :=
  ([.html .phrasing, .html .flow],
    [(.html .phrasing, transparentSpec .phrasing), (.html .flow, transparentSpec .flow)])

/-- Script-supporting elements before a run of children whose own lists admit them. -/
def scripts : Regex Cat := .star (hs .scriptSupporting)

/-- One or more `dt` then one or more `dd`, intermixed with script-supporting elements after the
first of each. -/
def dtDdGroup : Regex Cat :=
  seq [hs .term, .star (hs .termOrScript), hs .description, .star (hs .descriptionOrScript)]

def htmlSpec : Html.Elem → Html.Cat → Spec Cat
  | .html, _ => ⟨seq [hs .head, hs .body], true⟩
  | .head, _ =>
    ⟨.interleave (.interleave (hs .title) (opt (hs .base))) (.star (hs .metadata)), true⟩
  | .title, _ | .style, _ | .script, _ | .textarea, _ | .option, _ => textSpec
  | .base, _ | .link, _ | .meta, _ | .hr, _ | .br, _ | .wbr, _ | .img, _ | .input, _
  | .source, _ | .track, _ | .col, _ | .area, _ | .iframe, _ | .embed, _ => voidSpec
  | .div, .descriptionGroup => ⟨.cat scripts dtDdGroup, true⟩
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
    ⟨seq [.star (hs .paragraphOrScript), hs .heading, .star (hs .paragraphOrScript)], true⟩
  | .ul, _ | .ol, _ | .menu, _ => ⟨.star (hs .listItemOrScript), true⟩
  | .dl, _ =>
    ⟨.alt (.cat scripts (.star dtDdGroup)) (.star (hs .descriptionGroupOrScript)), true⟩
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
  | .picture, _ => ⟨seq [.star (hs .pictureSourceOrScript), hs .image, scripts], true⟩
  | .select, _ => ⟨.star (hs .selectChild), true⟩
  | .optgroup, _ => ⟨.star (hs .optionOrScript), true⟩
  | .datalist, _ => ⟨.alt (.star (hs .phrasing)) (.star (hs .optionOrScript)), true⟩
  | .fieldset, _ => ⟨seq [opt (hs .legend), .star (hs .flow)], true⟩
  | .details, _ => ⟨seq [hs .summary, .star (hs .flow)], true⟩
  -- A script after an optional part is held by the list that follows it, or by the scripts after
  -- the part where no list follows. Rows need no first row, since scripts alone are no bodies.
  | .table, _ =>
    ⟨seq [scripts, opt (seq [hs .tableCaption, scripts]), .star (hs .tableColumnGroupOrScript),
      opt (seq [hs .tableHead, scripts]),
      .alt (.star (hs .tableBodyOrScript)) (.star (hs .tableRowOrScript)),
      opt (seq [hs .tableFoot, scripts])], true⟩
  | .colgroup, _ => ⟨.star (hs .tableColumnOrTemplate), true⟩
  | .thead, _ | .tbody, _ | .tfoot, _ => ⟨.star (hs .tableRowOrScript), true⟩
  | .tr, _ => ⟨.star (hs .tableCellOrScript), true⟩

/-- The empty language, for a category an element cannot take. -/
def noSpec : Spec Cat := ⟨.empty, false⟩

def svgEl (e : Svg.Elem) : Cat := .svg (.el e)
def svgGroup (g : Svg.Group) : Cat := .svg (.group g)

/-- What a container such as `g` holds, besides an `a`. -/
def containerMembers : List Cat :=
  [svgGroup .animation, svgGroup .descriptive, svgGroup .paintServer, svgGroup .shape,
    svgGroup .structural, svgEl .clipPath, svgEl .filter, svgEl .foreignObject, svgEl .image,
    svgEl .marker, svgEl .mask, svgEl .script, svgEl .style, svgEl .switch, svgEl .text, svgEl .view]

def textMembers : List Cat :=
  [.text, svgGroup .animation, svgGroup .descriptive, svgGroup .paintServer,
    svgGroup .textContentChild, svgEl .clipPath, svgEl .marker, svgEl .mask, svgEl .script,
    svgEl .style]

def tspanMembers : List Cat :=
  [.text, svgGroup .descriptive, svgGroup .paintServer, svgEl .animate, svgEl .script, svgEl .set,
    svgEl .style, svgEl .tspan]

def textPathMembers : List Cat :=
  [.text, svgGroup .descriptive, svgGroup .paintServer, svgEl .animate, svgEl .clipPath,
    svgEl .marker, svgEl .mask, svgEl .script, svgEl .set, svgEl .style, svgEl .tspan]

/-- The categories each SVG content model admits in any number and order. -/
def svgMembers : Svg.Model → List Cat
  | .container => containerMembers ++ [.svg .aContainer]
  | .aContainer => containerMembers
  | .text => textMembers ++ [.svg .aText]
  | .aText => textMembers
  | .tspan => tspanMembers ++ [.svg .aTspan]
  | .aTspan => tspanMembers
  | .textPath => textPathMembers ++ [.svg .aTextPath]
  | .aTextPath => textPathMembers
  | .clipPath =>
    [svgGroup .descriptive, svgGroup .animation, svgGroup .shape, svgEl .text, svgEl .use,
      svgEl .script]
  | .use =>
    [svgGroup .animation, svgGroup .descriptive, svgEl .clipPath, svgEl .mask, svgEl .script,
      svgEl .style]
  | .switch =>
    [svgGroup .animation, svgGroup .shape, .svg .aContainer, svgEl .foreignObject, svgEl .g,
      svgEl .image, svgEl .svg, svgEl .switch, svgEl .text, svgEl .use]
  | .shape =>
    [svgGroup .animation, svgGroup .descriptive, svgGroup .paintServer, svgEl .clipPath,
      svgEl .marker, svgEl .mask, svgEl .script, svgEl .style]
  | .gradient =>
    [svgGroup .descriptive, svgEl .animate, svgEl .animateTransform, svgEl .script, svgEl .set,
      svgEl .stop, svgEl .style]
  | .stop => [svgEl .animate, svgEl .script, svgEl .set, svgEl .style]
  | .view => [svgGroup .animation, svgGroup .descriptive, svgEl .script, svgEl .style]
  | .animation => [svgGroup .descriptive, svgEl .script]
  | .filter =>
    [svgGroup .descriptive, svgGroup .filterPrimitive, svgEl .animate, svgEl .script, svgEl .set]
  | .componentTransfer => [svgGroup .descriptive, svgGroup .transferFunction, svgEl .script]
  | .merge => [svgGroup .descriptive, svgEl .feMergeNode, svgEl .script]
  | .feImage =>
    [svgGroup .descriptive, svgEl .animate, svgEl .animateTransform, svgEl .script, svgEl .set]
  | .primitive => [svgGroup .descriptive, svgEl .animate, svgEl .script, svgEl .set]

/-- The SVG content models that admit any of `cs`. -/
def svgModelsOf (cs : List Cat) : List Cat :=
  (Svg.Model.all.filter fun m => (svgMembers m).any cs.contains).map (.svg ∘ .content)

/-- Any number of children of SVG content model `m`, in any order. -/
def svgContent (m : Svg.Model) : Regex Cat := .star (.sym (.svg (.content m)))

def svgSpec : Svg.Elem → Svg.Cat → Spec Cat
  | .svg, _ | .g, _ | .defs, _ | .symbol, _ | .marker, _ | .pattern, _ | .mask, _ =>
    ⟨svgContent .container, true⟩
  | .a, .aContainer => ⟨svgContent .aContainer, true⟩
  | .a, .aText => ⟨svgContent .aText, false⟩
  | .a, .aTspan => ⟨svgContent .aTspan, false⟩
  | .a, .aTextPath => ⟨svgContent .aTextPath, false⟩
  | .a, _ => noSpec
  | .text, _ => ⟨svgContent .text, false⟩
  | .tspan, _ => ⟨svgContent .tspan, false⟩
  | .textPath, _ => ⟨svgContent .textPath, false⟩
  | .clipPath, _ => ⟨svgContent .clipPath, true⟩
  | .use, _ | .image, _ => ⟨svgContent .use, true⟩
  | .switch, _ => ⟨svgContent .switch, true⟩
  | .title, _ | .desc, _ | .metadata, _ => ⟨.star (.sym .any), false⟩
  | .foreignObject, _ => ⟨.star (.sym .any), true⟩
  | .circle, _ | .ellipse, _ | .line, _ | .path, _ | .polygon, _ | .polyline, _ | .rect, _ =>
    ⟨svgContent .shape, true⟩
  | .linearGradient, _ | .radialGradient, _ => ⟨svgContent .gradient, true⟩
  | .stop, _ => ⟨svgContent .stop, true⟩
  | .view, _ => ⟨svgContent .view, true⟩
  | .script, _ | .style, _ => textSpec
  | .animate, _ | .set, _ | .animateTransform, _ | .discard, _ | .mpath, _ =>
    ⟨svgContent .animation, true⟩
  | .animateMotion, _ => ⟨.interleave (opt (.sym (svgEl .mpath))) (svgContent .animation), true⟩
  | .filter, _ => ⟨svgContent .filter, true⟩
  | .feComponentTransfer, _ => ⟨svgContent .componentTransfer, true⟩
  | .feDiffuseLighting, _ | .feSpecularLighting, _ =>
    ⟨.interleave (.sym (svgGroup .lightSource)) (svgContent .animation), true⟩
  | .feMerge, _ => ⟨svgContent .merge, true⟩
  | .feImage, _ => ⟨svgContent .feImage, true⟩
  | .feBlend, _ | .feColorMatrix, _ | .feComposite, _ | .feConvolveMatrix, _
  | .feDisplacementMap, _ | .feDropShadow, _ | .feFlood, _ | .feGaussianBlur, _
  | .feMorphology, _ | .feOffset, _ | .feTile, _ | .feTurbulence, _ | .feFuncA, _ | .feFuncB, _
  | .feFuncG, _ | .feFuncR, _ | .feMergeNode, _ | .feDistantLight, _ | .fePointLight, _
  | .feSpotLight, _ => ⟨svgContent .primitive, true⟩

def mm (c : Mathml.Cat) : Regex Cat := .sym (.mathml c)

/-- A subscript and superscript in `mmultiscripts`. -/
def scriptPair : Regex Cat := seq [mm .expr, mm .expr]

def mathmlSpec : Mathml.Elem → Mathml.Cat → Spec Cat
  | .mi, _ | .mn, _ | .mo, _ | .ms, _ | .mtext, _ => ⟨.star (hs .phrasing), false⟩
  | .mspace, _ | .mprescripts, _ => voidSpec
  | .mfrac, _ | .mroot, _ | .msub, _ | .msup, _ | .munder, _ | .mover, _ =>
    ⟨seq [mm .expr, mm .expr], true⟩
  | .msubsup, _ | .munderover, _ => ⟨seq [mm .expr, mm .expr, mm .expr], true⟩
  | .mmultiscripts, _ =>
    ⟨seq [mm .expr, .star scriptPair, opt (seq [mm .prescripts, .star scriptPair])], true⟩
  | .mtable, _ => ⟨.star (mm .row), true⟩
  | .mtr, _ => ⟨.star (mm .cell), true⟩
  | .semantics, _ => ⟨seq [mm .expr, .star (mm .annotations)], true⟩
  | .annotation, _ => textSpec
  | .annotationXml, .annotationXmlHtml => flowSpec
  | .annotationXml, _ => ⟨.star (mm .annotationXmlContent), true⟩
  | .math, _ | .maction, _ | .merror, _ | .mpadded, _ | .mphantom, _ | .mrow, _ | .msqrt, _
  | .mstyle, _ | .mtd, _ => ⟨.star (mm .expr), true⟩

def Elem.spec (decls : Declarations) : Elem → Cat → Spec Cat
  | .html e, .html c => htmlSpec e c
  | .svg .svg, .html .phrasing => svgSpec .svg (.el .svg)
  | .svg e, .svg c => svgSpec e c
  | .mathml .math, .html .phrasing => mathmlSpec .math .expr
  | .mathml e, .mathml c => mathmlSpec e c
  | .html _, _ | .svg _, _ | .mathml _, _ => noSpec
  | .custom name _, c => (((decls.lookup name).getD undeclared).2.lookup c).getD noSpec

def Elem.cats (decls : Declarations) : Elem → List Cat
  | .html e => e.cats.map .html
  | .svg .svg => [.html .phrasing, .svg (.el .svg)]
  | .svg e => e.cats.map .svg
  | .mathml .math => [.html .phrasing]
  | .mathml e => e.cats.map .mathml
  | .custom name _ => ((decls.lookup name).getD undeclared).1

def Cat.above : Cat → List Cat
  | .text => [.html .phrasing, .html .flow, .html .phrasingOrHeading] ++ svgModelsOf [.text] ++ [.any]
  | .ws =>
    .text :: Html.Cat.whitespace.map .html ++ Svg.Model.all.map (.svg ∘ .content) ++
      [.mathml .row, .mathml .cell, .mathml .annotations, .mathml .annotationXmlContent, .any]
  | .html c => c.above.map .html ++ [.any]
  | .svg c =>
    let groups := c.above.map .svg
    groups ++ svgModelsOf (.svg c :: groups) ++
      (if c == .el .svg then [.mathml .annotationXmlContent] else []) ++ [.any]
  | .mathml c => c.above.map .mathml ++ [.any]
  | .any => []

theorem Cat.above_closed :
    ∀ c ∈ Cat.all, ∀ d ∈ Cat.above c, ∀ e ∈ Cat.above d, e ∈ Cat.above c := by
  decide +kernel

theorem Cat.ws_least : ∀ c ∈ Cat.all, Cat.ws ∉ Cat.above c := by decide +kernel

/-- The vocabulary of HTML, SVG, and MathML Core, with custom elements declared by `decls`. -/
abbrev vocabWith (decls : Declarations) : Vocabulary where
  Elem := Elem
  Cat := Cat
  ns
    | .svg _ => .svg
    | .mathml _ => .mathml
    | _ => .html
  name
    | .html e => e.name
    | .svg e => e.name
    | .mathml e => e.name
    | .custom name .. => name
  above := Cat.above
  cats := Elem.cats decls
  spec := Elem.spec decls
  text := .text
  ws := .ws
  above_trans {c} _ _ hd he := Cat.above_closed c (Cat.mem_all c) _ hd _ he
  text_above_ws := by decide
  ws_least c := Cat.ws_least c (Cat.mem_all c)

/-- The vocabulary of HTML, SVG, and MathML Core, with custom elements undeclared. -/
abbrev vocab : Vocabulary := vocabWith []

abbrev NodeWith (decls : Declarations) (α : Type) (c : Cat) := HtmlModel.Node (vocabWith decls).sig α c
abbrev TreeWith (decls : Declarations) (α : Type) := HtmlModel.Tree (vocabWith decls).sig α
abbrev FragmentWith (decls : Declarations) (α : Type) := HtmlModel.Fragment (vocabWith decls).sig α

abbrev Node (α : Type) (c : Cat) := NodeWith [] α c
abbrev Tree (α : Type) := TreeWith [] α
abbrev Fragment (α : Type) := FragmentWith [] α

/-- `Node.elem` in the vocabulary declaring `decls`, so that `.html` and the like resolve in its
arguments. `elem` and the other helpers without `With` are those of `vocab`. -/
abbrev elemWith (decls : Declarations) {α : Type} (e : Elem) (c : Cat) (p : α)
    {ks : List (SegK Cat)} (segs : Segs (vocabWith decls).sig α ks)
    (hc : c ∈ (vocabWith decls).cats e := by decide +kernel)
    (ok : (vocabWith decls).Admits e c ks := by admits) : NodeWith decls α c :=
  (vocabWith decls).elem e c p segs hc ok

abbrev elem {α : Type} (e : Elem) (c : Cat) (p : α) {ks : List (SegK Cat)}
    (segs : Segs vocab.sig α ks) (hc : c ∈ vocab.cats e := by decide +kernel)
    (ok : vocab.Admits e c ks := by admits) : Node α c :=
  vocab.elem e c p segs hc ok

/-- `Node.unchecked` in the vocabulary declaring `decls`. -/
abbrev uncheckedWith (decls : Declarations) {α : Type} (ns : Namespace) (name : String) (c : Cat)
    (p : α) (children : Frag (vocabWith decls).sig α)
    (hname : ns.validName name = true := by decide +kernel) : NodeWith decls α c :=
  (vocabWith decls).unchecked ns name c p children hname

abbrev unchecked {α : Type} (ns : Namespace) (name : String) (c : Cat) (p : α)
    (children : Frag vocab.sig α) (hname : ns.validName name = true := by decide +kernel) :
    Node α c :=
  vocab.unchecked ns name c p children hname

/-- Inter-element whitespace in the vocabulary declaring `decls`. -/
abbrev wsWith (decls : Declarations) {α : Type} (s : String)
    (h : isWhitespace s = true := by decide +kernel) : NodeWith decls α .ws :=
  (vocabWith decls).whitespace s h

abbrev ws {α : Type} (s : String) (h : isWhitespace s = true := by decide +kernel) : Node α .ws :=
  vocab.whitespace s h

/-- `n`, placed where category `d` is valid, in the vocabulary declaring `decls`. -/
abbrev widenWith (decls : Declarations) {α : Type} {c d : Cat} (n : NodeWith decls α c)
    (h : vocab.widens c d = true := by decide +kernel) : NodeWith decls α d :=
  (vocabWith decls).widen n h

abbrev widen {α : Type} {c d : Cat} (n : Node α c) (h : vocab.widens c d = true := by decide +kernel) :
    Node α d :=
  vocab.widen n h

end HtmlModel.Web
