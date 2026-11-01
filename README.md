# html-model

A Lean 4 library that models a tree of HTML, SVG, and MathML elements whose shape satisfies those standards' content models, with no knowledge of how the tree is serialized. An element's children are checked against its content model at compile time, even when they include lists known only at run time, and a tree erases to an untyped one that a renderer or a virtual DOM can consume, with a proof that the erased tree is valid.

It is the typed core shared by [lean-html](https://github.com/paulbutcher/lean-html), which renders HTML to strings, and a typed backend for [lasm](https://github.com/Millillion/lasm)'s `html!` macro. Content models are regular grammars, decided by [lean-regular](https://github.com/paulbutcher/lean-regular).

## Installation

Add it to your `lakefile.toml`:

```toml
[[require]]
name = "html-model"
git = "https://github.com/paulbutcher/lean-html-model"
```

## Usage

A node is indexed by the category it is valid in, and carries a payload of any type on each element, such as an attribute list. `Web.elem` builds an element from an element, the category it takes, a payload, and its children as segments, and proves by default that the element admits them. `Web.widen` places a node wherever a category it widens to is valid, so that a list known only at run time may hold nodes of several categories; the element keeps the category it was checked as. A node also coerces to any category it widens to, so that a list literal may mix categories.

```lean
import HtmlModel

open HtmlModel Web

/-- An HTML element with no payload. -/
abbrev el (e : Html.Elem) (c : Html.Cat) {ks : List (SegK Cat)} (segs : Segs vocab.sig Unit ks)
    (hc : Cat.html c ∈ vocab.cats (.html e) := by decide +kernel)
    (ok : vocab.Admits (.html e) (.html c) ks := by admits) : Web.Node Unit (.html c) :=
  Web.elem (.html e) (.html c) () segs hc ok

def txt (s : String) : Web.Node Unit .text := .text s

/-- A list whose items are known only at run time, after inter-element whitespace. -/
def list (items : List String) : Web.Node Unit (.html .flow) :=
  el .ul .flow segs![.one (ws "\n"),
    .many (Nodes.ofList (items.map fun i => el .li .listItem segs![.one (txt i)]))]

/-- Flow content of several categories, as a list known only at run time holds it. -/
def article (paras : List String) : List (Web.Node Unit (.html .flow)) :=
  Web.widen (el .h1 .heading segs![.one (txt "Title")]) :: paras.map fun s => Web.widen (txt s)
```

Children that the content model forbids are a compile error, which says which segment is wrong:

```lean
example : Web.Node Unit (.html .paragraph) :=
  el .p .paragraph segs![.one (txt "Hi"), .one (el .div .flow segs![])]
-- error: <p> as Cat.html Html.Cat.paragraph does not admit its children: segment 2, of category
-- Cat.html Html.Cat.flow, cannot follow the segments before it
```

An unchecked element stands for an element or content model the library does not yet have, such as `selectedcontent`. Its own children are not checked, but theirs are, and its name must survive being parsed back as HTML:

```lean
def picker : Web.Node Unit (.html .phrasing) :=
  el .select .phrasing segs![
    .one (Web.unchecked .html "selectedcontent" (.html .selectChild) () .nil),
    .one (el .option .option segs![.one (txt "A")])]
```

A fragment holds nodes of any categories, as an htmx response of table rows beside an out-of-band swap does:

```lean
def rows : Web.Fragment Unit :=
  [⟨_, el .tr .tableRow segs![]⟩, ⟨_, el .tr .tableRow segs![]⟩, ⟨_, el .div .flow segs![]⟩]
```

Erasure gives a `Tree` of text, verbatim markup, and elements, each element keeping its category and payload. Building a tree and erasing it, in time linear in its size, is all that runs: nodes and trees are built on the vocabulary's `Signature`, whose rules are propositions, so that compiled code reaches none of its tables or grammars.

```lean
example : (list ["a"]).erase.Valid := (list ["a"]).valid_erase

#eval (list ["a", "b"]).erase.tag   -- some (HtmlModel.Namespace.html, "ul")
#eval (Fragment.erase rows).length  -- 3
#eval picker.hasUnchecked           -- true
```

## Content model

- A segment is one node of a category, an optional node, a list of nodes of unknown length, a nonempty list, a list of groups each made of segments, or a choice between two runs of segments made at run time. Groups and choices nest, so that a list of `dl` groups or of ruby segments, each with its own number of terms, descriptions, or base nodes, is checked at compile time. An element admits its segments when every sequence of children they could stand for is in its content model's language, with each child's category widened to those it is valid wherever.
- An element valid only inside a particular parent, such as `li`, `dt`, `tr`, `summary`, `caption`, `source`, or `rt`, has a category of its own. One whose content model depends on its context takes one of several categories: `a` and the other transparent elements take phrasing or flow content, `noscript` in `head` holds only `link`, `meta`, and `style`, `source` takes `pictureSource` in a `picture`, and `div` takes `descriptionGroup` in a `dl`.
- Where a content model admits a mixture in any number, such as `ul`'s list items and script-supporting elements, the mixture is a category its members widen to, so that every list of children has one category. Script-supporting elements may so stand anywhere the standard admits them, including between a table's parts and within a group of terms and descriptions.
- Inter-element whitespace is a node of a category of its own, which drops out where the content model is not phrasing content and is text elsewhere. It widens to text and to exactly the categories that stand only repeated where whitespace may, never to one that also fills a required position, where it would stand in for the element required. Its proof that it is whitespace is `decide` for a literal.
- Not modelled: constraints on descendants rather than children, such as no interactive content inside `a`, and rules that depend on attributes, such as a media element with a `src` taking no `source` children, or `link` and `meta` being phrasing content only with certain attributes.

## SVG and MathML

- SVG follows [SVG 2](https://www.w3.org/TR/2026/CR-SVG2-20261006/) (W3C Candidate Recommendation Snapshot, 6 October 2026), with the filter primitives of [Filter Effects Module Level 1](https://www.w3.org/TR/2018/WD-filter-effects-1-20181218/) (W3C Working Draft, 18 December 2018), `clipPath` and `mask` from [CSS Masking Module Level 1](https://www.w3.org/TR/2021/CRD-css-masking-1-20210805/) (W3C Candidate Recommendation Draft, 5 August 2021), and the animation elements of [SVG Animations Level 2](https://svgwg.org/specs/animations/) (Editor's Draft, 14 September 2025, which the W3C has not published). Elements those specifications removed, such as SVG fonts, `tref`, and `animateColor`, are absent.
- `svg` is phrasing content in HTML and a container in SVG. Each SVG element has a category of its own, valid wherever the named categories it belongs to are, such as shape or animation elements, and wherever the content of an element that lists it or them may stand. SVG `a` holds what its parent holds, taking one of four categories: content of a container, `text`, `tspan`, or `textPath`.
- `foreignObject`, `title`, `desc`, and `metadata` admit any elements or character data, HTML included. `feDiffuseLighting` and `feSpecularLighting` hold exactly one light source, and `animateMotion` at most one `mpath`.
- MathML follows [MathML Core](https://www.w3.org/TR/2025/CR-mathml-core-20250624/) (W3C Candidate Recommendation Snapshot, 24 June 2025), whose rules say how elements lay out rather than which children are valid. The content models here are those its layout rules treat as well formed: two children for `mfrac`, `mroot`, `msub`, `msup`, `munder`, and `mover`, three for `msubsup` and `munderover`, `mmultiscripts` as its base, pairs of scripts, and optionally `mprescripts` and more pairs, `mtable` of `mtr` of `mtd`, and `semantics` as an expression followed by annotations.
- `math` is phrasing content in HTML. Token elements hold text and HTML phrasing content, and `annotation-xml` takes one of two categories, one holding HTML flow content as its `encoding` attribute allows and the other MathML or SVG, which a caller chooses as for `source`. Elements outside MathML Core, such as content MathML, need an unchecked element.

## Escape hatches

- A custom element's name must be a valid custom element name. Its categories and content model are those `Web.vocabWith` declares for its name, checked like any other, or else the standard's: phrasing or flow content, transparent. `Web.elemWith`, `Web.NodeWith`, and their siblings build nodes of such a vocabulary, and `Vocabulary.elem` and its siblings of any.
- An unchecked element takes a namespace, a name, a category, a payload, and children of any categories.
- Verbatim markup is a leaf valid in any category.
- `Node.hasUnchecked` and `Node.hasVerbatim`, and their counterparts on `Tree`, say whether a tree uses either, so that a consumer can refuse it.

## For macro authors

- A child whose category is unknown when the tree is elaborated, such as an absent optional child or an empty list literal, makes elaboration fail or slow down sharply. `Seg.ofOption` and `Seg.ofList` take the category explicitly.
- Lean defers default-argument proofs to the end of a term, where thousands of them slow down together. A large generated term should prove each distinct element, category, and kinds of children once as an auxiliary theorem and pass it explicitly; `test/Main.lean` generates such a term of 2,000 elements, which elaborates in about 3 seconds. `Vocabulary.admits_of_kinds` reuses a proof across children whose kinds differ but coarsen alike.
- `Vocabulary.infer` finds the category an element takes from its children and its parent's content model, and `Html.Elem.ofName?`, `Svg.Elem.ofName?`, and `Mathml.Elem.ofName?` the element a tag name names. Text a macro knows to be whitespace, such as JSX's space between elements, should be a `Web.ws` node, which may stand where text may not.
- `Tree.isInline` says whether whitespace beside a node would render, so that a pretty-printer must not put any there; `Tree.isInlineIn` and `Tree.childrenInline` judge a child by its parent too, so that nothing in `head` counts. `Tree.keepsWhitespace` says whether whitespace renders among an element's children wherever it stands, as in SVG `text` and MathML token elements.

## Formal verification

- Acceptance is lean-regular's `Accepts`, whose decision procedure lean-regular proves correct.
- `Node.valid_erase`: a typed node erases to a tree satisfying `Tree.Valid`, which is stated on the erased tree alone, so that a consumer of the erased tree can rely on it without the typed one. It holds of widened nodes because each vocabulary proves widening a preorder.
- `Node.erase_map`: the payload map commutes with erasure, and `NodeF` is a `LawfulFunctor`.
- `Vocabulary.infer_spec`: an inferred category is one the element may take, and admits its children.

## License

This library is released under the Apache 2.0 license. See the LICENSE file for the complete license text.
