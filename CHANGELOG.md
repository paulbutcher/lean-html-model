# Changelog

## [0.4.0] - 2026-11-01

* `HtmlPayload` and `EventAttr`, the classes a markup macro builds payloads with
* `HtmlModel.Quote`, `ToExpr` instances for elements and categories
* `Web.childNamespace` and `Web.Elem.ofNameIn?`, the namespace an element's children are read in and the element a tag name names there
* `admits` tries `Vocabulary.admits_of_kinds` first, so that an element of many children in any order is decided at once

## [0.3.1] - 2026-11-01

* `Tree.isInlineIn` and `Tree.childrenInline` judge layout by the parent too, so that nothing in `head` counts as inline

## [0.3.0] - 2026-11-01

* Breaking: a node widens to any category it is valid wherever, keeping the category it was checked as, so that a list known only at run time may mix categories
* Breaking: each mixture a content model admits in any number, such as list items and script-supporting elements, is a category its members widen to
* Breaking: inter-element whitespace is a node of its own category, replacing the whitespace segment, and widens only to categories that never fill a required position
* Breaking: nodes and trees are built on a `Signature` derived from the vocabulary, so that building and erasing a tree reaches none of its tables or grammars at run time
* Breaking: custom elements' content models are declared by the vocabulary, `Web.vocabWith`, and an undeclared one takes the standard's transparent content model
* Breaking: `link` and `meta` take one category, which widens to metadata and phrasing content
* Nodes coerce to any category they widen to
* `Segs.append` joins two runs of segments
* Helpers that take the vocabulary, `Vocabulary.elem` and its siblings, and `Web.elemWith` and its siblings for declared custom elements
* SVG's `discard` element

## [0.2.0] - 2026-10-31

* Requires lean-regular 0.2.0

## [0.1.1] - 2026-10-31

* Groups are made of segments, so repetition nests, as in `dl` groups and ruby segments built from run-time lists
* New segment kinds: a nonempty list, and a choice between two runs of segments made at run time
* Breaking: `SegK.groups` takes segment kinds, `Group` is removed in favour of `Segs`, and `SegK` no longer derives `DecidableEq`

## [0.1.0] - 2026-10-31

* A tree of HTML, SVG, and MathML Core elements indexed by category, each element's children checked against its content model by lean-regular at compile time, lists known only at run time included
* Erasure to an untyped tree, proven to satisfy a validity predicate stated on the erased tree alone, and a payload map that commutes with it
* Custom elements, unchecked elements, and verbatim markup, each of which a consumer can detect and refuse
* A rejected element's error names the segment of its children that is wrong
* Category inference, element lookup by name, and whether whitespace beside a node would render, for macros and pretty-printers built on the tree
