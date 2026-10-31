# Changelog

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
