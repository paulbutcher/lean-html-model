/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModelTests.Helpers

namespace HtmlModelTests.Layout

open HtmlModel Web

example : (txt "x").erase.isInline = true := by decide +kernel
example : (el .span .phrasing segs![]).erase.isInline = true := by decide +kernel
example : (el .rt .rubyText segs![]).erase.isInline = true := by decide +kernel
example : (el .div .flow segs![.one (txt "x")]).erase.isInline = false := by decide +kernel
example : (el .li .listItem segs![]).erase.isInline = false := by decide +kernel
example : (el .option .option segs![]).erase.isInline = false := by decide +kernel

-- A transparent element is inline when all it holds is.
example : (el .a .flow segs![.one (txt "x")]).erase.isInline = true := by decide +kernel
example : (el .a .flow segs![.one (el .p .paragraph segs![])]).erase.isInline = false := by decide +kernel

-- Nothing is known about how verbatim markup or an unchecked element lays out.
example : (Node.verbatim "<div></div>" : N (.html .flow)).erase.isInline = true := by decide +kernel
example : (Web.unchecked .html "fencedframe" (.html .flow) () .nil : N (.html .flow)).erase.isInline = true := by
  decide +kernel

-- Nothing in `head` renders, so `link` and `meta` lay out inline only among phrasing content.
def metaTag : N (.html .phrasingMetadata) := el .meta .phrasingMetadata segs![]
def linkTag : N (.html .phrasingMetadata) := el .link .phrasingMetadata segs![]
def headNoscript : N (.html .metadata) :=
  let ch : List (N (.html .noscriptMetadata)) := [metaTag, linkTag]
  el .noscript .metadata segs![.many (Nodes.ofList ch)]
def head : N (.html .head) :=
  let ch : List (N (.html .metadata)) := [metaTag, linkTag, headNoscript]
  el .head .head segs![.many (Nodes.ofList ch), .one (el .title .title segs![.one (txt "T")])]
def para : N (.html .paragraph) :=
  el .p .paragraph segs![.many (Nodes.ofList ([txt "x", metaTag] : List (N (.html .phrasing))))]
def bodyNoscript : N (.html .phrasing) := el .noscript .phrasing segs![.one (txt "x")]

example : head.erase.childrenInline = false := by decide +kernel
example : head.erase.isInlineIn metaTag.erase = false := by decide +kernel
example : headNoscript.erase.childrenInline = false := by decide +kernel
example : headNoscript.erase.isInlineIn linkTag.erase = false := by decide +kernel
example : para.erase.childrenInline = true := by decide +kernel
example : para.erase.isInlineIn metaTag.erase = true := by decide +kernel
example : bodyNoscript.erase.childrenInline = true := by decide +kernel
example : para.erase.isInlineIn bodyNoscript.erase = true := by decide +kernel

end HtmlModelTests.Layout
