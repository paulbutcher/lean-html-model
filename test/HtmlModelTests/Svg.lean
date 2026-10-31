/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModelTests.Helpers

namespace HtmlModelTests.Svg

open HtmlModel Web

-- `svg` is phrasing content in HTML, and a container in SVG.
example : N (.html .paragraph) :=
  el .p .paragraph segs![.one (txt "A circle: "), .one (inlineSvg segs![.one (sv .circle segs![])])]
example : N (.svg (.el .g)) := sv .g segs![.one (sv .svg segs![.one (sv .rect segs![])])]

-- After the specifications' examples: a gradient-filled rectangle with a title.
example : N (.html .phrasing) :=
  inlineSvg segs![.ws "\n",
    .one (sv .defs segs![.one (sv .linearGradient segs![.one (sv .stop segs![]), .ws "\n", .one (sv .stop segs![])])]),
    .one (sv .rect segs![.one (sv .title segs![.one (txt "A box")])])]

-- Text, character data mixed with text content child elements.
example : N (.svg (.el .text)) :=
  sv .text segs![.one (txt "Hello, "), .one (sv .tspan segs![.one (txt "out")]), .one (txt " there"),
    .one (sv .textPath segs![.one (txt "along a path"), .one (sv .tspan segs![])])]

-- A drop shadow filter, and lighting with exactly one light source in any position.
example : N (.svg (.el .filter)) :=
  sv .filter segs![.one (sv .feGaussianBlur segs![]), .one (sv .feOffset segs![]),
    .one (sv .feMerge segs![.one (sv .feMergeNode segs![]), .one (sv .feMergeNode segs![])])]
example : N (.svg (.el .filter)) :=
  sv .filter segs![.one (sv .feDiffuseLighting segs![.one (sv .desc segs![]), .one (sv .fePointLight segs![])]),
    .one (sv .feSpecularLighting segs![.one (sv .feDistantLight segs![]), .one (sv .script segs![])])]
example : N (.svg (.el .feComponentTransfer)) :=
  sv .feComponentTransfer segs![.one (sv .feFuncR segs![]), .one (sv .feFuncG segs![]), .one (sv .feFuncR segs![])]

-- Animation: at most one `mpath`, anywhere among the descriptive elements.
example : N (.svg (.el .animateMotion)) :=
  sv .animateMotion segs![.one (sv .title segs![]), .one (sv .mpath segs![]), .one (sv .desc segs![])]
example : N (.svg (.el .rect)) :=
  sv .rect segs![.one (sv .animate segs![]), .one (sv .set segs![]), .one (sv .animateTransform segs![])]

-- `switch`, with HTML in a `foreignObject`, and HTML in a `desc`.
example : N (.svg (.el .switch)) :=
  sv .switch segs![.one (sv .foreignObject segs![.one (el .p .paragraph segs![.one (txt "HTML")])]),
    .one (sv .text segs![.one (txt "SVG")])]
example : N (.svg (.el .desc)) := sv .desc segs![.one (el .span .phrasing segs![.one (txt "A chart")])]

-- Clipping paths and masks.
example : N (.svg (.el .clipPath)) :=
  sv .clipPath segs![.one (sv .rect segs![]), .one (sv .text segs![.one (txt "Clip")]), .one (sv .use segs![])]
example : N (.svg (.el .mask)) := sv .mask segs![.one (sv .rect segs![]), .one (sv .g segs![])]

-- `a` holds what its parent holds: graphics in a `g`, text in a `text`.
example : N (.svg (.el .g)) := sv .g segs![.one (sa .aContainer segs![.one (sv .rect segs![]), .one (sv .text segs![])])]
example : N (.svg (.el .text)) := sv .text segs![.one (sa .aText segs![.one (txt "link"), .one (sv .tspan segs![])])]
example : N (.svg (.el .tspan)) := sv .tspan segs![.one (sa .aTspan segs![.one (txt "link")])]

-- a shape in a tspan
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <tspan> as Cat.svg (Svg.Cat.el Svg.Elem.tspan) does not admit its children: segment 1, of category Cat.svg (Svg.Cat.el Svg.Elem.rect), cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .tspan)) := sv .tspan segs![.one (sv .rect segs![])]

-- character data directly in a g
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <g> as Cat.svg (Svg.Cat.el Svg.Elem.g) does not admit its children: segment 1, of category Cat.text, cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .g)) := sv .g segs![.one (txt "x")]

-- a transfer function outside feComponentTransfer
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <filter> as Cat.svg (Svg.Cat.el Svg.Elem.filter) does not admit its children: segment 1, of category Cat.svg (Svg.Cat.el Svg.Elem.feFuncR), cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .filter)) := sv .filter segs![.one (sv .feFuncR segs![])]

-- two light sources
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <feDiffuseLighting> as Cat.svg (Svg.Cat.el Svg.Elem.feDiffuseLighting) does not admit its children: segment 2, of category Cat.svg (Svg.Cat.el Svg.Elem.feSpotLight), cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .feDiffuseLighting)) := sv .feDiffuseLighting segs![.one (sv .fePointLight segs![]), .one (sv .feSpotLight segs![])]

-- no light source
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <feSpecularLighting> as Cat.svg (Svg.Cat.el Svg.Elem.feSpecularLighting) does not admit its children: they end before it is complete
-/
#guard_msgs in
example : N (.svg (.el .feSpecularLighting)) := sv .feSpecularLighting segs![.one (sv .desc segs![])]

-- two mpaths
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <animateMotion> as Cat.svg (Svg.Cat.el Svg.Elem.animateMotion) does not admit its children: segment 2, of category Cat.svg (Svg.Cat.el Svg.Elem.mpath), cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .animateMotion)) := sv .animateMotion segs![.one (sv .mpath segs![]), .one (sv .mpath segs![])]

-- a stop outside a gradient
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <g> as Cat.svg (Svg.Cat.el Svg.Elem.g) does not admit its children: segment 1, of category Cat.svg (Svg.Cat.el Svg.Elem.stop), cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .g)) := sv .g segs![.one (sv .stop segs![])]

-- a container in a clipPath
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <clipPath> as Cat.svg (Svg.Cat.el Svg.Elem.clipPath) does not admit its children: segment 1, of category Cat.svg (Svg.Cat.el Svg.Elem.g), cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .clipPath)) := sv .clipPath segs![.one (sv .g segs![])]

-- an a in an a
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <a> as Cat.svg Svg.Cat.aContainer does not admit its children: segment 1, of category Cat.svg Svg.Cat.aContainer, cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg .aContainer) := sa .aContainer segs![.one (sa .aContainer segs![])]

-- an a placed for text content inside a g
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <g> as Cat.svg (Svg.Cat.el Svg.Elem.g) does not admit its children: segment 1, of category Cat.svg Svg.Cat.aText, cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .g)) := sv .g segs![.one (sa .aText segs![.one (txt "x")])]

-- an SVG shape directly in HTML
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <div> as Cat.html Html.Cat.flow does not admit its children: segment 1, of category Cat.svg (Svg.Cat.el Svg.Elem.circle), cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .div .flow segs![.one (sv .circle segs![])]

-- HTML directly in SVG
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <g> as Cat.svg (Svg.Cat.el Svg.Elem.g) does not admit its children: segment 1, of category Cat.html Html.Cat.flow, cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .g)) := sv .g segs![.one (el .div .flow segs![])]

-- a merge node outside feMerge
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <filter> as Cat.svg (Svg.Cat.el Svg.Elem.filter) does not admit its children: segment 1, of category Cat.svg (Svg.Cat.el Svg.Elem.feMergeNode), cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .filter)) := sv .filter segs![.one (sv .feMergeNode segs![])]

-- an animation where feComponentTransfer admits none
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <feComponentTransfer> as Cat.svg (Svg.Cat.el Svg.Elem.feComponentTransfer) does not admit its children: segment 1, of category Cat.svg (Svg.Cat.el Svg.Elem.animate), cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .feComponentTransfer)) := sv .feComponentTransfer segs![.one (sv .animate segs![])]

-- a filter primitive outside a filter
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <g> as Cat.svg (Svg.Cat.el Svg.Elem.g) does not admit its children: segment 1, of category Cat.svg (Svg.Cat.el Svg.Elem.feGaussianBlur), cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .g)) := sv .g segs![.one (sv .feGaussianBlur segs![])]

-- an element in a style
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <style> as Cat.svg (Svg.Cat.el Svg.Elem.style) does not admit its children: segment 1, of category Cat.svg (Svg.Cat.el Svg.Elem.g), cannot follow the segments before it
-/
#guard_msgs in
example : N (.svg (.el .style)) := sv .style segs![.one (sv .g segs![])]

def grammarOf (e : Elem) (c : Cat) := (vocab.spec e c).grammar

-- Inference places `svg` and `a` by context, and `a` by what it holds.
example : vocab.infer (.svg .svg) [] (grammarOf (.html .div) (.html .flow)) = some (.html .phrasing) := by
  decide +kernel
example : vocab.infer (.svg .svg) [] (grammarOf (.svg .g) (.svg (.el .g))) = some (.svg (.el .svg)) := by
  decide +kernel
example : vocab.infer (.svg .a) [.one (.svg (.el .rect))] (grammarOf (.svg .g) (.svg (.el .g)))
    = some (.svg .aContainer) := by
  decide +kernel
example : vocab.infer (.svg .a) [.one .text] (grammarOf (.svg .text) (.svg (.el .text))) = some (.svg .aText) := by
  decide +kernel

-- Erasure names an SVG element in its own namespace, with its case.
example : (sv .linearGradient segs![]).erase.tag = some (.svg, "linearGradient") := by decide +kernel

-- Whitespace renders beside a `tspan` and among a `text`'s children, but not beside a shape.
example : (sv .tspan segs![]).erase.isInline = true := by decide +kernel
example : (sv .rect segs![]).erase.isInline = false := by decide +kernel
example : (sv .text segs![]).erase.keepsWhitespace = true := by decide +kernel
example : (sv .g segs![]).erase.keepsWhitespace = false := by decide +kernel
example : (inlineSvg segs![]).erase.isInline = true := by decide +kernel

end HtmlModelTests.Svg
