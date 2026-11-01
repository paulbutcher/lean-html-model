/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModel

namespace HtmlModelTests.Namespaces

open HtmlModel Web

example : childNamespace (.svg .text) (.svg (.el .text)) = some .svg := by decide +kernel
example : Elem.ofNameIn? (childNamespace (.svg .text) (.svg (.el .text))) "a" = some (.svg .a) := by
  decide +kernel
example : Elem.ofNameIn? (childNamespace (.mathml .mi) (.mathml .expr)) "b" = some (.html .b) := by
  decide +kernel
example : Elem.ofNameIn? (childNamespace (.mathml .annotationXml) (.mathml .annotationXmlHtml)) "p" =
    some (.html .p) := by decide +kernel
example : Elem.ofNameIn? (childNamespace (.mathml .annotationXml) (.mathml .annotationXml)) "svg" =
    some (.svg .svg) := by decide +kernel
example : childNamespace (.svg .foreignObject) (.svg (.el .foreignObject)) = some .html := by
  decide +kernel
example : childNamespace (.svg .title) (.svg (.el .title)) = some .html := by decide +kernel
example : childNamespace (.svg .svg) (.html .phrasing) = some .svg := by decide +kernel
example : childNamespace (.mathml .math) (.html .phrasing) = some .mathml := by decide +kernel
example : childNamespace (.html .div) (.html .flow) = some .html := by decide +kernel
example : childNamespace (.html .br) (.html .phrasing) = none := by decide +kernel
example : childNamespace (.html .title) (.html .title) = none := by decide +kernel

example : Elem.ofNameIn? (some .html) "svg" = some (.svg .svg) := by decide +kernel
example : Elem.ofNameIn? (some .html) "math" = some (.mathml .math) := by decide +kernel
example : Elem.ofNameIn? (some .html) "circle" = none := by decide +kernel
example : Elem.ofNameIn? (some .svg) "div" = none := by decide +kernel

example : Elem.ofNameIn? (some .html) "a" = some (.html .a) := by decide +kernel
example : Elem.ofNameIn? (some .svg) "a" = some (.svg .a) := by decide +kernel
example : Elem.ofNameIn? (some .html) "script" = some (.html .script) := by decide +kernel
example : Elem.ofNameIn? (some .svg) "script" = some (.svg .script) := by decide +kernel
example : Elem.ofNameIn? (some .html) "style" = some (.html .style) := by decide +kernel
example : Elem.ofNameIn? (some .svg) "style" = some (.svg .style) := by decide +kernel
example : Elem.ofNameIn? (some .html) "title" = some (.html .title) := by decide +kernel
example : Elem.ofNameIn? (some .svg) "title" = some (.svg .title) := by decide +kernel

example : Elem.ofNameIn? none "a" = some (.html .a) := by decide +kernel
example : Elem.ofNameIn? none "title" = some (.html .title) := by decide +kernel
example : Elem.ofNameIn? none "circle" = some (.svg .circle) := by decide +kernel
example : Elem.ofNameIn? none "mfrac" = some (.mathml .mfrac) := by decide +kernel

example : Elem.ofNameIn? (some .mathml) "annotation-xml" = some (.mathml .annotationXml) := by
  decide +kernel
example : Elem.ofNameIn? none "annotation-xml" = some (.mathml .annotationXml) := by decide +kernel
example : Elem.ofNameIn? (some .html) "annotation-xml" = none := by decide +kernel

example : Elem.ofNameIn? (some .html) "my-card" = some (.custom "my-card" rfl) := by decide +kernel
example : Elem.ofNameIn? none "my-card" = some (.custom "my-card" rfl) := by decide +kernel
example : Elem.ofNameIn? (some .svg) "my-card" = none := by decide +kernel
example : Elem.ofNameIn? (some .mathml) "my-card" = none := by decide +kernel

end HtmlModelTests.Namespaces
