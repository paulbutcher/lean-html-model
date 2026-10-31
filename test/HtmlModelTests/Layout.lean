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

end HtmlModelTests.Layout
