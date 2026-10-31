/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModel

namespace HtmlModelTests.Names

open HtmlModel

example : isWhitespace " \t\n\r\x0C" = true := by decide
example : isWhitespace "" = true := by decide
example : isWhitespace " x " = false := by decide

example : isCustomElementName "my-card" = true := by decide
example : isCustomElementName "x-é" = true := by decide
example : isCustomElementName "mycard" = false := by decide
example : isCustomElementName "My-card" = false := by decide
example : isCustomElementName "my-Card" = false := by decide
example : isCustomElementName "-card" = false := by decide
example : isCustomElementName "annotation-xml" = false := by decide
example : isCustomElementName "font-face" = false := by decide

example : Namespace.html.validName "selectedcontent" = true := by decide
example : Namespace.html.validName "fencedframe" = true := by decide
example : Namespace.html.validName "selectedContent" = false := by decide
example : Namespace.html.validName "x y" = false := by decide
example : Namespace.html.validName "" = false := by decide
example : Namespace.svg.validName "clipPath" = true := by decide
example : Namespace.svg.validName "newelement" = true := by decide
example : Namespace.svg.validName "newElement" = false := by decide
example : Namespace.mathml.validName "mfrac" = true := by decide
example : Namespace.mathml.validName "clipPath" = false := by decide

end HtmlModelTests.Names
