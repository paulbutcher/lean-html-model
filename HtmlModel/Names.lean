/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

@[expose] public section

namespace HtmlModel

/-- The namespace an element is created in. -/
inductive Namespace where
  | html
  | svg
  | mathml
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- HTML's ASCII whitespace. -/
def isAsciiWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\x0C' || c == '\r'

/-- Whether `s` is inter-element whitespace. The empty string is. -/
def isWhitespace (s : String) : Bool := s.toList.all isAsciiWhitespace

def isLowerAlpha (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

def isLowerNameChar (c : Char) : Bool := isLowerAlpha c || c.isDigit || c == '-'

/-- A lowercase ASCII letter followed by lowercase ASCII letters, digits, and `-`: names a renderer
can emit unquoted and an HTML parser reads back unchanged. -/
def isLowerName (s : String) : Bool :=
  match s.toList with
  | c :: cs => isLowerAlpha c && cs.all isLowerNameChar
  | [] => false

/-- The SVG element names the HTML parser restores from lowercase; any other name in mixed case
would come back lowercased from text/html. -/
def svgAdjustedNames : List String :=
  ["altGlyph", "altGlyphDef", "altGlyphItem", "animateColor", "animateMotion",
    "animateTransform", "clipPath", "feBlend", "feColorMatrix", "feComponentTransfer",
    "feComposite", "feConvolveMatrix", "feDiffuseLighting", "feDisplacementMap",
    "feDistantLight", "feDropShadow", "feFlood", "feFuncA", "feFuncB", "feFuncG", "feFuncR",
    "feGaussianBlur", "feImage", "feMerge", "feMergeNode", "feMorphology", "feOffset",
    "fePointLight", "feSpecularLighting", "feSpotLight", "feTile", "feTurbulence",
    "foreignObject", "glyphRef", "linearGradient", "radialGradient", "textPath"]

/-- Whether an unchecked element may be called `name` in `ns`: a name that survives being
emitted and parsed back as text/html. -/
def Namespace.validName : Namespace → String → Bool
  | .svg, name => isLowerName name || svgAdjustedNames.contains name
  | .html, name | .mathml, name => isLowerName name

/-- The HTML standard's PCENChar, the characters of a custom element name. -/
def isPCENChar (c : Char) : Bool :=
  let n := c.toNat
  c == '-' || c == '.' || c.isDigit || c == '_' || isLowerAlpha c || n == 0xB7 ||
    (0xC0 ≤ n && n ≤ 0xD6) || (0xD8 ≤ n && n ≤ 0xF6) || (0xF8 ≤ n && n ≤ 0x37D) ||
    (0x37F ≤ n && n ≤ 0x1FFF) || (0x200C ≤ n && n ≤ 0x200D) || (0x203F ≤ n && n ≤ 0x2040) ||
    (0x2070 ≤ n && n ≤ 0x218F) || (0x2C00 ≤ n && n ≤ 0x2FEF) || (0x3001 ≤ n && n ≤ 0xD7FF) ||
    (0xF900 ≤ n && n ≤ 0xFDCF) || (0xFDF0 ≤ n && n ≤ 0xFFFD) || (0x10000 ≤ n && n ≤ 0xEFFFF)

/-- Names the HTML standard reserves because SVG and MathML already use them. -/
def reservedCustomElementNames : List String :=
  ["annotation-xml", "color-profile", "font-face", "font-face-src", "font-face-uri",
    "font-face-format", "font-face-name", "missing-glyph"]

/-- The HTML standard's valid custom element name. -/
def isCustomElementName (s : String) : Bool :=
  match s.toList with
  | c :: cs => isLowerAlpha c && cs.all isPCENChar && cs.contains '-' &&
      !reservedCustomElementNames.contains s
  | [] => false

end HtmlModel
