/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModelTests.Helpers
meta import HtmlModelTests.Helpers

/-! A prototype of `html!` elaborating to this library: an untyped tree shaped like lasm's
`Lasm.UI.Html Msg`, keys and attributes aside, is placed into typed nodes by tag name and
category inference, then erased back. -/

namespace HtmlModelTests.Lasm

open HtmlModel Web Regular

inductive Raw where
  | text (s : String)
  | elem (ns : Namespace) (tag : String) (children : List Raw)
  deriving BEq, Repr

abbrev Placed := (k : SegK Cat) × Seg vocab Unit k

def Placed.cat : Placed → Cat
  | ⟨.one c, _⟩ => c
  | _ => .text

/-- An element of category `c`, if it admits the children placed for it. -/
def build (e : Html.Elem) (c : Html.Cat) (kids : List Placed) : Option Placed :=
  if hc : Cat.html c ∈ vocab.cats (.html e) then
    if ok : vocab.Admits (.html e) (.html c) (kids.map (·.1)) then
      some ⟨.one (.html c), .one (Web.elem (.html e) (.html c) () (Segs.ofList kids) hc ok)⟩
    else none
  else none

mutual
/-- Whitespace becomes a whitespace segment, so that it may stand where text may not. An element
tries each category that fits its parent, keeping the least that admits its children. -/
def place (parent : Regex Cat) : Raw → Option Placed
  | .text s => if h : isWhitespace s = true then some ⟨.ws, .ws s h⟩ else some ⟨.one .text, .one (.text s)⟩
  | .elem .html tag ch =>
    match Html.Elem.ofName? tag with
    | none => none
    | some e =>
      let built := (e.cats.filter fun c => parent.letters.any (vocab.widens (.html c))).filterMap
        fun c => (placeAll (vocab.spec (.html e) (.html c)).grammar ch).bind (build e c)
      built.find? fun p => built.all fun q => vocab.widens p.cat q.cat
  | .elem _ _ _ => none
def placeAll (parent : Regex Cat) : List Raw → Option (List Placed)
  | [] => some []
  | r :: rs => do pure ((← place parent r) :: (← placeAll parent rs))
end

mutual
def toRaw : Web.Tree Unit → Raw
  | .text s | .verbatim _ s => .text s
  | .elem e _ _ ch => .elem (vocab.ns e) (vocab.name e) (toRawAll ch)
  | .unchecked ns name _ _ ch => .elem ns name (toRawAll ch)
def toRawAll : List (Web.Tree Unit) → List Raw
  | [] => []
  | t :: ts => toRaw t :: toRawAll ts
end

def roundTrip (r : Raw) : Option Raw :=
  (place (.sym (.html .document)) r).bind fun ⟨_, x⟩ => (Seg.erase x).head?.map toRaw

def h (tag : String) (children : List Raw) : Raw := .elem .html tag children

def page : Raw :=
  h "html" [
    h "head" [.text "\n", h "meta" [], h "link" [], h "title" [.text "T"]],
    h "body" [
      h "h1" [.text "Hi"],
      h "p" [.text "Read ", h "a" [.text "this"], .text "."],
      h "a" [h "p" [.text "A block link"]],
      h "ul" [.text "\n", h "li" [.text "x"], .text "\n", h "li" [.text "y"], h "script" []],
      h "dl" [h "div" [h "dt" [.text "k"], h "dd" [.text "v"]]],
      h "table" [h "caption" [], h "tr" [h "td" [.text "1"]]],
      h "picture" [h "source" [], h "img" []],
      h "video" [h "source" [], .text "Fallback"]]]

#guard roundTrip page == some page

-- Invalid trees are refused, not repaired.
#guard roundTrip (h "html" [h "head" [h "title" []], h "body" [h "p" [h "div" []]]]) == none
#guard roundTrip (h "html" [h "head" [h "title" []], h "body" [h "ul" [.text "x"]]]) == none
#guard roundTrip (h "html" [h "head" [], h "body" []]) == none

end HtmlModelTests.Lasm
