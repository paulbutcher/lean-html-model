/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Web

@[expose] public section

namespace HtmlModel.Web

variable {α : Type}

mutual
/-- Whether whitespace beside this node would render, so that a pretty-printer must not put any
there. Text, verbatim markup, and elements whose layout is unknown, unchecked and custom ones,
count as inline. -/
def _root_.HtmlModel.Tree.isInline : Tree α → Bool
  | .text _ | .verbatim _ _ | .unchecked .. | .elem (.custom ..) _ _ _ => true
  | .elem (.html e) (.html c) _ ch =>
    c.isInline || (c == .flow && e.isTransparent && Tree.allInline ch)
  | .elem _ (.html c) _ _ => c.isInline
  | .elem (.svg e) (.svg c) _ _ => e.keepsWhitespace || c.inText
  | .elem (.mathml _) (.mathml _) _ _ => false
  | .elem _ _ _ _ => true
/-- Whether every one of `ts` lays out inline. -/
def _root_.HtmlModel.Tree.allInline : List (Tree α) → Bool
  | [] => true
  | t :: ts => Tree.isInline t && Tree.allInline ts
end

/-- Whether whitespace beside `t`, standing among the children of `parent`, would render. As
`Tree.isInline`, except that nothing in `head`, or in a `noscript` standing there, renders. -/
def _root_.HtmlModel.Tree.isInlineIn (parent t : Tree α) : Bool :=
  match parent with
  | .elem _ (.html .head) _ _ | .elem (.html .noscript) (.html .metadata) _ _ => false
  | _ => t.isInline

/-- Whether every one of this element's children lays out inline within it. -/
def _root_.HtmlModel.Tree.childrenInline (t : Tree α) : Bool :=
  match t with
  | .elem _ _ _ ch | .unchecked _ _ _ _ ch => ch.all t.isInlineIn
  | .text _ | .verbatim _ _ => true

/-- Whether whitespace renders among this element's children wherever it stands, so that a
pretty-printer may add none there even beside children that are not inline. -/
def _root_.HtmlModel.Tree.keepsWhitespace : Tree α → Bool
  | .elem (.html .pre) _ _ _ | .elem (.html .textarea) _ _ _ => true
  | .elem (.svg e) (.svg c) _ _ => e.keepsWhitespace || c.inText
  | .elem (.mathml e) _ _ _ => e.isToken
  | _ => false

end HtmlModel.Web
