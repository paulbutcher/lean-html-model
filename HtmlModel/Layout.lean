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
  | .elem (.html _) .text _ _ => true
/-- Whether every one of `ts` lays out inline. -/
def _root_.HtmlModel.Tree.allInline : List (Tree α) → Bool
  | [] => true
  | t :: ts => Tree.isInline t && Tree.allInline ts
end

end HtmlModel.Web
