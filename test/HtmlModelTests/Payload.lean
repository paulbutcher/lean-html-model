/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModelTests.Helpers

namespace HtmlModelTests.Payload

open HtmlModel Web

/-- Attributes in the order first written, the last occurrence of a name giving its value. -/
abbrev Attrs := List (String × String)

def set (name value : String) (p : Attrs) : Attrs :=
  if p.any (·.1 == name) then p.map fun (n, v) => (n, if n == name then value else v)
  else p ++ [(name, value)]

instance : HtmlPayload Attrs where
  empty := []
  attr := set
  flag name on p := if on then set name "" p else p.filter (·.1 != name)
  style name value p := set "style" (((p.lookup "style").getD "") ++ s!"{name}:{value};") p
  key := set "key"
  append p q := q.foldl (fun p (n, v) => set n v p) p

instance : EventAttr Attrs "onClick" String where
  on := set "onclick"

open HtmlPayload in
def button : Web.Node Attrs (.html .phrasing) :=
  Web.elem (.html .button) (.html .phrasing)
    (EventAttr.on (event := "onClick") "go()"
      (append (style "color" "red" (flag "disabled" false (attr "class" "a" empty)))
        (attr "class" "b" (key "k" empty))))
    segs![.one (.text "Go")]

example : (match button.erase with | .elem _ _ p _ => p | _ => []) =
    [("class", "b"), ("style", "color:red;"), ("key", "k"), ("onclick", "go()")] := by
  decide +kernel

end HtmlModelTests.Payload
