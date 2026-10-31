/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HtmlModelTests

/-! Times elaborating three generated documents, each of which must take under `budgetMs`: one of
500 elements with default proofs, one of 500 mostly SVG elements with default proofs, and one of
2,000 in a single term, as a macro such as `html!`
would generate it, proving each distinct element, category and kinds of children once and reusing
the proof. -/

def budgetMs : Nat := 5000

/-- An element, its category, and the kinds of children its cached proofs are about. -/
structure Key where
  name : String
  elem : String
  cat : String
  segs : String

def keys : List Key := [
  ⟨"kDiv", "div", "flow", ".many (.html .flow)"⟩,
  ⟨"kSection", "div", "flow", ".ws, .one (.html .paragraph), .one (.html .flow), .one (.html .flow)"⟩,
  ⟨"kP1", "p", "paragraph", ".one .text, .one (.html .phrasing), .one (.html .phrasing)"⟩,
  ⟨"kP2", "p", "paragraph", ".one .text"⟩,
  ⟨"kSpan", "span", "phrasing", ".one .text"⟩,
  ⟨"kA", "a", "phrasing", ".one .text"⟩,
  ⟨"kUl", "ul", "flow", ".many (.html .listItem), .one (.html .scriptSupporting)"⟩,
  ⟨"kLi", "li", "listItem", ".one (.html .paragraph)"⟩,
  ⟨"kTable", "table", "flow", ".one (.html .tableBody)"⟩,
  ⟨"kTbody", "tbody", "tableBody", ".many (.html .tableRow)"⟩,
  ⟨"kTr", "tr", "tableRow", ".ws, .one (.html .tableCell), .one (.html .tableCell)"⟩,
  ⟨"kTd", "td", "tableCell", ".one .text"⟩,
  ⟨"kScript", "script", "scriptSupporting", ""⟩]

def keyOf (name : String) : Key := (keys.find? (·.name == name)).getD ⟨name, "", "", ""⟩

def el (cached : Bool) (key : String) (segs : String) : String :=
  let k := keyOf key
  let call := s!"el .{k.elem} .{k.cat} segs![{segs}]"
  if cached then s!"{call} (hc := {key}_cat) (ok := {key})"
  else call

/-- Twenty elements, the mix of an ordinary page. -/
def section_ (cached : Bool) (i : Nat) : String :=
  let el := el cached
  let lis := ", ".intercalate ((List.range 3).map fun j =>
    el "kLi" s!".one ({el "kP2" s!".one (txt \"item {j}\")"})")
  let td (s : String) := el "kTd" s!".one (txt \"{s}\")"
  let trs := ", ".intercalate ((List.range 2).map fun _ =>
    el "kTr" s!".ws \"\\n\", .one ({td "a"}), .one ({td "b"})")
  el "kSection" (s!".ws \"\\n\",\n    " ++
    s!".one ({el "kP1" s!".one (txt \"Section {i} \"), .one ({el "kSpan" ".one (txt \"x\")"}), .one ({el "kA" ".one (txt \"link\")"})"}),\n    " ++
    s!".one ({el "kUl" s!"nodes [{lis}], .one ({el "kScript" ""})"}),\n    " ++
    s!".one ({el "kTable" s!".one ({el "kTbody" s!"nodes [{trs}]"})"})")

def document (sections : Nat) (cached : Bool) : String :=
  let header := "import HtmlModelTests.Helpers\n\nopen HtmlModel Web HtmlModelTests Regular\n\n"
  let theorems := if cached then
      String.join (keys.map fun k =>
        s!"theorem {k.name}_cat : Cat.html .{k.cat} ∈ vocab.cats (.html .{k.elem}) := by decide\n" ++
        s!"theorem {k.name} : vocab.Admits (.html .{k.elem}) (.html .{k.cat}) [{k.segs}] := by decide +kernel\n") ++ "\n"
    else ""
  let body := ",\n  ".intercalate ((List.range sections).map (section_ cached))
  header ++ theorems ++ s!"def doc : N (.html .flow) := {el cached "kDiv" s!"nodes [\n  {body}]"}\n"

/-- About twenty-two elements, an HTML figure holding an SVG with a gradient, a filter, shapes, and text. -/
def svgSection (i : Nat) : String :=
  s!"el .div .flow segs![.one (el .p .paragraph segs![.one (txt \"Figure {i}\")]), .one (inlineSvg segs![.ws \"\\n\", " ++
  ".one (sv .defs segs![.one (sv .linearGradient segs![.one (sv .stop segs![]), .one (sv .stop segs![])]), " ++
  ".one (sv .filter segs![.one (sv .feGaussianBlur segs![]), .one (sv .feOffset segs![]), " ++
  ".one (sv .feMerge segs![.one (sv .feMergeNode segs![]), .one (sv .feMergeNode segs![])])])]), " ++
  ".one (sv .g segs![.one (sv .rect segs![.one (sv .title segs![.one (txt \"Box\")])]), .one (sv .circle segs![]), " ++
  ".one (sv .path segs![]), .one (sv .text segs![.one (txt \"t\"), .one (sv .tspan segs![.one (txt \"x\")])]), " ++
  ".one (sa .aContainer segs![.one (sv .rect segs![])])])])]"

def svgDocument (sections : Nat) : String :=
  "import HtmlModelTests.Helpers\n\nopen HtmlModel Web HtmlModelTests\n\n" ++
    s!"def doc : N (.html .flow) := el .div .flow segs![nodes [\n  " ++
    ",\n  ".intercalate ((List.range sections).map svgSection) ++ "]]\n"

def run (name : String) (source : String) : IO Bool := do
  let dir : System.FilePath := ".lake" / "bench"
  IO.FS.createDirAll dir
  let path := dir / s!"{name}.lean"
  IO.FS.writeFile path source
  let start ← IO.monoMsNow
  let out ← IO.Process.output { cmd := "lake", args := #["env", "lean", path.toString] }
  let ms := (← IO.monoMsNow) - start
  if out.exitCode != 0 then
    IO.eprintln s!"{name}: failed to elaborate\n{out.stdout}{out.stderr}"
    return false
  IO.println s!"{name}: {ms} ms"
  if ms > budgetMs then
    IO.eprintln s!"{name}: over the budget of {budgetMs} ms"
    return false
  return true

def main : IO UInt32 := do
  let defaults ← run "Defaults" (document 25 false)
  let svg ← run "Svg" (svgDocument 23)
  let cached ← run "Cached" (document 100 true)
  return if defaults && svg && cached then 0 else 1
