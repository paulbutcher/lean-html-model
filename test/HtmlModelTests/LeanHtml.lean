/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel

/-! lean-html's tag functions rebuilt on this library, with their present argument shapes, each list
argument a run-time `List` whose items may be of any categories widening to the list's own. -/

@[expose] public section

namespace HtmlModelTests.LeanHtml

open HtmlModel Web

abbrev Attrs := List (String × String)
abbrev Node (c : Html.Cat) := Web.Node Attrs (.html c)

instance {c : Html.Cat} [h : Widens .text (.html c)] (s : String) : CoeT String s (Node c) :=
  ⟨Web.widen (.text s) h.widens⟩

structure Whitespace where
  val : String
  isWhitespace : HtmlModel.isWhitespace val = true := by decide

def Whitespace.newline : Whitespace := { val := "\n" }

instance {c : Html.Cat} [h : Widens .ws (.html c)] (w : Whitespace) : CoeT Whitespace w (Node c) :=
  ⟨Web.widen (Web.ws w.val w.isWhitespace) h.widens⟩

def Segs.append {α : Type} {ks ls : List (SegK Cat)} :
    Segs vocab.sig α ks → Segs vocab.sig α ls → Segs vocab.sig α (ks ++ ls)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (Segs.append xs ys)

/-- An element of category `c` whose children are one run-time list of category `d`. -/
abbrev listElement (e : Html.Elem) (c d : Html.Cat) (children : List (Node d)) (attrs : Attrs)
    (hc : Cat.html c ∈ vocab.cats (.html e) := by decide +kernel)
    (ok : vocab.Admits (.html e) (.html c) [.many (.html d)] := by admits) : Node c :=
  Web.elem (.html e) (.html c) attrs segs![.many (Nodes.ofList children)] hc ok

def div (children : List (Node .flow)) (attrs : Attrs := []) : Node .flow :=
  listElement .div .flow .flow children attrs

def body (children : List (Node .flow)) (attrs : Attrs := []) : Node .body :=
  listElement .body .body .flow children attrs

def p (children : List (Node .phrasing)) (attrs : Attrs := []) : Node .paragraph :=
  listElement .p .paragraph .phrasing children attrs

def h1 (children : List (Node .phrasing)) (attrs : Attrs := []) : Node .heading :=
  listElement .h1 .heading .phrasing children attrs

def span (children : List (Node .phrasing)) (attrs : Attrs := []) : Node .phrasing :=
  listElement .span .phrasing .phrasing children attrs

def strong (children : List (Node .phrasing)) (attrs : Attrs := []) : Node .phrasing :=
  listElement .strong .phrasing .phrasing children attrs

def ul (children : List (Node .listItemOrScript)) (attrs : Attrs := []) : Node .flow :=
  listElement .ul .flow .listItemOrScript children attrs

def li (children : List (Node .flow)) (attrs : Attrs := []) : Node .listItem :=
  listElement .li .listItem .flow children attrs

def dt (children : List (Node .flow)) (attrs : Attrs := []) : Node .term :=
  listElement .dt .term .flow children attrs

def dd (children : List (Node .flow)) (attrs : Attrs := []) : Node .description :=
  listElement .dd .description .flow children attrs

def tr (children : List (Node .tableCellOrScript)) (attrs : Attrs := []) : Node .tableRow :=
  listElement .tr .tableRow .tableCellOrScript children attrs

def td (children : List (Node .flow)) (attrs : Attrs := []) : Node .tableCell :=
  listElement .td .tableCell .flow children attrs

def th (children : List (Node .flow)) (attrs : Attrs := []) : Node .tableCell :=
  listElement .th .tableCell .flow children attrs

def thead (children : List (Node .tableRowOrScript)) (attrs : Attrs := []) : Node .tableHead :=
  listElement .thead .tableHead .tableRowOrScript children attrs

def tbody (children : List (Node .tableRowOrScript)) (attrs : Attrs := []) : Node .tableBody :=
  listElement .tbody .tableBody .tableRowOrScript children attrs

def tfoot (children : List (Node .tableRowOrScript)) (attrs : Attrs := []) : Node .tableFoot :=
  listElement .tfoot .tableFoot .tableRowOrScript children attrs

def rt (children : List (Node .phrasing)) (attrs : Attrs := []) : Node .rubyText :=
  listElement .rt .rubyText .phrasing children attrs

def rp (children : List (Node .phrasing)) (attrs : Attrs := []) : Node .rubyParenthesis :=
  listElement .rp .rubyParenthesis .phrasing children attrs

def template (children : List (Node .flow)) (attrs : Attrs := []) : Node .template :=
  listElement .template .template .flow children attrs

def script (attrs : Attrs := []) : Node .scriptSupporting :=
  Web.elem (.html .script) (.html .scriptSupporting) attrs segs![]

def title (content : String) (attrs : Attrs := []) : Node .title :=
  Web.elem (.html .title) (.html .title) attrs segs![.one (.text content)]

def meta_ (rawAttrs : Attrs) : Node .phrasingMetadata :=
  Web.elem (.html .meta) (.html .phrasingMetadata) rawAttrs segs![]

def base (attrs : Attrs := []) : Node .base := Web.elem (.html .base) (.html .base) attrs segs![]

/-- Categories a transparent element may take, with its proofs for each. -/
class Transparent (c : Html.Cat) : Prop where
  takes : Cat.html c ∈ vocab.cats (.html .a)
  admits : vocab.Admits (.html .a) (.html c) [.many (.html c)]

instance : Transparent .flow := ⟨by decide, by decide +kernel⟩
instance : Transparent .phrasing := ⟨by decide, by decide +kernel⟩

structure AAttrs where
  href : Option String := none

def a {cat : Html.Cat} [h : Transparent cat] (attrs : AAttrs) (children : List (Node cat)) :
    Node cat :=
  listElement .a cat cat children (attrs.href.toList.map ("href", ·)) h.takes h.admits

/-- Exactly one `<title>` and at most one `<base>`. -/
def head (title : Node .title) (children : List (Node .metadata) := []) (attrs : Attrs := [])
    (base : Option (Node .base) := none) : Node .head :=
  Web.elem (.html .head) (.html .head) attrs
    segs![Seg.ofOption _ base, .many (Nodes.ofList children), .one title]

/-- One or more `<dt>` followed by one or more `<dd>`. -/
structure DlGroup where
  term : Node .term
  moreTerms : List (Node .termOrScript) := []
  desc : Node .description
  moreDescs : List (Node .descriptionOrScript) := []

abbrev dlGroupK : List (SegK Cat) :=
  [.one (.html .term), .many (.html .termOrScript), .one (.html .description),
    .many (.html .descriptionOrScript)]

def DlGroup.segs (g : DlGroup) : Segs vocab.sig Attrs dlGroupK :=
  segs![.one g.term, .many (Nodes.ofList g.moreTerms), .one g.desc, .many (Nodes.ofList g.moreDescs)]

inductive DlContent where
  | groups (groups : List DlGroup)
  | divs (divs : List (Node .descriptionGroupOrScript))

instance : Coe (List DlGroup) DlContent := ⟨.groups⟩
instance : Coe (List (Node .descriptionGroupOrScript)) DlContent := ⟨.divs⟩

def dl (content : DlContent := .groups []) (attrs : Attrs := []) : Node .flow :=
  let children : Seg vocab.sig Attrs (.alt [.groups dlGroupK] [.many (.html .descriptionGroupOrScript)]) :=
    match content with
    | .groups gs => .inl segs![.groups (Groups.ofList (gs.map DlGroup.segs))]
    | .divs ds => .inr segs![.many (Nodes.ofList ds)]
  Web.elem (.html .dl) (.html .flow) attrs segs![children]

/-- A `<div>` wrapping one group of a `<dl>`. -/
def dlDiv (group : DlGroup) (attrs : Attrs := []) : Node .descriptionGroup :=
  Web.elem (.html .div) (.html .descriptionGroup) attrs group.segs

/-- A table's body: any number of `<tbody>`, or else bare `<tr>` rows. -/
inductive TableBody where
  | sections (sections : List (Node .tableBodyOrScript))
  | rows (rows : List (Node .tableRowOrScript))

instance : Coe (List (Node .tableRowOrScript)) TableBody := ⟨.rows⟩
instance : Coe (List (Node .tableRow)) TableBody := ⟨fun rs => .rows (rs.map fun (r : Node .tableRow) => (r : Node .tableRowOrScript))⟩

def table (body : TableBody := .sections []) (attrs : Attrs := [])
    (caption : Option (Node .tableCaption) := none)
    (colgroups : List (Node .tableColumnGroupOrScript) := []) (thead : Option (Node .tableHead) := none)
    (tfoot : Option (Node .tableFoot) := none) : Node .flow :=
  let body : Seg vocab.sig Attrs (.alt [.many (.html .tableBodyOrScript)] [.many (.html .tableRowOrScript)]) :=
    match body with
    | .sections ss => .inl segs![.many (Nodes.ofList ss)]
    | .rows rs => .inr segs![.many (Nodes.ofList rs)]
  Web.elem (.html .table) (.html .flow) attrs
    segs![Seg.ofOption _ caption, .many (Nodes.ofList colgroups), Seg.ofOption _ thead, body,
      Seg.ofOption _ tfoot]

/-- A ruby annotation: one or more `<rt>`, or else an `<rp>` followed by one or more `<rt>`, each
followed by an `<rp>`. -/
inductive RubyText where
  | rt (first : Node .rubyText) (rest : List (Node .rubyText) := [])
  | parenthesized (opening : Node .rubyParenthesis) (first : Node .rubyText × Node .rubyParenthesis)
      (rest : List (Node .rubyText × Node .rubyParenthesis) := [])

instance : Coe (Node .rubyText) RubyText := ⟨(.rt · [])⟩

structure RubySegment where
  base : List (Node .phrasing)
  text : RubyText

abbrev rubySegmentK : List (SegK Cat) :=
  [.many (.html .phrasing),
    .alt [.one (.html .rubyText), .many (.html .rubyText)]
      [.one (.html .rubyParenthesis), .one (.html .rubyText), .one (.html .rubyParenthesis),
        .groups [.one (.html .rubyText), .one (.html .rubyParenthesis)]]]

def RubySegment.segs (s : RubySegment) : Segs vocab.sig Attrs rubySegmentK :=
  segs![.many (Nodes.ofList s.base), match s.text with
    | .rt first rest => .inl segs![.one first, .many (Nodes.ofList rest)]
    | .parenthesized opening (t, p) rest =>
      .inr segs![.one opening, .one t, .one p,
        .groups (Groups.ofList (rest.map fun (t, p) => segs![.one t, .one p]))]]

def ruby (segment : RubySegment) (more : List RubySegment := []) (attrs : Attrs := []) :
    Node .phrasing :=
  Web.elem (.html .ruby) (.html .phrasing) attrs
    (Segs.append segment.segs segs![.groups (Groups.ofList (more.map RubySegment.segs))])

/-- Renders compactly, unescaped, for no more than making `document` a string as lean-html's is. -/
partial def render : Web.Tree Attrs → String
  | .text s | .verbatim _ s => s
  | .elem e _ attrs ch => tag (vocab.sig.name e) attrs ch
  | .unchecked _ name _ attrs ch => tag name attrs ch
where
  tag (name : String) (attrs : Attrs) (ch : List (Web.Tree Attrs)) : String :=
    s!"<{name}{String.join (attrs.map fun (n, v) => s!" {n}=\"{v}\"")}>" ++
      String.join (ch.map render) ++ s!"</{name}>"

def document (head : Node .head) (body : Node .body) (lang : Option String := none)
    (pretty : Bool := false) : String :=
  let _ := pretty
  "<!DOCTYPE html>" ++ render (Web.elem (.html .html) (.html .document)
    (lang.toList.map ("lang", ·)) segs![.one head, .one body]).erase

-- lean-html's README example.
def page : String :=
  document
    (head (title "My page") [ meta_ [("charset", "utf-8")] ])
    (body [
      h1 [ "Welcome" ],
      p [ "Hello, ", strong [ "world" ], "!" ],
      ul [
        li [ a { href := "/a" } [ "Link A" ] ],
        li [ a { href := "/b" } [ "Link B" ] ],
      ],
      table [ tr [ td [ "1" ], td [ "2" ] ] ] (thead := thead [ tr [ th [ "A" ], th [ "B" ] ] ]),
    ])
    (lang := "en") (pretty := true)

-- `script`, `template` and whitespace among a list's items.
def list (items : List String) : Node .flow :=
  let items : List (Node .listItemOrScript) := items.map fun (i : String) => li [ i ]
  ul (Whitespace.newline :: script :: template [ p [ "x" ] ] :: items)

-- A phrasing element and a text literal in a flow list.
def mixed : Node .flow := div [ p [ "a" ], span [ "b" ], "c", div [], Whitespace.newline ]

def glossary (entries : List (String × String)) : Node .flow :=
  dl (entries.map fun ((k, v) : String × String) =>
    ({ term := dt [ k ], moreTerms := [ script ], desc := dd [ v ] } : DlGroup))

def glossaryDivs (entries : List (String × String)) : Node .flow :=
  let divs : List (Node .descriptionGroupOrScript) :=
    entries.map fun ((k, v) : String × String) => dlDiv { term := dt [ k ], desc := dd [ v ] }
  dl (.divs (script :: divs))

def rows (cells : List (List String)) : Node .flow :=
  let rows : List (Node .tableRowOrScript) :=
    cells.map fun (r : List String) => tr (r.map fun (c : String) => td [ c ])
  table (.rows (script :: rows))

def sections (n : Nat) : Node .flow :=
  let bodies : List (Node .tableBodyOrScript) := (List.range n).map fun _ => tbody []
  table (.sections (script :: bodies)) (thead := thead []) (tfoot := tfoot [])

def kanji : Node .phrasing :=
  ruby { base := [ "漢" ], text := rt [ "kan" ] }
    [ { base := [ "字" ], text := .parenthesized (rp [ "(" ]) (rt [ "ji" ], rp [ ")" ]) } ]

def page' (metas : List (Node .metadata)) : Node .head :=
  head (title "T") (meta_ [("charset", "utf-8")] :: script :: metas) (base := base)

end HtmlModelTests.LeanHtml
