/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlModelTests.Helpers

namespace HtmlModelTests.ContentModel

open HtmlModel Web

-- lean-html's structured tag functions, as children in the order they emit them.
example : N (.html .flow) := el .table .flow segs![.one (el .tr .tableRow segs![.one (el .td .tableCell segs![])])]
example : N (.html .flow) :=
  el .details .flow segs![.one (el .summary .summary segs![.one (txt "More")]), .one (el .p .paragraph segs![.one (txt "Body")])]
example : N (.html .flow) :=
  el .fieldset .flow segs![.one (el .legend .legend segs![.one (txt "Name")]), .one (el .p .paragraph segs![])]
example : N (.html .flow) :=
  el .figure .flow segs![.one (el .figcaption .figureCaption segs![]), .one (el .p .paragraph segs![])]
example : N (.html .flow) :=
  el .figure .flow segs![.one (el .p .paragraph segs![]), .one (el .figcaption .figureCaption segs![])]
example : N (.html .flow) :=
  el .dl .flow segs![.one (el .dt .term segs![]), .one (el .dt .term segs![]), .one (el .dd .description segs![])]
example : N (.html .flow) :=
  el .dl .flow segs![.one (el .div .descriptionGroup segs![.one (el .dt .term segs![]), .one (el .dd .description segs![]),
    .one (el .dd .description segs![])])]
example : N (.html .phrasing) :=
  el .picture .phrasing segs![.one (el .source .pictureSource segs![]), .one (el .img .image segs![])]
example : N (.html .flow) :=
  el .video .flow segs![.one (el .source .source segs![]), .one (el .track .track segs![]), .one (txt "No video")]
example : N (.html .phrasing) := el .audio .phrasing segs![.one (el .track .track segs![])]
example : N (.html .phrasing) :=
  el .ruby .phrasing segs![.one (txt "漢"), .one (el .rp .rubyParenthesis segs![]), .one (el .rt .rubyText segs![]),
    .one (el .rp .rubyParenthesis segs![]), .one (txt "字"), .one (el .rt .rubyText segs![])]
example : N (.html .headingGroup) :=
  el .hgroup .headingGroup segs![.one (el .p .paragraph segs![]), .one (el .h1 .heading segs![]),
    .one (el .p .paragraph segs![])]

-- Heading content, `hgroup` included, may stand in `<summary>` and `<legend>`.
example : N (.html .summary) := el .summary .summary segs![.one (el .h2 .heading segs![]), .one (txt " more")]
example : N (.html .legend) :=
  el .legend .legend segs![.one (el .hgroup .headingGroup segs![.one (el .h1 .heading segs![])])]

-- Script-supporting elements intermix with structured children, and `<template>` with `<col>`s.
example : N (.html .flow) := el .ul .flow segs![.one (el .li .listItem segs![]), .one (el .script .scriptSupporting segs![])]
example : N (.html .flow) :=
  el .table .flow segs![.one (el .colgroup .tableColumnGroup segs![.one (el .col .tableColumn segs![]),
      .one (el .template .template segs![])]),
    .one (el .tr .tableRow segs![.one (el .td .tableCell segs![]), .one (el .script .scriptSupporting segs![])]),
    .one (el .template .template segs![])]
example : N (.html .phrasing) :=
  el .select .phrasing segs![.one (el .option .option segs![.one (txt "a")]), .one (el .script .scriptSupporting segs![])]
example : N (.html .phrasing) :=
  el .picture .phrasing segs![.one (el .script .scriptSupporting segs![]), .one (el .img .image segs![])]
example : N (.html .flow) :=
  el .dl .flow segs![.one (el .div .descriptionGroup segs![.one (el .dt .term segs![]), .one (el .dd .description segs![])]),
    .one (el .script .scriptSupporting segs![])]

-- In `<head>`, a `<noscript>` holds `link` and `meta`; in `<body>`, flow content.
example : N (.html .document) :=
  el .html .document segs![
    .one (el .head .head segs![.one (el .noscript .metadata segs![.one (el .link .noscriptMetadata segs![])]),
      .one (el .title .title segs![.one (txt "T")])]),
    .one (el .body .body segs![.one (el .noscript .flow segs![.one (txt "Enable scripts")])])]

-- Children known only at run time, as lists and as groups.
example (entries : List (String × String)) : N (.html .flow) :=
  el .dl .flow segs![.groups (Groups.ofList (entries.map fun (k, v) =>
    segs![.one (el .dt .term segs![.one (txt k)]), .one (el .dd .description segs![.one (txt v)])]))]
example (rows : List (List String)) : N (.html .flow) :=
  el .table .flow segs![nodes (rows.map fun r => el .tr .tableRow segs![nodes (r.map fun c => el .td .tableCell segs![.one (txt c)])])]
example (items : List (N (.html .listItem))) (caption : Option (N (.html .tableCaption))) :
    N (.html .flow) :=
  el .div .flow segs![.one (el .ul .flow segs![nodes items]),
    .one (el .table .flow segs![Seg.ofOption (Cat.html .tableCaption) caption])]

-- Repetition nested within repetition, as lean-html's `DlGroup` and `RubySegment` build it.
def dt (s : String) : N (.html .term) := el .dt .term segs![.one (txt s)]
def dd (s : String) : N (.html .description) := el .dd .description segs![.one (txt s)]
def rt (s : String) : N (.html .rubyText) := el .rt .rubyText segs![.one (txt s)]
def rp (s : String) : N (.html .rubyParenthesis) := el .rp .rubyParenthesis segs![.one (txt s)]

/-- One or more terms, then one or more descriptions. -/
abbrev dlGroup : List (SegK Cat) := [.many1 (.html .term), .many1 (.html .description)]

example (groups : List ((String × List String) × (String × List String))) : N (.html .flow) :=
  el .dl .flow segs![.groups (Groups.ofList (groups.map fun ((t, ts), (d, ds)) =>
    (segs![.many1 (dt t) (Nodes.ofList (ts.map dt)), .many1 (dd d) (Nodes.ofList (ds.map dd))] :
      Segs vocab Unit dlGroup)))]

/-- One or more `rt`, or an opening `rp` and then one or more pairs of `rt` and a closing `rp`. -/
abbrev rubyText : SegK Cat :=
  .alt [.many1 (.html .rubyText)]
    [.one (.html .rubyParenthesis), .one (.html .rubyText), .one (.html .rubyParenthesis),
      .groups [.one (.html .rubyText), .one (.html .rubyParenthesis)]]

def annotation : (String × List String) ⊕ (String × List String) → Seg vocab Unit rubyText
  | .inl (t, ts) => .inl segs![.many1 (rt t) (Nodes.ofList (ts.map rt))]
  | .inr (t, ts) => .inr segs![.one (rp "("), .one (rt t), .one (rp ")"),
      .groups (Groups.ofList (ts.map fun t => segs![.one (rt t), .one (rp ")")]))]

def base (s : List String) : Seg vocab Unit (.many .text) := .many (Nodes.ofList (s.map txt))

example (first : List String × ((String × List String) ⊕ (String × List String)))
    (more : List (List String × ((String × List String) ⊕ (String × List String)))) :
    N (.html .phrasing) :=
  el .ruby .phrasing segs![base first.1, annotation first.2,
    .groups (Groups.ofList (more.map fun (b, a) => segs![base b, annotation a]))]

-- Inter-element whitespace may stand among children that are not phrasing content.
example : N (.html .flow) :=
  el .ul .flow segs![.one (el .li .listItem segs![]), .ws "\n", .one (el .li .listItem segs![])]
example : N (.html .tableRow) :=
  el .tr .tableRow segs![.one (el .td .tableCell segs![]), .ws " \n", .one (el .td .tableCell segs![])]

-- Valid markup lean-html rejects, having no list to hold it.
example : N (.html .flow) :=
  el .table .flow segs![.one (el .caption .tableCaption segs![]), .one (el .script .scriptSupporting segs![]),
    .one (el .thead .tableHead segs![]), .one (el .template .template segs![]), .one (el .tbody .tableBody segs![]),
    .one (el .script .scriptSupporting segs![]), .one (el .tfoot .tableFoot segs![])]
example : N (.html .flow) :=
  el .dl .flow segs![.one (el .dt .term segs![]), .one (el .script .scriptSupporting segs![]),
    .one (el .dd .description segs![])]
example : N (.html .head) := el .head .head segs![.ws "\n  ", .one (el .title .title segs![])]

-- lean-html's rejections. Where lean-html rejects valid markup because the argument the child is
-- passed in is typed, such as a `<legend>` among a `<fieldset>`'s children, the case here puts
-- the child where the content model really forbids it.

-- thead after tbody
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <table> as Cat.html Html.Cat.flow does not admit its children: segment 2, of category Cat.html Html.Cat.tableHead, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .table .flow segs![.one (el .tbody .tableBody segs![]), .one (el .thead .tableHead segs![])]

-- caption after body
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <table> as Cat.html Html.Cat.flow does not admit its children: segment 2, of category Cat.html Html.Cat.tableCaption, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .table .flow segs![.one (el .tbody .tableBody segs![]), .one (el .caption .tableCaption segs![])]

-- dt in div
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <div> as Cat.html Html.Cat.flow does not admit its children: segment 1, of category Cat.html Html.Cat.term, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .div .flow segs![.one (el .dt .term segs![])]

-- source in div
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <div> as Cat.html Html.Cat.flow does not admit its children: segment 1, of category Cat.html Html.Cat.source, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .div .flow segs![.one (el .source .source segs![])]

-- rt in span
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <span> as Cat.html Html.Cat.phrasing does not admit its children: segment 1, of category Cat.html Html.Cat.rubyText, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .phrasing) := el .span .phrasing segs![.one (el .rt .rubyText segs![])]

-- body before head
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <html> as Cat.html Html.Cat.document does not admit its children: segment 1, of category Cat.html Html.Cat.body, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .document) := el .html .document segs![.one (el .body .body segs![]), .one (el .head .head segs![.one (el .title .title segs![])])]

-- details without summary
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <details> as Cat.html Html.Cat.flow does not admit its children: segment 1, of category Cat.html Html.Cat.paragraph, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .details .flow segs![.one (el .p .paragraph segs![])]

-- two summaries
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <details> as Cat.html Html.Cat.flow does not admit its children: segment 2, of category Cat.html Html.Cat.summary, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .details .flow segs![.one (el .summary .summary segs![]), .one (el .summary .summary segs![])]

-- legend after content
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <fieldset> as Cat.html Html.Cat.flow does not admit its children: segment 2, of category Cat.html Html.Cat.legend, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .fieldset .flow segs![.one (el .p .paragraph segs![]), .one (el .legend .legend segs![])]

-- figcaption in the middle
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <figure> as Cat.html Html.Cat.flow does not admit its children: segment 3, of category Cat.html Html.Cat.paragraph, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .figure .flow segs![.one (el .p .paragraph segs![]), .one (el .figcaption .figureCaption segs![]), .one (el .p .paragraph segs![])]

-- dd before dt
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <dl> as Cat.html Html.Cat.flow does not admit its children: segment 1, of category Cat.html Html.Cat.description, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .dl .flow segs![.one (el .dd .description segs![]), .one (el .dt .term segs![])]

-- dt in a dl of divs
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <dl> as Cat.html Html.Cat.flow does not admit its children: segment 2, of category Cat.html Html.Cat.term, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .dl .flow segs![.one (el .div .descriptionGroup segs![.one (el .dt .term segs![]), .one (el .dd .description segs![])]), .one (el .dt .term segs![])]

-- img before source
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <picture> as Cat.html Html.Cat.phrasing does not admit its children: segment 2, of category Cat.html Html.Cat.pictureSource, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .phrasing) := el .picture .phrasing segs![.one (el .img .image segs![]), .one (el .source .pictureSource segs![])]

-- picture without img
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <picture> as Cat.html Html.Cat.phrasing does not admit its children: segment 1, of category Cat.html Html.Cat.phrasing, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .phrasing) := el .picture .phrasing segs![.one (el .span .phrasing segs![])]

-- source after track
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <video> as Cat.html Html.Cat.flow does not admit its children: segment 2, of category Cat.html Html.Cat.source, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .video .flow segs![.one (el .track .track segs![]), .one (el .source .source segs![])]

-- rt in base text
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <ruby> as Cat.html Html.Cat.phrasing does not admit its children: they end before it is complete
-/
#guard_msgs in
example : N (.html .phrasing) := el .ruby .phrasing segs![.one (txt "x"), .one (el .rt .rubyText segs![]), .one (txt "y")]

-- rp not bracketing
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <ruby> as Cat.html Html.Cat.phrasing does not admit its children: they end before it is complete
-/
#guard_msgs in
example : N (.html .phrasing) := el .ruby .phrasing segs![.one (txt "x"), .one (el .rt .rubyText segs![]), .one (el .rt .rubyText segs![]), .one (el .rp .rubyParenthesis segs![])]

-- two headings in hgroup
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <hgroup> as Cat.html Html.Cat.headingGroup does not admit its children: segment 2, of category Cat.html Html.Cat.heading, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .headingGroup) := el .hgroup .headingGroup segs![.one (el .h1 .heading segs![]), .one (el .h2 .heading segs![])]

-- no heading in hgroup
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <hgroup> as Cat.html Html.Cat.headingGroup does not admit its children: they end before it is complete
-/
#guard_msgs in
example : N (.html .headingGroup) := el .hgroup .headingGroup segs![.one (el .p .paragraph segs![])]

-- text in ul
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <ul> as Cat.html Html.Cat.flow does not admit its children: segment 1, of category Cat.text, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .ul .flow segs![.one (txt "hello")]

-- text in tr
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <tr> as Cat.html Html.Cat.tableRow does not admit its children: segment 1, of category Cat.text, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .tableRow) := el .tr .tableRow segs![.one (txt "hello")]

-- not whitespace
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  isWhitespace "x" = true
is false
-/
#guard_msgs in
example : Seg vocab Unit .ws := .ws "x"

-- whitespace for summary
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <details> as Cat.html Html.Cat.flow does not admit its children: they end before it is complete
-/
#guard_msgs in
example : N (.html .flow) := el .details .flow segs![.ws "\n"]

-- p in summary
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <summary> as Cat.html Html.Cat.summary does not admit its children: segment 1, of category Cat.html Html.Cat.paragraph, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .summary) := el .summary .summary segs![.one (el .p .paragraph segs![])]

-- hgroup in hgroup
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <hgroup> as Cat.html Html.Cat.headingGroup does not admit its children: segment 1, of category Cat.html Html.Cat.headingGroup, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .headingGroup) := el .hgroup .headingGroup segs![.one (el .hgroup .headingGroup segs![.one (el .h1 .heading segs![])])]

-- script in colgroup
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <colgroup> as Cat.html Html.Cat.tableColumnGroup does not admit its children: segment 2, of category Cat.html Html.Cat.scriptSupporting, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .tableColumnGroup) := el .colgroup .tableColumnGroup segs![.one (el .col .tableColumn segs![]), .one (el .script .scriptSupporting segs![])]

-- script among sources
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <video> as Cat.html Html.Cat.flow does not admit its children: segment 3, of category Cat.html Html.Cat.source, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .video .flow segs![.one (el .source .source segs![]), .one (el .script .scriptSupporting segs![]), .one (el .source .source segs![])]

-- script for a dt
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <dl> as Cat.html Html.Cat.flow does not admit its children: segment 2, of category Cat.html Html.Cat.description, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .flow) := el .dl .flow segs![.one (el .script .scriptSupporting segs![]), .one (el .dd .description segs![])]

-- script in noscript in head
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <noscript> as Cat.html Html.Cat.metadata does not admit its children: segment 1, of category Cat.html Html.Cat.scriptSupporting, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .metadata) := el .noscript .metadata segs![.one (el .script .scriptSupporting segs![])]

-- text in noscript in head
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <noscript> as Cat.html Html.Cat.metadata does not admit its children: segment 1, of category Cat.text, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .metadata) := el .noscript .metadata segs![.one (txt "x")]

-- div in p
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <p> as Cat.html Html.Cat.paragraph does not admit its children: segment 1, of category Cat.html Html.Cat.flow, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .paragraph) := el .p .paragraph segs![.one (el .div .flow segs![])]

-- children in a void element
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <br> as Cat.html Html.Cat.phrasing does not admit its children: segment 1, of category Cat.text, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .phrasing) := el .br .phrasing segs![.one (txt "x")]

-- head without title
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <head> as Cat.html Html.Cat.head does not admit its children: they end before it is complete
-/
#guard_msgs in
example : N (.html .head) := el .head .head segs![.one (el .meta .metadata segs![])]

-- two titles
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <head> as Cat.html Html.Cat.head does not admit its children: segment 2, of category Cat.html Html.Cat.title, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .head) := el .head .head segs![.one (el .title .title segs![]), .one (el .title .title segs![])]

-- element in title
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <title> as Cat.html Html.Cat.title does not admit its children: segment 1, of category Cat.html Html.Cat.phrasing, cannot follow the segments before it
-/
#guard_msgs in
example : N (.html .title) := el .title .title segs![.one (el .span .phrasing segs![])]

-- li as flow: wrong category
/--
error: could not synthesize default value for parameter 'hc' using tactics
---
error: Tactic `decide` proved that the proposition
  Cat.html Html.Cat.flow ∈ vocab.cats (Elem.html Html.Elem.li)
is false
-/
#guard_msgs in
example : N (.html .flow) := el .li .flow segs![]

-- descriptions in a group that may be empty
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <dl> as Cat.html Html.Cat.flow does not admit its children: they end before it is complete
-/
#guard_msgs in
example (groups : List (String × List String)) : N (.html .flow) :=
  el .dl .flow segs![.groups (Groups.ofList (groups.map fun (t, ds) =>
    segs![.one (dt t), .many (Nodes.ofList (ds.map dd))]))]

-- a ruby segment whose annotation may be empty
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: <ruby> as Cat.html Html.Cat.phrasing does not admit its children: they end before it is complete
-/
#guard_msgs in
example (segments : List (List String × List String)) : N (.html .phrasing) :=
  el .ruby .phrasing segs![.one (txt "x"), .one (rt "x"),
    .groups (Groups.ofList (segments.map fun (b, ts) => segs![base b, .many (Nodes.ofList (ts.map rt))]))]

end HtmlModelTests.ContentModel
