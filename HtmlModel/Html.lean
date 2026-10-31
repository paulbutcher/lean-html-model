/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

@[expose] public section

namespace HtmlModel.Html

inductive Elem where
  | html | head | title | base | link | «meta» | style | body
  | article | «section» | nav | aside | h1 | h2 | h3 | h4 | h5 | h6 | hgroup | header | footer
  | address | p | hr | pre | blockquote | ol | ul | menu | li | dl | dt | dd | figure
  | figcaption | main | search | div
  | a | em | strong | small | s | cite | q | dfn | abbr | ruby | rt | rp | data | time | code
  | var | samp | kbd | sub | sup | i | b | u | mark | bdi | bdo | span | br | wbr
  | ins | del
  | picture | source | img | iframe | embed | object | video | audio | track | map | area
  | table | caption | colgroup | col | tbody | thead | tfoot | tr | td | th
  | form | label | input | button | select | datalist | optgroup | option | textarea | output
  | progress | meter | fieldset | legend
  | details | summary | dialog
  | script | noscript | template | slot | canvas
  deriving DecidableEq, Repr

def Elem.name : Elem → String
  | .html => "html" | .head => "head" | .title => "title" | .base => "base" | .link => "link"
  | .meta => "meta" | .style => "style" | .body => "body" | .article => "article"
  | .section => "section" | .nav => "nav" | .aside => "aside" | .h1 => "h1" | .h2 => "h2"
  | .h3 => "h3" | .h4 => "h4" | .h5 => "h5" | .h6 => "h6" | .hgroup => "hgroup"
  | .header => "header" | .footer => "footer" | .address => "address" | .p => "p" | .hr => "hr"
  | .pre => "pre" | .blockquote => "blockquote" | .ol => "ol" | .ul => "ul" | .menu => "menu"
  | .li => "li" | .dl => "dl" | .dt => "dt" | .dd => "dd" | .figure => "figure"
  | .figcaption => "figcaption" | .main => "main" | .search => "search" | .div => "div"
  | .a => "a" | .em => "em" | .strong => "strong" | .small => "small" | .s => "s"
  | .cite => "cite" | .q => "q" | .dfn => "dfn" | .abbr => "abbr" | .ruby => "ruby"
  | .rt => "rt" | .rp => "rp" | .data => "data" | .time => "time" | .code => "code"
  | .var => "var" | .samp => "samp" | .kbd => "kbd" | .sub => "sub" | .sup => "sup"
  | .i => "i" | .b => "b" | .u => "u" | .mark => "mark" | .bdi => "bdi" | .bdo => "bdo"
  | .span => "span" | .br => "br" | .wbr => "wbr" | .ins => "ins" | .del => "del"
  | .picture => "picture" | .source => "source" | .img => "img" | .iframe => "iframe"
  | .embed => "embed" | .object => "object" | .video => "video" | .audio => "audio"
  | .track => "track" | .map => "map" | .area => "area" | .table => "table"
  | .caption => "caption" | .colgroup => "colgroup" | .col => "col" | .tbody => "tbody"
  | .thead => "thead" | .tfoot => "tfoot" | .tr => "tr" | .td => "td" | .th => "th"
  | .form => "form" | .label => "label" | .input => "input" | .button => "button"
  | .select => "select" | .datalist => "datalist" | .optgroup => "optgroup"
  | .option => "option" | .textarea => "textarea" | .output => "output"
  | .progress => "progress" | .meter => "meter" | .fieldset => "fieldset"
  | .legend => "legend" | .details => "details" | .summary => "summary" | .dialog => "dialog"
  | .script => "script" | .noscript => "noscript" | .template => "template" | .slot => "slot"
  | .canvas => "canvas"

/-- Every element, in the order declared. -/
def Elem.all : List Elem :=
  [.html, .head, .title, .base, .link, .meta, .style, .body, .article, .section, .nav, .aside,
    .h1, .h2, .h3, .h4, .h5, .h6, .hgroup, .header, .footer, .address, .p, .hr, .pre,
    .blockquote, .ol, .ul, .menu, .li, .dl, .dt, .dd, .figure, .figcaption, .main, .search, .div,
    .a, .em, .strong, .small, .s, .cite, .q, .dfn, .abbr, .ruby, .rt, .rp, .data, .time, .code,
    .var, .samp, .kbd, .sub, .sup, .i, .b, .u, .mark, .bdi, .bdo, .span, .br, .wbr, .ins, .del,
    .picture, .source, .img, .iframe, .embed, .object, .video, .audio, .track, .map, .area,
    .table, .caption, .colgroup, .col, .tbody, .thead, .tfoot, .tr, .td, .th, .form, .label,
    .input, .button, .select, .datalist, .optgroup, .option, .textarea, .output, .progress,
    .meter, .fieldset, .legend, .details, .summary, .dialog, .script, .noscript, .template,
    .slot, .canvas]

/-- The element a tag name names, as a parser or macro reads it. -/
def Elem.ofName? (name : String) : Option Elem := Elem.all.find? (·.name == name)

/-- Besides flow and phrasing content, there is a category for each element whose parent fixes
where it may appear, and for each narrowing of flow or phrasing content that some parent demands
exactly (`heading`, `paragraph`, `image`). -/
inductive Cat where
  | flow | phrasing | phrasingOrHeading | heading | headingGroup | paragraph | image
  | metadata | noscriptMetadata | title | base | document | head | body
  | listItem | term | description | descriptionGroup | figureCaption | summary | legend
  | source | pictureSource | track | rubyText | rubyParenthesis | option | selectChild
  | tableCaption | tableColumnGroup | tableColumn | tableHead | tableBody | tableFoot | tableRow
  | tableCell
  /-- `script`, and with `template`, whatever a script-supporting element may stand among. -/
  | scriptSupporting
  /-- `template`, which `colgroup` admits and `script` it does not. -/
  | template
  deriving DecidableEq, Repr

/-- Every category `c` is valid wherever, transitively. -/
def Cat.above : Cat → List Cat
  | .phrasing => [.flow, .phrasingOrHeading]
  | .heading | .headingGroup => [.flow, .phrasingOrHeading]
  | .paragraph => [.flow]
  | .image => [.phrasing, .flow, .phrasingOrHeading]
  | .option => [.selectChild]
  | .scriptSupporting => [.metadata, .phrasing, .flow, .phrasingOrHeading]
  | .template => [.scriptSupporting, .metadata, .phrasing, .flow, .phrasingOrHeading]
  | _ => []

/-- The categories an element may take. One taking several takes its content model from the
context it is placed in, as a transparent element does. -/
def Elem.cats : Elem → List Cat
  | .html => [.document]
  | .head => [.head]
  | .body => [.body]
  | .title => [.title]
  | .base => [.base]
  | .link | .meta => [.metadata, .noscriptMetadata, .phrasing]
  | .style => [.metadata, .noscriptMetadata]
  | .script => [.scriptSupporting]
  | .template => [.template]
  | .noscript => [.metadata, .phrasing, .flow]
  | .div => [.flow, .descriptionGroup]
  | .h1 | .h2 | .h3 | .h4 | .h5 | .h6 => [.heading]
  | .hgroup => [.headingGroup]
  | .p => [.paragraph]
  | .li => [.listItem]
  | .dt => [.term]
  | .dd => [.description]
  | .figcaption => [.figureCaption]
  | .rt => [.rubyText]
  | .rp => [.rubyParenthesis]
  | .a | .ins | .del | .object | .video | .audio | .map | .slot | .canvas => [.phrasing, .flow]
  | .source => [.source, .pictureSource]
  | .track => [.track]
  | .img => [.image]
  | .caption => [.tableCaption]
  | .colgroup => [.tableColumnGroup]
  | .col => [.tableColumn]
  | .thead => [.tableHead]
  | .tbody => [.tableBody]
  | .tfoot => [.tableFoot]
  | .tr => [.tableRow]
  | .td | .th => [.tableCell]
  | .optgroup => [.selectChild]
  | .option => [.option]
  | .legend => [.legend]
  | .summary => [.summary]
  | .em | .strong | .small | .s | .cite | .q | .dfn | .abbr | .ruby | .data | .time | .code
  | .var | .samp | .kbd | .sub | .sup | .i | .b | .u | .mark | .bdi | .bdo | .span | .br
  | .wbr | .picture | .iframe | .embed | .area | .label | .input | .button | .select
  | .datalist | .textarea | .output | .progress | .meter => [.phrasing]
  | .article | .section | .nav | .aside | .header | .footer | .address | .hr | .pre
  | .blockquote | .ol | .ul | .menu | .dl | .figure | .main | .search | .form | .fieldset
  | .details | .dialog | .table => [.flow]

/-- Whether content of this category lays out inline. `rt` and `rp` count, since whitespace between
them and the base text would render inside the ruby; so do script-supporting elements, which may
stand among phrasing content. -/
def Cat.isInline : Cat → Bool
  | .phrasing | .image | .rubyText | .rubyParenthesis | .scriptSupporting | .template => true
  | _ => false

/-- An element that takes the content model of its context, so that it lays out inline when all
it holds does. -/
def Elem.isTransparent : Elem → Bool
  | .a | .ins | .del | .object | .video | .audio | .map | .slot | .canvas | .noscript => true
  | _ => false

end HtmlModel.Html
