/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

@[expose] public section

namespace HtmlModel.Mathml

/-- The elements of MathML Core. -/
inductive Elem where
  | annotation | annotationXml | maction | math | merror | mfrac | mi | mmultiscripts | mn | mo
  | mover | mpadded | mphantom | mprescripts | mroot | mrow | ms | mspace | msqrt | mstyle | msub
  | msubsup | msup | mtable | mtd | mtext | mtr | munder | munderover | semantics
  deriving DecidableEq, Repr

def Elem.all : List Elem :=
  [.annotation, .annotationXml, .maction, .math, .merror, .mfrac, .mi, .mmultiscripts, .mn, .mo,
    .mover, .mpadded, .mphantom, .mprescripts, .mroot, .mrow, .ms, .mspace, .msqrt, .mstyle, .msub,
    .msubsup, .msup, .mtable, .mtd, .mtext, .mtr, .munder, .munderover, .semantics]

def Elem.name : Elem → String
  | .annotation => "annotation" | .annotationXml => "annotation-xml" | .maction => "maction"
  | .math => "math" | .merror => "merror" | .mfrac => "mfrac" | .mi => "mi"
  | .mmultiscripts => "mmultiscripts" | .mn => "mn" | .mo => "mo" | .mover => "mover"
  | .mpadded => "mpadded" | .mphantom => "mphantom" | .mprescripts => "mprescripts"
  | .mroot => "mroot" | .mrow => "mrow" | .ms => "ms" | .mspace => "mspace" | .msqrt => "msqrt"
  | .mstyle => "mstyle" | .msub => "msub" | .msubsup => "msubsup" | .msup => "msup"
  | .mtable => "mtable" | .mtd => "mtd" | .mtext => "mtext" | .mtr => "mtr" | .munder => "munder"
  | .munderover => "munderover" | .semantics => "semantics"

def Elem.ofName? (name : String) : Option Elem := Elem.all.find? (·.name == name)

inductive Cat where
  /-- A presentation expression, which every element but the parts of a table, scripts, and
  annotations is. -/
  | expr
  | prescripts
  | row
  | cell
  | annotation
  /-- `annotation-xml` holding HTML, as its `encoding` attribute says, which makes it an HTML
  integration point. -/
  | annotationXmlHtml
  /-- `annotation-xml` holding anything else, such as content MathML or SVG. -/
  | annotationXml
  /-- Any of the three annotations, which `semantics` holds after its expression. -/
  | annotations
  /-- An expression or an `svg`, which an `annotation-xml` that is not HTML holds. -/
  | annotationXmlContent
  deriving DecidableEq, Repr

def Cat.all : List Cat :=
  [.expr, .prescripts, .row, .cell, .annotation, .annotationXmlHtml, .annotationXml, .annotations,
    .annotationXmlContent]

theorem Cat.mem_all (c : Cat) : c ∈ Cat.all := by cases c <;> decide

def Cat.above : Cat → List Cat
  | .expr => [.annotationXmlContent]
  | .annotation | .annotationXmlHtml | .annotationXml => [.annotations]
  | _ => []

def Elem.cats : Elem → List Cat
  | .mprescripts => [.prescripts]
  | .mtr => [.row]
  | .mtd => [.cell]
  | .annotation => [.annotation]
  | .annotationXml => [.annotationXmlHtml, .annotationXml]
  | _ => [.expr]

/-- The token elements, within which whitespace renders as text. -/
def Elem.isToken : Elem → Bool
  | .mi | .mn | .mo | .ms | .mtext => true
  | _ => false

end HtmlModel.Mathml
