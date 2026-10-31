/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Engine.Vocabulary

@[expose] public section

namespace HtmlModel

open Regular

/-- Why an element does not admit its children. -/
inductive Rejection (C : Type) where
  /-- The child of category `c` from segment `seg`, numbered from 0, cannot follow those
  before it. -/
  | unexpected (seg : Nat) (c : C)
  /-- Every child can follow those before it, but more are needed. -/
  | incomplete
  deriving Repr

namespace Vocabulary

variable (V : Vocabulary)

/-- The segment holding the `pos`th letter, numbered from 0, given how many letters each holds. -/
def segmentOf : List Nat → Nat → Nat
  | [], _ => 0
  | n :: ns, pos => if pos < n then 0 else segmentOf ns (pos - n) + 1

/-- Why element `e` of category `c` rejects children of kinds `ks`, or `none` if it admits
them. Each letter of the shortest counterexample is tagged with the position of the symbol in
the shape that produced it, which locates its segment. -/
def rejection (e : V.Elem) (c : V.Cat) (ks : List (SegK V.Cat)) : Option (Rejection V.Cat) :=
  let spec := V.spec e c
  let shape := V.shape spec.ws ks
  match counterexample (fun (p : Nat × V.Cat) d => V.widens p.2 d) spec.grammar
      (Shape.indexed shape) with
  | none => none
  | some w =>
    match diagnose V.widens spec.grammar (w.map (·.2)) with
    | .unexpected i =>
      match w[i]? with
      | some (pos, l) =>
        some (.unexpected (segmentOf (ks.map fun k => (V.segShape spec.ws k).letters.length) pos) l)
      | none => some .incomplete
    | _ => some .incomplete

end Vocabulary

end HtmlModel
