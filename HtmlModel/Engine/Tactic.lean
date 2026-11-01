/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlModel.Engine.Explain
public meta import Lean.Elab.Tactic

public section

namespace HtmlModel

open Lean Meta Elab Tactic

/-- Reduces `e` to constructors and literals in the kernel, which evaluates lean-regular's
procedure far faster than the elaborator would. `fuel` bounds the depth of the value. -/
meta def kernelNormalize (fuel : Nat) (e : Expr) : MetaM Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let env ← getEnv
    let e ← ofExceptKernelException (Kernel.whnf env (← getLCtx) e)
    let .const name _ := e.getAppFn | return e
    let some (.ctorInfo ctor) := env.find? name | return e
    let args ← e.getAppArgs.mapIdxM fun i a =>
      if i < ctor.numParams then pure a else kernelNormalize fuel a
    return mkAppN e.getAppFn args

/-- Proves that an element admits its children by `decide +kernel`. When it does not, says which
segment is wrong and how, from the counterexample `Vocabulary.rejection` finds. -/
syntax (name := admits) "admits" : tactic

@[tactic admits] meta def evalAdmits : Tactic := fun _ => do
  let ty ← whnfR (← instantiateMVars (← getMainTarget))
  try evalTactic (← `(tactic| decide +kernel))
  catch ex =>
    let (``Vocabulary.Admits, #[V, e, c, ks]) := ty.getAppFnArgs | throw ex
    if ty.hasMVar then throw ex
    let name ← kernelNormalize 2 (mkApp2 (mkConst ``Vocabulary.name) V e)
    let tag := match name with
      | .lit (.strVal s) => m!"<{s}>"
      | _ => m!"{e}"
    let rejection ← kernelNormalize 64 (mkApp4 (mkConst ``Vocabulary.rejection) V e c ks)
    let pp (x : Expr) : MetaM String := return (← ppExpr x).pretty 1000
    match rejection.getAppFnArgs with
    | (``Option.some, #[_, r]) =>
      match r.getAppFnArgs with
      | (``Rejection.unexpected, #[_, .lit (.natVal seg), l]) =>
        throwError "{tag} as {← pp c} does not admit its children: segment {seg + 1}, of \
          category {← pp l}, cannot follow the segments before it"
      | (``Rejection.incomplete, _) =>
        throwError "{tag} as {← pp c} does not admit its children: they end before it is \
          complete"
      | _ => throw ex
    | _ => throw ex

end HtmlModel
