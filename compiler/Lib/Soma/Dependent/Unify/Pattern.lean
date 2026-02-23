import Soma.Core.Value
import Soma.Core.Eval
import Soma.Dependent.Monad
import Soma.Dependent.Unify.Core

namespace Soma.Dependent

open Soma.Core

/-- A renaming maps levels in the RHS to levels in the spine.
    For ?m x y = t, if t mentions x at level 0 and y at level 1,
    we need to know which spine argument corresponds to each. -/
structure Subst where
  /-- Map from RHS levels to spine positions -/
  mapping : List (DeBruijnLvl × Nat)
  deriving Inhabited

/-- Create a renaming from spine levels -/
def mkSubst (spineLevels : List DeBruijnLvl) : Subst :=
  ⟨enumList spineLevels |>.map (fun (i, lvl) => (lvl, i))⟩

/-- Look up a level in the renaming -/
def Subst.lookup (r : Subst) (lvl : DeBruijnLvl) : Option Nat :=
  match r.mapping.find? (fun (l, _) => l == lvl) with
  | some (_, idx) => some idx
  | none => none

mutual

/-- Apply a renaming to a value, producing an Expr that uses de Bruijn indices relative to the lambda we're building -/
partial def applySubst (r : Subst) (v : Value) : Option Soma.Core.Expr :=
  match v with
  | .vType level => some (.sort level)
  | .vPi qty binder name dom cod =>
    match applySubst r dom with
    | some domE =>
      match cod.body with
      | some body => some (.pi qty binder name domE body)
      | none => some (.pi qty binder name domE (.bvar 0))
    | none => none
  | .vLam name body =>
    match body.body with
    | some bodyE => some (.lam .explicit name (.sort Level.zero) bodyE)
    | none => some (.lam .explicit name (.sort Level.zero) (.bvar 0))
  | .vSigma qty name fst snd =>
    match applySubst r fst with
    | some fstE =>
      match snd.body with
      | some sndBody => some (.sigma qty .explicit name fstE sndBody)
      | none => some (.sigma qty .explicit name fstE (.bvar 0))
    | none => none
  | .vPair a b =>
    match applySubst r a, applySubst r b with
    | some aE, some bE => some (.pair aE bE)
    | _, _ => none
  | .vNeutral _ neu => applySubstNeutral r neu
  | .vPrimTy p => some (.primTy p)
  | .vIntLit n => some (.lit (.int n))
  | .vStringLit s => some (.lit (.string s))
  | .vRowEmpty => some .rowEmpty
  | .vRowExtend label ty tail =>
    match applySubst r label, applySubst r ty, applySubst r tail with
    | some labelE, some tyE, some tailE => some (.rowExtend labelE tyE tailE)
    | _, _, _ => none
  | .vRecord row =>
    match applySubst r row with
    | some rowE => some (.recordTy rowE)
    | none => none
  | .vVariant row =>
    match applySubst r row with
    | some rowE => some (.variantTy rowE)
    | none => none
  | .vLabelLit name => some (.labelLit name)
  | .vRowSort => some .rowSort
  | .vLabelSort => some .labelSort
  | .vRecordVal fields =>
    let fieldExprs := fields.filterMap (fun (name, v) =>
      match applySubst r v with
      | some e => some (name, e)
      | none => none)
    if fieldExprs.length == fields.length then
      some (.record fieldExprs.toArray)
    else
      none
  | .vDataType id params =>
    let paramExprs := params.filterMap (applySubst r)
    if paramExprs.length != params.length then none
    else
      let baseExpr := Soma.Core.Expr.const ⟨⟨id.unique, id.module, id.name⟩⟩
      some (paramExprs.foldl (fun acc p => .app acc p) baseExpr)
  | .vConstructor name tag args =>
    let argExprs := args.filterMap (applySubst r)
    if argExprs.length == args.length then
      some (.construct name tag argExprs.toArray)
    else
      none
  | .vEq tyLevel ty lhs rhs =>
    match applySubst r ty, applySubst r lhs, applySubst r rhs with
    | some tyE, some lhsE, some rhsE => some (.eqTy tyLevel tyE lhsE rhsE)
    | _, _, _ => none
  | .vRefl ty x =>
    match applySubst r ty, applySubst r x with
    | some tyE, some xE => some (.refl tyE xE)
    | _, _ => none
  | .vTransport tyLevel ty motive lhs rhs eq body =>
    match applySubst r ty, applySubst r motive, applySubst r lhs,
          applySubst r rhs, applySubst r eq, applySubst r body with
    | some tyE, some motiveE, some lhsE, some rhsE, some eqE, some bodyE =>
      some (.transport tyLevel tyE motiveE lhsE rhsE eqE bodyE)
    | _, _, _, _, _, _ => none

partial def applySubstNeutral (r : Subst) (n : Neutral) : Option Soma.Core.Expr :=
  match n with
  | .nVar v =>
    match r.lookup v.level with
    | some idx => some (.bvar idx)
    | none => none  -- Variable not in scope
  | .nMeta id => some (.mvar id)
  | .nApp fn arg =>
    match applySubstNeutral r fn, applySubst r arg with
    | some fnE, some argE => some (.app fnE argE)
    | _, _ => none
  | .nFst pair =>
    match applySubstNeutral r pair with
    | some pairE => some (.projFst pairE)
    | none => none
  | .nSnd pair =>
    match applySubstNeutral r pair with
    | some pairE => some (.projSnd pairE)
    | none => none
  | .nFieldAccess rec field =>
    match applySubstNeutral r rec with
    | some recE => some (.fieldAccess recE field 0)
    | none => none
  | .nCase scrut arms =>
    match applySubstNeutral r scrut with
    | some scrutE =>
      let armExprs := arms.filterMap fun arm =>
        match arm.closure.body with
        | some bodyExpr => some (Soma.Core.Arm.mk #[Soma.Core.Pattern.wildcard] bodyExpr)
        | none => none
      if armExprs.length == arms.length then
        some (.«case» #[scrutE] armExprs.toArray)
      else
        none
    | none => none

end

/-- Build nested lambdas from the spine -/
def buildLambdaSolution (spineLevels : List DeBruijnLvl) (body : Soma.Core.Expr) : Soma.Core.Expr :=
  spineLevels.foldr (fun lvl acc =>
    Soma.Core.Expr.lam .explicit s!"x{lvl.lvl}" (.sort Level.zero) acc) body

/-- Evaluate a solution Expr to a Value -/
def evalSolutionTerm (t : Soma.Core.Expr) : TCM Value := do
  let ctx ← TCM.getCtx
  let state ← TCM.getState
  let evalCtx : EvalCtx := {
    env := ctx.env
    globals := ctx.globals.toGlobalEnv
    metas := state.metas
  }
  return evalCoreExpr evalCtx t

end Soma.Dependent
