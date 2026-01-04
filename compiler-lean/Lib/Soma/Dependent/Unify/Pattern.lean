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

/-- Apply a renaming to a value, producing a Term that uses de Bruijn indices relative to the lambda we're building -/
partial def applySubst (r : Subst) (v : Value) : Option Term :=
  match v with
  | .vType level => some (.type level)
  | .vPi qty binder name dom cod =>
    match applySubst r dom with
    | some domT =>
      -- For the codomain, we'd need to handle the extended scope
      match cod.body with
      | some body => some (.pi qty binder name domT body)
      | none => some (.pi qty binder name domT (.var 0 "_"))
    | none => none
  | .vLam _ _ name dom body =>
    match applySubst r dom with
    | some _domT =>
      match body.body with
      | some bodyT => some (.lam [name] bodyT)
      | none => some (.lam [name] (.var 0 name))
    | none => none
  | .vSigma qty name fst snd =>
    match applySubst r fst with
    | some fstT =>
      match snd.body with
      | some sndBody => some (.sigma qty name fstT sndBody)
      | none => some (.sigma qty name fstT (.var 0 "_"))
    | none => none
  | .vPair a b =>
    match applySubst r a, applySubst r b with
    | some aT, some bT => some (.pair aT bT)
    | _, _ => none
  | .vNeutral _ neu => applySubstNeutral r neu
  | .vPrimTy p => some (.primTy p)
  | .vHigherPrim p => some (.higherPrimTy p)
  | .vIntLit n => some (.intLit n)
  | .vStringLit s => some (.stringLit s)
  | .vRowEmpty => some .rowEmpty
  | .vRowExtend label ty tail =>
    match applySubst r label, applySubst r ty, applySubst r tail with
    | some labelT, some tyT, some tailT => some (.rowExtend labelT tyT tailT)
    | _, _, _ => none
  | .vRecord row =>
    match applySubst r row with
    | some rowT => some (.recordTy rowT)
    | none => none
  | .vVariant row =>
    match applySubst r row with
    | some rowT => some (.variantTy rowT)
    | none => none
  | .vLabelLit name => some (.labelLit name)
  | .vRecordVal fields =>
    let fieldTerms := fields.filterMap (fun (name, v) =>
      match applySubst r v with
      | some t => some (name, t)
      | none => none)
    if fieldTerms.length == fields.length then
      some (.record fieldTerms)
    else
      none
  | .vDataType id params =>
    -- Convert data type with its parameters
    let paramTerms := params.filterMap (applySubst r)
    if paramTerms.length != params.length then none
    else
      let baseTerm := Term.global (Name.user ⟨id.unique, id.module, id.name⟩)
      some (paramTerms.foldl (fun acc p => .app acc [p]) baseTerm)
  | .vConstructor name tag args =>
    let argTerms := args.filterMap (applySubst r)
    if argTerms.length == args.length then
      some (.construct name tag argTerms)
    else
      none
  | .vEq tyLevel ty lhs rhs =>
    match applySubst r ty, applySubst r lhs, applySubst r rhs with
    | some tyT, some lhsT, some rhsT => some (.eq tyLevel tyT lhsT rhsT)
    | _, _, _ => none
  | .vRefl ty x =>
    match applySubst r ty, applySubst r x with
    | some tyT, some xT => some (.refl tyT xT)
    | _, _ => none
  | .vTransport tyLevel ty motive lhs rhs eq body =>
    match applySubst r ty, applySubst r motive, applySubst r lhs,
          applySubst r rhs, applySubst r eq, applySubst r body with
    | some tyT, some motiveT, some lhsT, some rhsT, some eqT, some bodyT =>
      some (.transport tyLevel tyT motiveT lhsT rhsT eqT bodyT)
    | _, _, _, _, _, _ => none

partial def applySubstNeutral (r : Subst) (n : Neutral) : Option Term :=
  match n with
  | .nVar v =>
    match r.lookup v.level with
    | some idx => some (.var idx v.name)
    | none => none  -- Variable not in scope
  | .nMeta id => some (.mvar id.id)
  | .nApp fn arg =>
    match applySubstNeutral r fn, applySubst r arg with
    | some fnT, some argT => some (.app fnT [argT])
    | _, _ => none
  | .nFst pair =>
    match applySubstNeutral r pair with
    | some pairT => some (.fst pairT)
    | none => none
  | .nSnd pair =>
    match applySubstNeutral r pair with
    | some pairT => some (.snd pairT)
    | none => none
  | .nFieldAccess rec field =>
    match applySubstNeutral r rec with
    | some recT => some (.fieldAccess recT field)
    | none => none
  | .nCase scrut arms =>
    match applySubstNeutral r scrut with
    | some scrutT =>
      -- Convert each arm: apply the closure to get the body, then convert
      let armTerms := arms.filterMap fun arm =>
        match arm.closure.body with
        | some bodyTerm => some (arm.pattern, 0, bodyTerm)
        | none => none
      if armTerms.length == arms.length then
        some (.case scrutT armTerms)
      else
        none  -- Can't convert all arms
    | none => none

end

/-- Build nested lambdas from the spine -/
def buildLambdaSolution (spineLevels : List DeBruijnLvl) (body : Term) : Term :=
  let names := spineLevels.map (fun lvl => s!"x{lvl.lvl}")
  if names.isEmpty then body else .lam names body

/-- Evaluate a Term to a Value (simplified) -/
def evalSolutionTerm (t : Term) : TCM Value := TCM.evalTerm t

end Soma.Dependent
