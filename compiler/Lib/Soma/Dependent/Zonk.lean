import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quote
import Soma.Dependent.Monad
import Soma.Dependent.Convert

namespace Soma.Dependent

open Soma.Core
open Soma.Syntax (Span)

mutual

/-- Zonk a Value: substitute all solved metavariables -/
partial def zonkValue (v : Value) : TCM Value := do
  match v with
  | .vType level =>
    let level' ← zonkLevel level
    return .vType level'

  | .vPi qty binder name domain codomain =>
    let domain' ← zonkValue domain
    let codomain' ← zonkClosure codomain
    return .vPi qty binder name domain' codomain'

  | .vLam name body =>
    let body' ← zonkClosure body
    return .vLam name body'

  | .vSigma qty name fst snd =>
    let fst' ← zonkValue fst
    let snd' ← zonkClosure snd
    return .vSigma qty name fst' snd'

  | .vPair a b =>
    let a' ← zonkValue a
    let b' ← zonkValue b
    return .vPair a' b'

  | .vNeutral ty neu =>
    -- First check if the neutral is a solved meta
    match neu with
    | .nMeta m =>
      match ← TCM.lookupMeta m with
      | some info =>
        match info.solution with
        | some sol => zonkValue sol  -- Substitute and continue zonking
        | none => return .vNeutral (← zonkValue ty) neu  -- Unsolved
      | none => return .vNeutral (← zonkValue ty) neu
    | _ =>
      let ty' ← zonkValue ty
      let neu' ← zonkNeutral neu
      return .vNeutral ty' neu'

  | .vPrimTy p => return .vPrimTy p
  | .vIntLit n => return .vIntLit n
  | .vStringLit s => return .vStringLit s

  | .vRowEmpty => return .vRowEmpty

  | .vRowExtend label ty tail =>
    let label' ← zonkValue label
    let ty' ← zonkValue ty
    let tail' ← zonkValue tail
    return .vRowExtend label' ty' tail'

  | .vRecord row =>
    let row' ← zonkValue row
    return .vRecord row'

  | .vVariant row =>
    let row' ← zonkValue row
    return .vVariant row'

  | .vLabelLit name => return .vLabelLit name

  | .vRowSort => return .vRowSort
  | .vLabelSort => return .vLabelSort

  | .vRecordVal fields =>
    let fields' ← fields.mapM fun (name, val) => do
      let val' ← zonkValue val
      return (name, val')
    return .vRecordVal fields'

  | .vDataType id params =>
    let params' ← params.mapM zonkValue
    return .vDataType id params'

  | .vConstructor name tag args rty =>
    let args' ← args.mapM zonkValue
    let rty' ← zonkValue rty
    return .vConstructor name tag args' rty'

  | .vEq tyLevel ty lhs rhs =>
    let tyLevel' ← zonkLevel tyLevel
    let ty' ← zonkValue ty
    let lhs' ← zonkValue lhs
    let rhs' ← zonkValue rhs
    return .vEq tyLevel' ty' lhs' rhs'

  | .vRefl ty x =>
    let ty' ← zonkValue ty
    let x' ← zonkValue x
    return .vRefl ty' x'

  | .vTransport tyLevel ty motive lhs rhs eq body =>
    let tyLevel' ← zonkLevel tyLevel
    let ty' ← zonkValue ty
    let motive' ← zonkValue motive
    let lhs' ← zonkValue lhs
    let rhs' ← zonkValue rhs
    let eq' ← zonkValue eq
    let body' ← zonkValue body
    return .vTransport tyLevel' ty' motive' lhs' rhs' eq' body'

/-- Zonk a neutral term -/
partial def zonkNeutral (n : Neutral) : TCM Neutral := do
  match n with
  | .nVar v => return .nVar v

  | .nMeta m =>
    -- Check if solved
    match ← TCM.lookupMeta m with
    | some info =>
      match info.solution with
      | some _sol =>
        -- Solution found - but we need to return a Neutral
        -- The caller should handle this case before calling zonkNeutral
        return .nMeta m
      | none => return .nMeta m
    | none => return .nMeta m

  | .nApp fn arg =>
    let fn' ← zonkNeutral fn
    let arg' ← zonkValue arg
    return .nApp fn' arg'

  | .nFst pair =>
    let pair' ← zonkNeutral pair
    return .nFst pair'

  | .nSnd pair =>
    let pair' ← zonkNeutral pair
    return .nSnd pair'

  | .nFieldAccess rec field =>
    let rec' ← zonkNeutral rec
    return .nFieldAccess rec' field

  | .nCase scrut arms rty =>
    let scrut' ← zonkNeutral scrut
    let arms' ← arms.mapM fun arm => do
      let clos' ← zonkClosure arm.closure
      return ArmClosure.mk arm.pattern clos'
    let rty' ← zonkValue rty
    return .nCase scrut' arms' rty'

/-- Zonk a closure -/
partial def zonkClosure (clos : Closure) : TCM Closure := do
  match clos with
  | .const name value =>
    -- For HOAS closures, zonk the stored value
    let value' ← zonkValue value
    return Closure.const name value'
  | .term name env body =>
    -- For term closures, zonk the environment values
    let env' ← zonkEnv env
    return Closure.term name env' body

/-- Zonk an environment -/
partial def zonkEnv (env : Env) : TCM Env := do
  let values' ← env.values.mapM fun (name, val) => do
    let val' ← zonkValue val
    return (name, val')
  return Env.mk values' env.size

/-- Zonk a universe level (substitute level variables) -/
partial def zonkLevel (l : Level) : TCM Level := do
  -- todo: substitute solved level variables.
  return l.simplify

end

/-- Zonk a Core.Expr: substitute all solved metavariables in type annotations and terms -/
partial def zonkExpr (e : Expr) (depth : Nat := 0) : TCM Expr := do
  match e with
  | .mvar id =>
    match ← TCM.lookupMeta id with
    | some info =>
      match info.solution with
      | some sol =>
        let zonked ← zonkValue sol
        return Soma.Core.quoteExpr ⟨depth⟩ zonked
      | none => return e
    | none => return e

  | .bvar _ | .sort _ | .primTy _ | .rowSort | .labelSort
  | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .lit _ => return e

  | .fvar id ty => return .fvar id (← zonkExpr ty depth)
  | .const name ty => return .const name (← zonkExpr ty depth)

  | .app fn arg => return .app (← zonkExpr fn depth) (← zonkExpr arg depth)

  | .lam info name dom body =>
    return .lam info name (← zonkExpr dom depth) (← zonkExpr body (depth + 1))

  | .let_ name ty val body =>
    return .let_ name (← zonkExpr ty depth) (← zonkExpr val depth) (← zonkExpr body (depth + 1))

  | .pi qty info name dom cod =>
    return .pi qty info name (← zonkExpr dom depth) (← zonkExpr cod (depth + 1))

  | .sigma qty info name fst snd =>
    return .sigma qty info name (← zonkExpr fst depth) (← zonkExpr snd (depth + 1))

  | .pair fst snd => return .pair (← zonkExpr fst depth) (← zonkExpr snd depth)
  | .projFst e => return .projFst (← zonkExpr e depth)
  | .projSnd e => return .projSnd (← zonkExpr e depth)

  | .construct name tag args resultTy =>
    let args' ← args.mapM (zonkExpr · depth)
    return .construct name tag args' (← zonkExpr resultTy depth)

  | .«case» scruts arms resultTy =>
    let scruts' ← scruts.mapM (zonkExpr · depth)
    let arms' ← arms.mapM fun arm => do
      let binds := arm.patterns.foldl (fun acc p => acc + p.bindingCount) 0
      let body' ← zonkExpr arm.body (depth + binds)
      return Arm.mk arm.patterns body'
    return .«case» scruts' arms' (← zonkExpr resultTy depth)

  | .record fields =>
    let fields' ← fields.mapM fun (name, e) => return (name, ← zonkExpr e depth)
    return .record fields'

  | .recordUpdate base updates =>
    let base' ← zonkExpr base depth
    let updates' ← updates.mapM fun (name, e) => return (name, ← zonkExpr e depth)
    return .recordUpdate base' updates'

  | .fieldAccess e field idx => return .fieldAccess (← zonkExpr e depth) field idx

  | .inject label args resultTy =>
    let args' ← args.mapM (zonkExpr · depth)
    return .inject label args' (← zonkExpr resultTy depth)

  | .if_ cond then_ else_ =>
    return .if_ (← zonkExpr cond depth) (← zonkExpr then_ depth) (← zonkExpr else_ depth)

  | .closure name captures =>
    let captures' ← captures.mapM (zonkExpr · depth)
    return .closure name captures'

  | .array elems resultTy =>
    let elems' ← elems.mapM (zonkExpr · depth)
    return .array elems' (← zonkExpr resultTy depth)

  | .tuple elems =>
    let elems' ← elems.mapM (zonkExpr · depth)
    return .tuple elems'

  | .rowExtend label fieldTy tail =>
    return .rowExtend (← zonkExpr label depth) (← zonkExpr fieldTy depth) (← zonkExpr tail depth)

  | .recordTy row => return .recordTy (← zonkExpr row depth)
  | .variantTy row => return .variantTy (← zonkExpr row depth)
  | .dataTy id params =>
    let params' ← params.mapM (zonkExpr · depth)
    return .dataTy id params'

  | .eqTy lv ty lhs rhs =>
    return .eqTy lv (← zonkExpr ty depth) (← zonkExpr lhs depth) (← zonkExpr rhs depth)
  | .refl ty x => return .refl (← zonkExpr ty depth) (← zonkExpr x depth)
  | .transport lv ty motive lhs rhs eq body =>
    return .transport lv (← zonkExpr ty depth) (← zonkExpr motive depth)
      (← zonkExpr lhs depth) (← zonkExpr rhs depth)
      (← zonkExpr eq depth) (← zonkExpr body depth)

  | .ann expr ty => return .ann (← zonkExpr expr depth) (← zonkExpr ty depth)

mutual

/-- Check if a value contains unsolved metavariables -/
partial def hasUnsolvedMetas (v : Value) : TCM Bool := do
  match v with
  | .vNeutral _ (.nMeta m) =>
    match ← TCM.lookupMeta m with
    | some info => return info.solution.isNone
    | none => return true
  | .vPi _ _ _ dom _ => hasUnsolvedMetas dom
  | .vLam _ _ => return false
  | .vSigma _ _ fst _ => hasUnsolvedMetas fst
  | .vPair a b =>
    if ← hasUnsolvedMetas a then return true
    hasUnsolvedMetas b
  | .vNeutral ty neu =>
    if ← hasUnsolvedMetas ty then return true
    hasUnsolvedMetasNeutral neu
  | .vRowExtend label ty tail =>
    if ← hasUnsolvedMetas label then return true
    if ← hasUnsolvedMetas ty then return true
    hasUnsolvedMetas tail
  | .vRecord row => hasUnsolvedMetas row
  | .vVariant row => hasUnsolvedMetas row
  | .vRecordVal fields =>
    for (_, val) in fields do
      if ← hasUnsolvedMetas val then return true
    return false
  | .vDataType _ params =>
    for p in params do
      if ← hasUnsolvedMetas p then return true
    return false
  | .vConstructor _ _ args _ =>
    for a in args do
      if ← hasUnsolvedMetas a then return true
    return false
  | .vEq _ ty lhs rhs =>
    if ← hasUnsolvedMetas ty then return true
    if ← hasUnsolvedMetas lhs then return true
    hasUnsolvedMetas rhs
  | .vRefl ty x =>
    if ← hasUnsolvedMetas ty then return true
    hasUnsolvedMetas x
  | .vTransport _ ty motive lhs rhs eq body =>
    if ← hasUnsolvedMetas ty then return true
    if ← hasUnsolvedMetas motive then return true
    if ← hasUnsolvedMetas lhs then return true
    if ← hasUnsolvedMetas rhs then return true
    if ← hasUnsolvedMetas eq then return true
    hasUnsolvedMetas body
  | _ => return false

partial def hasUnsolvedMetasNeutral (n : Neutral) : TCM Bool := do
  match n with
  | .nMeta m =>
    match ← TCM.lookupMeta m with
    | some info => return info.solution.isNone
    | none => return true
  | .nApp fn arg =>
    if ← hasUnsolvedMetasNeutral fn then return true
    hasUnsolvedMetas arg
  | .nFst pair => hasUnsolvedMetasNeutral pair
  | .nSnd pair => hasUnsolvedMetasNeutral pair
  | .nFieldAccess rec _ => hasUnsolvedMetasNeutral rec
  | .nCase scrut _ _ => hasUnsolvedMetasNeutral scrut
  | _ => return false

end

mutual

partial def collectUnsolvedMetas (v : Value) (span : Span) : TCM Unit := do
  match v with
  | .vNeutral ty (.nMeta m) =>
    match ← TCM.lookupMeta m with
    | some info =>
      if info.solution.isNone then
        TCM.addError (.unsolvedMeta m info.type span #[] none)
    | none =>
      TCM.addError (.unsolvedMeta m ty span #[] none)
  | .vPi _ _ _ dom _ => collectUnsolvedMetas dom span
  | .vLam _ _ => pure ()
  | .vSigma _ _ fst _ => collectUnsolvedMetas fst span
  | .vPair a b =>
    collectUnsolvedMetas a span
    collectUnsolvedMetas b span
  | .vNeutral ty neu =>
    collectUnsolvedMetas ty span
    collectUnsolvedMetasNeutral neu span
  | .vRowExtend label ty tail =>
    collectUnsolvedMetas label span
    collectUnsolvedMetas ty span
    collectUnsolvedMetas tail span
  | .vRecord row => collectUnsolvedMetas row span
  | .vVariant row => collectUnsolvedMetas row span
  | .vRecordVal fields =>
    for (_, val) in fields do
      collectUnsolvedMetas val span
  | .vDataType _ params =>
    for p in params do
      collectUnsolvedMetas p span
  | .vConstructor _ _ args _ =>
    for a in args do
      collectUnsolvedMetas a span
  | .vEq _ ty lhs rhs =>
    collectUnsolvedMetas ty span
    collectUnsolvedMetas lhs span
    collectUnsolvedMetas rhs span
  | .vRefl ty x =>
    collectUnsolvedMetas ty span
    collectUnsolvedMetas x span
  | .vTransport _ ty motive lhs rhs eq body =>
    collectUnsolvedMetas ty span
    collectUnsolvedMetas motive span
    collectUnsolvedMetas lhs span
    collectUnsolvedMetas rhs span
    collectUnsolvedMetas eq span
    collectUnsolvedMetas body span
  | _ => pure ()

partial def collectUnsolvedMetasNeutral (n : Neutral) (span : Span) : TCM Unit := do
  match n with
  | .nMeta m =>
    match ← TCM.lookupMeta m with
    | some info =>
      if info.solution.isNone then
        TCM.addError (.unsolvedMeta m info.type span #[] none)
    | none => pure ()
  | .nApp fn arg =>
    collectUnsolvedMetasNeutral fn span
    collectUnsolvedMetas arg span
  | .nFst pair => collectUnsolvedMetasNeutral pair span
  | .nSnd pair => collectUnsolvedMetasNeutral pair span
  | .nFieldAccess rec _ => collectUnsolvedMetasNeutral rec span
  | .nCase scrut _ _ => collectUnsolvedMetasNeutral scrut span
  | _ => pure ()

end

/-- Report all unsolved metavariables in a value -/
def reportUnsolvedMetas (v : Value) (span : Span) : TCM Unit := do
  collectUnsolvedMetas v span

end Soma.Dependent
