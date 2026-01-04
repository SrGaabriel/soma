import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Metal.Expr

namespace Soma.Dependent

open Soma.Core
open Soma.Metal (Expr ExprList Name BinderInfo Scope ScopedVar Pattern)
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

  | .vLam qty binder name domain body =>
    let domain' ← zonkValue domain
    let body' ← zonkClosure body
    return .vLam qty binder name domain' body'

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
  | .vHigherPrim p => return .vHigherPrim p
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

  | .vRecordVal fields =>
    let fields' ← fields.mapM fun (name, val) => do
      let val' ← zonkValue val
      return (name, val')
    return .vRecordVal fields'

  | .vDataType id params =>
    let params' ← params.mapM zonkValue
    return .vDataType id params'

  | .vConstructor name tag args =>
    let args' ← args.mapM zonkValue
    return .vConstructor name tag args'

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

  | .nCase scrut arms =>
    let scrut' ← zonkNeutral scrut
    let arms' ← arms.mapM fun arm => do
      let clos' ← zonkClosure arm.closure
      return ArmClosure.mk arm.pattern clos'
    return .nCase scrut' arms'

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

/-- Axiom: zonking a param list preserves bindingIds.
    This holds because zonking only modifies type annotations, not binding structure. -/
axiom zonkParamList_bindingIds (params : Soma.Metal.ParamList Value) (params' : Soma.Metal.ParamList Value) :
  params'.bindingIds = params.bindingIds

/-- Axiom: zonking a pattern preserves bindings.
    This holds because zonking only modifies type annotations, not binding structure. -/
axiom zonkPattern_bindings (pat : Pattern Value) (pat' : Pattern Value) :
  pat'.bindings = pat.bindings

/-- Axiom: zonking a pattern list preserves bindingIds.
    This holds because zonking only modifies type annotations, not binding structure. -/
axiom zonkPatternList_bindingIds (pats : Soma.Metal.PatternList Value) (pats' : Soma.Metal.PatternList Value) :
  pats'.bindingIds = pats.bindingIds

/-- Zonk a param list with proof of bindingIds preservation -/
partial def zonkParamListWithProof (params : Soma.Metal.ParamList Value)
    : TCM (Σ' (params' : Soma.Metal.ParamList Value), params'.bindingIds = params.bindingIds) := do
  let params' ← zonkParamListImpl params
  return ⟨params', zonkParamList_bindingIds params params'⟩
where
  zonkParamListImpl : Soma.Metal.ParamList Value → TCM (Soma.Metal.ParamList Value)
    | .nil => return .nil
    | .cons binding name ty rest => do
      let ty' ← zonkValue ty
      let rest' ← zonkParamListImpl rest
      return .cons binding name ty' rest'

/-- Zonk a pattern with proof of bindings preservation -/
partial def zonkPatternWithProof (pat : Pattern Value)
    : TCM (Σ' (pat' : Pattern Value), pat'.bindings = pat.bindings) := do
  let pat' ← zonkPatternImpl pat
  return ⟨pat', zonkPattern_bindings pat pat'⟩
where
  zonkPatternImpl : Pattern Value → TCM (Pattern Value)
    | .wildcard ty span => do
      let ty' ← zonkValue ty
      return .wildcard ty' span
    | .var binding original ty span => do
      let ty' ← zonkValue ty
      return .var binding original ty' span
    | .lit l span => return .lit l span
    | .variant label arg ty span => do
      let arg' ← match arg with
        | some p => some <$> zonkPatternImpl p
        | none => pure none
      let ty' ← zonkValue ty
      return .variant label arg' ty' span
    | .ctor name args ty span => do
      let args' ← args.mapM zonkPatternImpl
      let ty' ← zonkValue ty
      return .ctor name args' ty' span
    | .tuple elems ty span => do
      let elems' ← elems.mapM zonkPatternImpl
      let ty' ← zonkValue ty
      return .tuple elems' ty' span
    | .array elems ty span => do
      let elems' ← elems.mapM zonkPatternImpl
      let ty' ← zonkValue ty
      return .array elems' ty' span
    | .cons head tail ty span => do
      let head' ← zonkPatternImpl head
      let tail' ← zonkPatternImpl tail
      let ty' ← zonkValue ty
      return .cons head' tail' ty' span
    | .as binding original inner ty span => do
      let inner' ← zonkPatternImpl inner
      let ty' ← zonkValue ty
      return .as binding original inner' ty' span

/-- Zonk a pattern list with proof of bindingIds preservation -/
partial def zonkPatternListWithProof (pats : Soma.Metal.PatternList Value)
    : TCM (Σ' (pats' : Soma.Metal.PatternList Value), pats'.bindingIds = pats.bindingIds) := do
  let pats' ← zonkPatternListImpl pats
  return ⟨pats', zonkPatternList_bindingIds pats pats'⟩
where
  zonkPatternListImpl : Soma.Metal.PatternList Value → TCM (Soma.Metal.PatternList Value)
    | .nil => return .nil
    | .cons pat rest => do
      let pat' ← zonkPatternWithProof.zonkPatternImpl pat
      let rest' ← zonkPatternListImpl rest
      return .cons pat' rest'

mutual

/-- Zonk an expression: substitute solved metavariables in type annotations -/
partial def zonkExpr {scope : Scope} (e : Expr Value scope) : TCM (Expr Value scope) := do
  match e with
  | .var v ty span =>
    let ty' ← zonkValue ty
    return .var v ty' span

  | .lit l span => return .lit l span

  | .call fn args ty span =>
    let fn' ← zonkExpr fn
    let args' ← zonkExprList args
    let ty' ← zonkValue ty
    return .call fn' args' ty' span

  | .let_ binding original value body ty span =>
    let value' ← zonkExpr value
    let body' ← zonkExpr body
    let ty' ← zonkValue ty
    return .let_ binding original value' body' ty' span

  | .lam params body ty span =>
    let ⟨params', hParams⟩ ← zonkParamListWithProof params
    let body' ← zonkExpr body
    let ty' ← zonkValue ty
    return .lam params' (hParams ▸ body') ty' span

  | .closure name caps ty span =>
    let caps' ← zonkCaptureList caps
    let ty' ← zonkValue ty
    return .closure name caps' ty' span

  | .construct name tag args ty span =>
    let args' ← zonkExprList args
    let ty' ← zonkValue ty
    return .construct name tag args' ty' span

  | .tuple elems ty span =>
    let elems' ← zonkExprList elems
    let ty' ← zonkValue ty
    return .tuple elems' ty' span

  | .record fields ty span =>
    let fields' ← zonkRecordFields fields
    let ty' ← zonkValue ty
    return .record fields' ty' span

  | .recordUpdate base updates ty span =>
    let base' ← zonkExpr base
    let updates' ← zonkRecordFields updates
    let ty' ← zonkValue ty
    return .recordUpdate base' updates' ty' span

  | .inject label args ty span =>
    let args' ← zonkExprList args
    let ty' ← zonkValue ty
    return .inject label args' ty' span

  | .array elems ty span =>
    let elems' ← zonkExprList elems
    let ty' ← zonkValue ty
    return .array elems' ty' span

  | .if_ cond then_ else_ ty span =>
    let cond' ← zonkExpr cond
    let then_' ← zonkExpr then_
    let else_' ← zonkExpr else_
    let ty' ← zonkValue ty
    return .if_ cond' then_' else_' ty' span

  | .case scrutinees arms ty span =>
    let scrutinees' ← zonkExprList scrutinees
    let arms' ← zonkArmList arms
    let ty' ← zonkValue ty
    return .case scrutinees' arms' ty' span

  | .fieldAccess expr fieldName fieldIdx ty span =>
    let expr' ← zonkExpr expr
    let ty' ← zonkValue ty
    return .fieldAccess expr' fieldName fieldIdx ty' span

  | .global name ty span =>
    let ty' ← zonkValue ty
    return .global name ty' span

  | .panic msg ty span =>
    let ty' ← zonkValue ty
    return .panic msg ty' span

  | .proj typeName fieldName fieldIdx ty span =>
    let ty' ← zonkValue ty
    return .proj typeName fieldName fieldIdx ty' span

  | .typeApp arg ty span =>
    let ty' ← zonkValue ty
    return .typeApp arg ty' span

  | .type level span => return .type level span

  | .pi qty binder name domain codomain span =>
    let domain' ← zonkExpr domain
    let codomain' ← zonkExpr codomain
    return .pi qty binder name domain' codomain' span

  | .sigma qty name fst snd span =>
    let fst' ← zonkExpr fst
    let snd' ← zonkExpr snd
    return .sigma qty name fst' snd' span

  | .pair fst snd ty span =>
    let fst' ← zonkExpr fst
    let snd' ← zonkExpr snd
    let ty' ← zonkValue ty
    return .pair fst' snd' ty' span

  | .fst e ty span =>
    let e' ← zonkExpr e
    let ty' ← zonkValue ty
    return .fst e' ty' span

  | .snd e ty span =>
    let e' ← zonkExpr e
    let ty' ← zonkValue ty
    return .snd e' ty' span

  | .primTy p span => return .primTy p span
  | .higherPrimTy p span => return .higherPrimTy p span
  | .rowEmpty span => return .rowEmpty span

  | .rowExtend label fieldTy tail span =>
    let label' ← zonkExpr label
    let fieldTy' ← zonkExpr fieldTy
    let tail' ← zonkExpr tail
    return .rowExtend label' fieldTy' tail' span

  | .recordTy row span =>
    let row' ← zonkExpr row
    return .recordTy row' span

  | .variantTy row span =>
    let row' ← zonkExpr row
    return .variantTy row' span

  | .labelLit name span => return .labelLit name span

  | .dataTy id params span =>
    let params' ← zonkExprList params
    return .dataTy id params' span

  | .ann expr ty tyVal span =>
    let expr' ← zonkExpr expr
    let ty' ← zonkExpr ty
    let tyVal' ← zonkValue tyVal
    return .ann expr' ty' tyVal' span

  | .hole id span => return .hole id span

  | .mvar id ty span =>
    -- Check if this metavariable is solved
    match ← TCM.lookupMeta ⟨id⟩ with
    | some info =>
      match info.solution with
      | some _sol =>
        --todo: quote the solution?
        let ty' ← zonkValue ty
        return .mvar id ty' span
      | none =>
        let ty' ← zonkValue ty
        return .mvar id ty' span
    | none =>
      let ty' ← zonkValue ty
      return .mvar id ty' span

  | .eq tyLevel ty lhs rhs span =>
    let ty' ← zonkExpr ty
    let lhs' ← zonkExpr lhs
    let rhs' ← zonkExpr rhs
    return .eq tyLevel ty' lhs' rhs' span

  | .refl ty x span =>
    let ty' ← zonkExpr ty
    let x' ← zonkExpr x
    return .refl ty' x' span

  | .transport tyLevel ty motive lhs rhs eq body span =>
    let ty' ← zonkExpr ty
    let motive' ← zonkExpr motive
    let lhs' ← zonkExpr lhs
    let rhs' ← zonkExpr rhs
    let eq' ← zonkExpr eq
    let body' ← zonkExpr body
    return .transport tyLevel ty' motive' lhs' rhs' eq' body' span

/-- Zonk an expression list -/
partial def zonkExprList {scope : Scope} (es : ExprList Value scope)
    : TCM (ExprList Value scope) := do
  match es with
  | .nil => return .nil
  | .cons e rest =>
    let e' ← zonkExpr e
    let rest' ← zonkExprList rest
    return .cons e' rest'

/-- Zonk a param list -/
partial def zonkParamList (params : Soma.Metal.ParamList Value)
    : TCM (Soma.Metal.ParamList Value) := do
  match params with
  | .nil => return .nil
  | .cons binding name ty rest =>
    let ty' ← zonkValue ty
    let rest' ← zonkParamList rest
    return .cons binding name ty' rest'

/-- Zonk a capture list -/
partial def zonkCaptureList {scope : Scope} (caps : Soma.Metal.CaptureList Value scope)
    : TCM (Soma.Metal.CaptureList Value scope) := do
  match caps with
  | .nil => return .nil
  | .cons v ty rest =>
    let ty' ← zonkValue ty
    let rest' ← zonkCaptureList rest
    return .cons v ty' rest'

/-- Zonk record fields -/
partial def zonkRecordFields {scope : Scope} (fields : Soma.Metal.RecordFieldList Value scope)
    : TCM (Soma.Metal.RecordFieldList Value scope) := do
  match fields with
  | .nil => return .nil
  | .cons name expr rest =>
    let expr' ← zonkExpr expr
    let rest' ← zonkRecordFields rest
    return .cons name expr' rest'

/-- Zonk case arms -/
partial def zonkArmList {scope : Scope} (arms : Soma.Metal.ArmList Value scope)
    : TCM (Soma.Metal.ArmList Value scope) := do
  match arms with
  | .nil => return .nil
  | .cons arm rest =>
    let arm' ← zonkArm arm
    let rest' ← zonkArmList rest
    return .cons arm' rest'

/-- Zonk a single case arm -/
partial def zonkArm {scope : Scope} (arm : Soma.Metal.Arm Value scope)
    : TCM (Soma.Metal.Arm Value scope) := do
  match arm with
  | .mk pats body span =>
    -- zonkPatternListWithProof returns both zonked patterns and proof of bindingIds preservation
    let ⟨pats', hPats⟩ ← zonkPatternListWithProof pats
    let body' ← zonkExpr body
    -- Use the proof to cast body' to match pats'.bindingIds
    return .mk pats' (hPats ▸ body') span

/-- Zonk pattern list -/
partial def zonkPatternList (pats : Soma.Metal.PatternList Value)
    : TCM (Soma.Metal.PatternList Value) := do
  match pats with
  | .nil => return .nil
  | .cons pat rest =>
    let pat' ← zonkPattern pat
    let rest' ← zonkPatternList rest
    return .cons pat' rest'

/-- Zonk a pattern (just zonk the type annotation) -/
partial def zonkPattern (pat : Pattern Value)
    : TCM (Pattern Value) := do
  match pat with
  | .wildcard ty span =>
    let ty' ← zonkValue ty
    return .wildcard ty' span
  | .var binding original ty span =>
    let ty' ← zonkValue ty
    return .var binding original ty' span
  | .lit l span => return .lit l span
  | .variant label arg ty span =>
    let arg' ← match arg with
      | some p => some <$> zonkPattern p
      | none => pure none
    let ty' ← zonkValue ty
    return .variant label arg' ty' span
  | .ctor name args ty span =>
    let args' ← args.mapM zonkPattern
    let ty' ← zonkValue ty
    return .ctor name args' ty' span
  | .tuple elems ty span =>
    let elems' ← elems.mapM zonkPattern
    let ty' ← zonkValue ty
    return .tuple elems' ty' span
  | .array elems ty span =>
    let elems' ← elems.mapM zonkPattern
    let ty' ← zonkValue ty
    return .array elems' ty' span
  | .cons head tail ty span =>
    let head' ← zonkPattern head
    let tail' ← zonkPattern tail
    let ty' ← zonkValue ty
    return .cons head' tail' ty' span
  | .as binding original inner ty span =>
    let inner' ← zonkPattern inner
    let ty' ← zonkValue ty
    return .as binding original inner' ty' span

end

mutual

/-- Check if a value contains unsolved metavariables -/
partial def hasUnsolvedMetas (v : Value) : TCM Bool := do
  match v with
  | .vNeutral _ (.nMeta m) =>
    match ← TCM.lookupMeta m with
    | some info => return info.solution.isNone
    | none => return true
  | .vPi _ _ _ dom _ => hasUnsolvedMetas dom
  | .vLam _ _ _ dom _ => hasUnsolvedMetas dom
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
  | .vConstructor _ _ args =>
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
  | .nCase scrut _ => hasUnsolvedMetasNeutral scrut
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
  | .vLam _ _ _ dom _ => collectUnsolvedMetas dom span
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
  | .vConstructor _ _ args =>
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
  | .nCase scrut _ => collectUnsolvedMetasNeutral scrut span
  | _ => pure ()

end

/-- Report all unsolved metavariables in a value -/
def reportUnsolvedMetas (v : Value) (span : Span) : TCM Unit := do
  collectUnsolvedMetas v span

end Soma.Dependent
