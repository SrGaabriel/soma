import Soma.Core.Value
import Soma.Core.Level
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
