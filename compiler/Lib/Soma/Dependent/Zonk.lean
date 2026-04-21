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
    let forced ← force v
    match forced with
    | .vNeutral ty' neu' =>
      let ty'' ← zonkValue ty'
      let neu'' ← zonkNeutral neu'
      return .vNeutral ty'' neu''
    | other => zonkValue other

  | .vPrimTy p => return .vPrimTy p
  | .vIntLit n => return .vIntLit n
  | .vFloatLit f => return .vFloatLit f
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
  | .nConst qn ty => return .nConst qn ty

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

  | .nCase scrutinees arms rty =>
    let scrutinees' ← scrutinees.mapM zonkValue
    let arms' ← arms.mapM fun arm => do
      let clos' ← zonkClosure arm.closure
      return ArmClosure.mk arm.pattern clos'
    let rty' ← zonkValue rty
    return .nCase scrutinees' arms' rty'

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

/-- Collect all mvar IDs from an expression -/
partial def collectMvarIds (e : Expr) (acc : Std.HashSet MetaId := {}) : Std.HashSet MetaId :=
  match e with
  | .mvar id => acc.insert id
  | .bvar _ | .sort _ | .primTy _ | .rowSort | .labelSort
  | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .lit _ => acc
  | .fvar _ ty => collectMvarIds ty acc
  | .const _ ty => collectMvarIds ty acc
  | .app fn arg => collectMvarIds arg (collectMvarIds fn acc)
  | .lam _ _ dom body => collectMvarIds body (collectMvarIds dom acc)
  | .let_ _ ty val body => collectMvarIds body (collectMvarIds val (collectMvarIds ty acc))
  | .pi _ _ _ dom cod => collectMvarIds cod (collectMvarIds dom acc)
  | .sigma _ _ _ fst snd => collectMvarIds snd (collectMvarIds fst acc)
  | .pair fst snd => collectMvarIds snd (collectMvarIds fst acc)
  | .projFst e => collectMvarIds e acc
  | .projSnd e => collectMvarIds e acc
  | .construct _ _ args rty =>
    args.foldl (fun a e => collectMvarIds e a) acc |> collectMvarIds rty
  | .«case» scruts arms rty =>
    let a := scruts.foldl (fun a e => collectMvarIds e a) acc
    let a := arms.foldl (fun a arm => collectMvarIds arm.body a) a
    collectMvarIds rty a
  | .record fields => fields.foldl (fun a (_, e) => collectMvarIds e a) acc
  | .recordUpdate base updates =>
    let a := collectMvarIds base acc
    updates.foldl (fun a (_, e) => collectMvarIds e a) a
  | .fieldAccess e _ _ => collectMvarIds e acc
  | .inject _ args rty =>
    args.foldl (fun a e => collectMvarIds e a) acc |> collectMvarIds rty
  | .if_ c t el => collectMvarIds el (collectMvarIds t (collectMvarIds c acc))
  | .closure _ caps => caps.foldl (fun a e => collectMvarIds e a) acc
  | .array es ety => es.foldl (fun a e => collectMvarIds e a) acc |> collectMvarIds ety
  | .tuple es => es.foldl (fun a e => collectMvarIds e a) acc
  | .rowExtend l f t => collectMvarIds t (collectMvarIds f (collectMvarIds l acc))
  | .recordTy r => collectMvarIds r acc
  | .variantTy r => collectMvarIds r acc
  | .dataTy _ ps => ps.foldl (fun a e => collectMvarIds e a) acc
  | .eqTy _ t l r => collectMvarIds r (collectMvarIds l (collectMvarIds t acc))
  | .refl t x => collectMvarIds x (collectMvarIds t acc)
  | .transport _ t m l r ep b =>
    collectMvarIds b (collectMvarIds ep (collectMvarIds r (collectMvarIds l
      (collectMvarIds m (collectMvarIds t acc)))))
  | .ann x t => collectMvarIds t (collectMvarIds x acc)

/-- Apply a metavariable substitution map to an expression -/
partial def applyMvarSubst (e : Expr) (subst : Std.HashMap MetaId Expr) (depth : Nat := 0) : Expr :=
  match e with
  | .mvar id => subst.getD id e
  | .bvar _ | .sort _ | .primTy _ | .rowSort | .labelSort
  | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .lit _ => e
  | .fvar id ty => .fvar id (applyMvarSubst ty subst depth)
  | .const name ty => .const name (applyMvarSubst ty subst depth)
  | .app fn arg => .app (applyMvarSubst fn subst depth) (applyMvarSubst arg subst depth)
  | .lam info name dom body =>
    .lam info name (applyMvarSubst dom subst depth) (applyMvarSubst body subst (depth + 1))
  | .let_ name ty val body =>
    .let_ name (applyMvarSubst ty subst depth) (applyMvarSubst val subst depth) (applyMvarSubst body subst (depth + 1))
  | .pi qty info name dom cod =>
    .pi qty info name (applyMvarSubst dom subst depth) (applyMvarSubst cod subst (depth + 1))
  | .sigma qty info name fst snd =>
    .sigma qty info name (applyMvarSubst fst subst depth) (applyMvarSubst snd subst (depth + 1))
  | .pair fst snd => .pair (applyMvarSubst fst subst depth) (applyMvarSubst snd subst depth)
  | .projFst x => .projFst (applyMvarSubst x subst depth)
  | .projSnd x => .projSnd (applyMvarSubst x subst depth)
  | .construct name tag args rty =>
    .construct name tag (args.map (applyMvarSubst · subst depth)) (applyMvarSubst rty subst depth)
  | .«case» scruts arms rty =>
    .«case» (scruts.map (applyMvarSubst · subst depth))
      (arms.map fun arm =>
        let binds := arm.patterns.foldl (fun acc p => acc + p.bindingCount) 0
        Arm.mk arm.patterns (applyMvarSubst arm.body subst (depth + binds)))
      (applyMvarSubst rty subst depth)
  | .record fields => .record (fields.map fun (n, e) => (n, applyMvarSubst e subst depth))
  | .recordUpdate base updates =>
    .recordUpdate (applyMvarSubst base subst depth)
      (updates.map fun (n, e) => (n, applyMvarSubst e subst depth))
  | .fieldAccess x field idx => .fieldAccess (applyMvarSubst x subst depth) field idx
  | .inject l args rty =>
    .inject l (args.map (applyMvarSubst · subst depth)) (applyMvarSubst rty subst depth)
  | .if_ c t el =>
    .if_ (applyMvarSubst c subst depth) (applyMvarSubst t subst depth) (applyMvarSubst el subst depth)
  | .closure n caps => .closure n (caps.map (applyMvarSubst · subst depth))
  | .array es ety =>
    .array (es.map (applyMvarSubst · subst depth)) (applyMvarSubst ety subst depth)
  | .tuple es => .tuple (es.map (applyMvarSubst · subst depth))
  | .rowExtend l f t =>
    .rowExtend (applyMvarSubst l subst depth) (applyMvarSubst f subst depth) (applyMvarSubst t subst depth)
  | .recordTy r => .recordTy (applyMvarSubst r subst depth)
  | .variantTy r => .variantTy (applyMvarSubst r subst depth)
  | .dataTy id ps => .dataTy id (ps.map (applyMvarSubst · subst depth))
  | .eqTy lv t l r =>
    .eqTy lv (applyMvarSubst t subst depth) (applyMvarSubst l subst depth) (applyMvarSubst r subst depth)
  | .refl t x => .refl (applyMvarSubst t subst depth) (applyMvarSubst x subst depth)
  | .transport lv t m l r ep b =>
    .transport lv (applyMvarSubst t subst depth) (applyMvarSubst m subst depth)
      (applyMvarSubst l subst depth) (applyMvarSubst r subst depth)
      (applyMvarSubst ep subst depth) (applyMvarSubst b subst depth)
  | .ann x t => .ann (applyMvarSubst x subst depth) (applyMvarSubst t subst depth)

/-- Substitute all solved metavariables in type annotations and terms -/
partial def zonkExpr (e : Expr) (depth : Nat := 0) : TCM Expr := do
  let mut result := e
  let mut seen : Std.HashSet MetaId := {}
  for _ in List.range 100 do
    let mvarIds := collectMvarIds result
    let newIds := mvarIds.fold (fun acc id => if seen.contains id then acc else acc.push id) #[]
    if newIds.isEmpty then
      return result
    let mut subst : Std.HashMap MetaId Expr := {}
    for id in newIds do
      seen := seen.insert id
      match ← TCM.lookupMeta id with
      | some info =>
        match info.solution with
        | some sol =>
          subst := subst.insert id (Soma.Core.quoteExpr ⟨depth⟩ sol)
        | none => pure ()
      | none => pure ()
    if subst.isEmpty then
      return result
    result := applyMvarSubst result subst depth
  return result

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
  | .nCase scrutinees _ _ =>
    let mut result := false
    for s in scrutinees do
      if ← hasUnsolvedMetas s then
        result := true
        break
    return result
  | _ => return false

end

mutual

partial def collectUnsolvedMetas (v : Value) (span : Span) : TCM Unit := do
  match v with
  | .vNeutral ty (.nMeta m) =>
    match ← TCM.lookupMeta m with
    | some info =>
      if info.solution.isNone && info.origin != .errorRecovery then
        TCM.addError (.unsolvedMeta info.type span #[] none)
    | none =>
      TCM.addError (.unsolvedMeta ty span #[] none)
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
      if info.solution.isNone && info.origin != .errorRecovery then
        TCM.addError (.unsolvedMeta info.type span #[] none)
    | none => pure ()
  | .nApp fn arg =>
    collectUnsolvedMetasNeutral fn span
    collectUnsolvedMetas arg span
  | .nFst pair => collectUnsolvedMetasNeutral pair span
  | .nSnd pair => collectUnsolvedMetasNeutral pair span
  | .nFieldAccess rec _ => collectUnsolvedMetasNeutral rec span
  | .nCase scrutinees _ _ =>
    for s in scrutinees do
      collectUnsolvedMetas s span
  | _ => pure ()

end

/-- Report all unsolved metavariables in a value -/
def reportUnsolvedMetas (v : Value) (span : Span) : TCM Unit := do
  collectUnsolvedMetas v span

/-- Eagerly expand all parameterized type abbreviation DataTypes in a Value -/
partial def expandAbbrevValue (v : Value) : TCM Value := do
  match v with
  | .vDataType dId params =>
    -- Check if this DataType is actually a type abbreviation
    let abbrev? ← TCM.lookupAbbrev ⟨dId⟩
    match abbrev? with
    | some abbrevInfo =>
      -- Recursively expand params first
      let params' ← params.mapM expandAbbrevValue
      if params'.length == abbrevInfo.arity then
        -- Fully applied: expand the abbreviation by applying expansion to args
        let mut result := abbrevInfo.expansion
        for arg in params' do
          match result with
          | .vLam _ body => result ← applyClosure body arg
          | .vPi _ _ _ _ cod => result ← applyClosure cod arg
          | _ => return .vDataType dId params'
        -- Recursively expand the result (abbreviations may contain other abbreviations)
        expandAbbrevValue result
      else
        -- Not fully applied: keep as DataType with expanded params
        return .vDataType dId params'
    | none =>
      -- Real DataType, not an abbreviation: expand params
      let params' ← params.mapM expandAbbrevValue
      return .vDataType dId params'
  | .vPi qty binder name dom cod =>
    let dom' ← expandAbbrevValue dom
    let cod' ← expandAbbrevClosure cod
    return .vPi qty binder name dom' cod'
  | .vLam name body =>
    let body' ← expandAbbrevClosure body
    return .vLam name body'
  | .vSigma qty name fst snd =>
    let fst' ← expandAbbrevValue fst
    let snd' ← expandAbbrevClosure snd
    return .vSigma qty name fst' snd'
  | .vPair a b =>
    let a' ← expandAbbrevValue a
    let b' ← expandAbbrevValue b
    return .vPair a' b'
  | .vNeutral ty neu =>
    let ty' ← expandAbbrevValue ty
    return .vNeutral ty' neu
  | .vRecord row =>
    let row' ← expandAbbrevValue row
    return .vRecord row'
  | .vVariant row =>
    let row' ← expandAbbrevValue row
    return .vVariant row'
  | .vRowExtend label fieldTy tail =>
    let label' ← expandAbbrevValue label
    let fieldTy' ← expandAbbrevValue fieldTy
    let tail' ← expandAbbrevValue tail
    return .vRowExtend label' fieldTy' tail'
  | .vRecordVal fields =>
    let fields' ← fields.mapM fun (name, val) => do
      let val' ← expandAbbrevValue val
      return (name, val')
    return .vRecordVal fields'
  | .vConstructor name tag args rty =>
    let args' ← args.mapM expandAbbrevValue
    let rty' ← expandAbbrevValue rty
    return .vConstructor name tag args' rty'
  | .vEq l ty lhs rhs =>
    let ty' ← expandAbbrevValue ty
    let lhs' ← expandAbbrevValue lhs
    let rhs' ← expandAbbrevValue rhs
    return .vEq l ty' lhs' rhs'
  | _ => return v
where
  /-- Expand abbreviations inside a closure -/
  expandAbbrevClosure (clos : Closure) : TCM Closure := do
    match clos with
    | .const name val =>
      let val' ← expandAbbrevValue val
      return .const name val'
    | .term name env body =>
      let values' ← env.values.mapM fun (n, v) => do
        let v' ← expandAbbrevValue v
        return (n, v')
      return .term name (Env.mk values' env.size) body

end Soma.Dependent
