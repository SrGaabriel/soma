import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quote
import Soma.Dependent.Monad
import Soma.Dependent.Convert

namespace Soma.Dependent

open Soma.Core
open Soma.Syntax (Span)

/-- Collect all mvar IDs from an expression -/
partial def collectMvarIds (e : Expr) (acc : Std.HashSet MetaId := {}) : Std.HashSet MetaId :=
  match e with
  | .mvar id => acc.insert id
  | .bvar _ | .sort _ | .rowSort | .labelSort
  | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .lit _ | .tyvar _ _ => acc
  | .fvar _ ty => collectMvarIds ty acc
  | .const _ ty => collectMvarIds ty acc
  | .app fn arg => collectMvarIds arg (collectMvarIds fn acc)
  | .lam _ _ dom body => collectMvarIds body (collectMvarIds dom acc)
  | .let_ _ ty val body => collectMvarIds body (collectMvarIds val (collectMvarIds ty acc))
  | .pi _ _ _ dom cod => collectMvarIds cod (collectMvarIds dom acc)
  | .construct _ _ args rty =>
    args.foldl (fun a e => collectMvarIds e a) acc |> collectMvarIds rty
  | .«case» scruts motive arms =>
    let a := scruts.foldl (fun a e => collectMvarIds e a) acc
    let a := collectMvarIds motive a
    arms.foldl (fun a arm => collectMvarIds arm.body a) a
  | .record fields => fields.foldl (fun a (_, e) => collectMvarIds e a) acc
  | .recordUpdate base updates =>
    let a := collectMvarIds base acc
    updates.foldl (fun a (_, e) => collectMvarIds e a) a
  | .fieldAccess e _ _ => collectMvarIds e acc
  | .inject _ args rty => args.foldl (fun a e => collectMvarIds e a) acc |> collectMvarIds rty
  | .if_ c t e => collectMvarIds e (collectMvarIds t (collectMvarIds c acc))
  | .closure _ caps ty =>
    collectMvarIds ty (caps.foldl (fun a e => collectMvarIds e a) acc)
  | .array es ety => es.foldl (fun a e => collectMvarIds e a) acc |> collectMvarIds ety
  | .tuple es => es.foldl (fun a e => collectMvarIds e a) acc
  | .rowExtend l f t => collectMvarIds t (collectMvarIds f (collectMvarIds l acc))
  | .recordTy r => collectMvarIds r acc
  | .variantTy r => collectMvarIds r acc
  | .dataTy _ ps => ps.foldl (fun a e => collectMvarIds e a) acc
  | .ann x t => collectMvarIds t (collectMvarIds x acc)

/-- Apply a metavariable substitution map to an expression -/
partial def applyMvarSubst (e : Expr) (subst : Std.HashMap MetaId Expr) (depth : Nat := 0) : Expr :=
  match e with
  | .mvar id => subst.getD id e
  | .bvar _ | .sort _ | .rowSort | .labelSort
  | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .lit _ | .tyvar _ _ => e
  | .fvar id ty => .fvar id (applyMvarSubst ty subst depth)
  | .const name ty => .const name (applyMvarSubst ty subst depth)
  | .app fn arg => .app (applyMvarSubst fn subst depth) (applyMvarSubst arg subst depth)
  | .lam info name dom body =>
    .lam info name (applyMvarSubst dom subst depth) (applyMvarSubst body subst (depth + 1))
  | .let_ name ty val body =>
    .let_ name (applyMvarSubst ty subst depth) (applyMvarSubst val subst depth) (applyMvarSubst body subst (depth + 1))
  | .pi qty info name dom cod =>
    .pi qty info name (applyMvarSubst dom subst depth) (applyMvarSubst cod subst (depth + 1))
  | .construct name tag args rty =>
    .construct name tag (args.map (applyMvarSubst · subst depth)) (applyMvarSubst rty subst depth)
  | .«case» scruts motive arms =>
    .«case» (scruts.map (applyMvarSubst · subst depth))
      (applyMvarSubst motive subst depth)
      (arms.map fun arm =>
        let binds := arm.patterns.foldl (fun acc p => acc + p.bindingCount) 0
        Arm.mk arm.patterns (applyMvarSubst arm.body subst (depth + binds)))
  | .record fields => .record (fields.map fun (n, e) => (n, applyMvarSubst e subst depth))
  | .recordUpdate base updates =>
    .recordUpdate (applyMvarSubst base subst depth)
      (updates.map fun (n, e) => (n, applyMvarSubst e subst depth))
  | .fieldAccess x field idx => .fieldAccess (applyMvarSubst x subst depth) field idx
  | .inject l args rty =>
    .inject l (args.map (applyMvarSubst · subst depth)) (applyMvarSubst rty subst depth)
  | .if_ c t el =>
    .if_ (applyMvarSubst c subst depth) (applyMvarSubst t subst depth) (applyMvarSubst el subst depth)
  | .closure n caps ty =>
    .closure n (caps.map (applyMvarSubst · subst depth)) (applyMvarSubst ty subst depth)
  | .array es ety =>
    .array (es.map (applyMvarSubst · subst depth)) (applyMvarSubst ety subst depth)
  | .tuple es => .tuple (es.map (applyMvarSubst · subst depth))
  | .rowExtend l f t =>
    .rowExtend (applyMvarSubst l subst depth) (applyMvarSubst f subst depth) (applyMvarSubst t subst depth)
  | .recordTy r => .recordTy (applyMvarSubst r subst depth)
  | .variantTy r => .variantTy (applyMvarSubst r subst depth)
  | .dataTy id ps => .dataTy id (ps.map (applyMvarSubst · subst depth))
  | .ann x t => .ann (applyMvarSubst x subst depth) (applyMvarSubst t subst depth)

/-- Substitute all solved metavariables in an expression -/
partial def zonkExpr (e : Expr) (depth : Nat := 0) : TCM Expr :=
  loop e {}
where
  loop (result : Expr) (processed : Std.HashSet MetaId) : TCM Expr := do
    let mvarIds := collectMvarIds result
    let mut newIds : Array MetaId := #[]
    for id in mvarIds do
      if !processed.contains id then newIds := newIds.push id
    if newIds.isEmpty then return result
    let mut processed' := processed
    let mut subst : Std.HashMap MetaId Expr := {}
    for id in newIds do
      processed' := processed'.insert id
      match ← TCM.lookupMeta id with
      | none => pure ()
      | some info =>
        match info.solution with
        | none => pure ()
        | some sol =>
          subst := subst.insert id (Soma.Core.quoteExpr ⟨depth⟩ sol)
    if subst.isEmpty then return result
    loop (applyMvarSubst result subst depth) processed'

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

  | .vLam name dom body =>
    let dom' ← zonkValue dom
    let body' ← zonkClosure body
    return .vLam name dom' body'

  | .vNeutral _ _ =>
    let forced ← force v
    match forced with
    | .vNeutral ty' neu' =>
      let ty'' ← zonkValue ty'
      let neu'' ← zonkNeutral neu'
      return .vNeutral ty'' neu''
    | other => zonkValue other

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

/-- Zonk a neutral head -/
partial def zonkHead (h : Head) : TCM Head := do
  match h with
  | .hVar v => return .hVar v
  | .hMeta m => return .hMeta m
  | .hErrored => return .hErrored
  | .hConst qn ty =>
    let ty' ← zonkValue ty
    return .hConst qn ty'
  | .hCase scrutinees motive arms =>
    let scrutinees' ← scrutinees.mapM zonkValue
    let motive' ← zonkValue motive
    let arms' ← arms.mapM fun arm => do
      let clos' ← zonkClosure arm.closure
      return ArmClosure.mk arm.pattern clos'
    return .hCase scrutinees' motive' arms'

/-- Zonk a spine eliminator by walking its subvalues -/
partial def zonkElim (e : Elim) : TCM Elim := do
  match e with
  | .eApp arg =>
    let arg' ← zonkValue arg
    return .eApp arg'
  | .eField name => return .eField name

/-- Zonk a neutral term -/
partial def zonkNeutral (n : Neutral) : TCM Neutral := do
  let head' ← zonkHead n.head
  let spine' ← n.spine.mapM zonkElim
  return .mk head' spine'

/-- Zonk a closure -/
partial def zonkClosure (clos : Closure) : TCM Closure := do
  match clos with
  | .const name value =>
    -- For HOAS closures, zonk the stored value
    let value' ← zonkValue value
    return Closure.const name value'
  | .term name env body =>
    -- For term closures, zonk both captured values
    let env' ← zonkEnv env
    let body' ← zonkExpr body env.size
    return Closure.term name env' body'

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
  | .vLam _ dom _ => hasUnsolvedMetas dom
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
  | _ => return false

partial def hasUnsolvedMetasNeutral (n : Neutral) : TCM Bool := do
  if ← hasUnsolvedMetasHead n.head then return true
  for e in n.spine do
    if ← hasUnsolvedMetasElim e then return true
  return false

partial def hasUnsolvedMetasHead (h : Head) : TCM Bool := do
  match h with
  | .hMeta m =>
    match ← TCM.lookupMeta m with
    | some info => return info.solution.isNone
    | none => return true
  | .hVar _ => return false
  | .hConst _ _ => return false
  | .hErrored => return false
  | .hCase scrutinees motive _ =>
    for s in scrutinees do
      if ← hasUnsolvedMetas s then
        return true
    hasUnsolvedMetas motive

partial def hasUnsolvedMetasElim (e : Elim) : TCM Bool := do
  match e with
  | .eApp arg => hasUnsolvedMetas arg
  | .eField _ => return false

end

mutual

partial def gatherUnsolvedMetaIds (v : Value)
    (acc : Std.HashSet Nat) : TCM (Std.HashSet Nat) := do
  match v with
  | .vPi _ _ _ dom _ => gatherUnsolvedMetaIds dom acc
  | .vLam _ dom _ => gatherUnsolvedMetaIds dom acc
  | .vNeutral ty neu =>
    let acc ← gatherUnsolvedMetaIds ty acc
    gatherUnsolvedMetaIdsNeutral neu acc
  | .vRowExtend label ty tail =>
    let acc ← gatherUnsolvedMetaIds label acc
    let acc ← gatherUnsolvedMetaIds ty acc
    gatherUnsolvedMetaIds tail acc
  | .vRecord row => gatherUnsolvedMetaIds row acc
  | .vVariant row => gatherUnsolvedMetaIds row acc
  | .vRecordVal fields =>
    fields.foldlM (init := acc) fun a (_, val) => gatherUnsolvedMetaIds val a
  | .vDataType _ params =>
    params.foldlM (init := acc) fun a p => gatherUnsolvedMetaIds p a
  | .vConstructor _ _ args _ =>
    args.foldlM (init := acc) fun a v => gatherUnsolvedMetaIds v a
  | _ => return acc

partial def gatherUnsolvedMetaIdsNeutral (n : Neutral)
    (acc : Std.HashSet Nat) : TCM (Std.HashSet Nat) := do
  let acc ← gatherUnsolvedMetaIdsHead n.head acc
  n.spine.foldlM (init := acc) fun a e => gatherUnsolvedMetaIdsElim e a

partial def gatherUnsolvedMetaIdsHead (h : Head)
    (acc : Std.HashSet Nat) : TCM (Std.HashSet Nat) := do
  match h with
  | .hMeta m =>
    if acc.contains m.id then return acc
    match ← TCM.lookupMeta m with
    | some info =>
      if info.solution.isNone && info.origin != .errorRecovery then
        return acc.insert m.id
      else return acc
    | none => return acc
  | .hVar _ | .hConst _ _ | .hErrored => return acc
  | .hCase scrutinees motive _ =>
    let acc ← scrutinees.foldlM (init := acc) fun a s => gatherUnsolvedMetaIds s a
    gatherUnsolvedMetaIds motive acc

partial def gatherUnsolvedMetaIdsElim (e : Elim)
    (acc : Std.HashSet Nat) : TCM (Std.HashSet Nat) := do
  match e with
  | .eApp arg => gatherUnsolvedMetaIds arg acc
  | .eField _ => return acc

end

/-- Collect every postponed `TrackedConstraint` that references the given meta -/
private def relatedConstraintsFor (metaId : MetaId) : TCM (Array MetaConstraintInfo) := do
  let state ← TCM.getState
  let mut out : Array MetaConstraintInfo := #[]
  for tracked in state.postponed do
    if tracked.metas.any (· == metaId) then
      out := out.push {
        description := tracked.constraint.describe
        origin := tracked.origin
        isBlocked := true
      }
  return out

/-- Report every unique unsolved metavariable reachable from `v` -/
def reportUnsolvedMetas (v : Value) (span : Span) : TCM Unit := do
  let ids ← gatherUnsolvedMetaIds v {}
  for id in ids do
    match ← TCM.lookupMeta ⟨id⟩ with
    | some info =>
      let ctx := info.context.map fun (n, t, _) => (n, t)
      let related ← relatedConstraintsFor ⟨id⟩
      TCM.addError (.unsolvedMeta info.type span related none ctx)
    | none => pure ()

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
          | .vLam _ _ body => result ← applyClosure body arg
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
  | .vLam name dom body =>
    let dom' ← expandAbbrevValue dom
    let body' ← expandAbbrevClosure body
    return .vLam name dom' body'
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

namespace Zonk

/-- Zonk every value in a `localTypes` map (the by-byte-offset binder-type cache feeding LSP hover) -/
def zonkLocalTypes (m : Std.HashMap Nat Soma.Core.Value)
    : TCM (Std.HashMap Nat Soma.Core.Value) := do
  let mut out : Std.HashMap Nat Soma.Core.Value := {}
  for (k, v) in m.toList do
    let zv ← zonkValue v
    out := out.insert k zv
  return out

end Zonk

/-- Zonk the current TCM state's `localTypes` in place -/
def zonkLocalTypesInPlace : TCM Unit := do
  let st ← TCM.getState
  let zonked ← Zonk.zonkLocalTypes st.localTypes
  TCM.modifyState fun s => { s with localTypes := zonked }

end Soma.Dependent
