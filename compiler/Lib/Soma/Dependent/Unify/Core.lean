import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.Quote
import Soma.Core.Pp
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Error
import Soma.Dependent.Zonk

open Soma.Syntax (Span)

namespace Soma.Dependent

open Soma.Core

/-- A spine is the sequence of argument eliminators applied to a head -/
structure Spine where
  args : List Value
  deriving Inhabited

/-- Extract a pattern spine (list of argument values) from a neutral -/
def getSpine (neu : Neutral) : Option Spine := Id.run do
  let mut args : List Value := []
  for e in neu.spine do
    match e with
    | .eApp arg => args := args ++ [arg]
    | _ => return none
  return some ⟨args⟩

/-- Check if a value is a bound variable at a specific level (no spine) -/
def asBoundVar : Value → Option DeBruijnLvl
  | .vNeutral _ neu =>
    if neu.isBareHead then
      match neu.head with
      | .hVar v => some v.level
      | _ => none
    else none
  | _ => none

/-- Check if all values in the spine are distinct bound variables -/
def spineIsPattern (spine : Spine) : Option (List DeBruijnLvl) := do
  let mut levels : List DeBruijnLvl := []
  for arg in spine.args do
    let lvl ← asBoundVar arg
    if levels.contains lvl then
      none  -- Duplicate variable - not a pattern
    else
      levels := levels ++ [lvl]
  return levels

mutual

/-- Structural occurs check -/
partial def occursIn (m : MetaId) (v : Value) : Bool :=
  match v with
  | .vType _ => false
  | .vPi _ _ _ dom cod =>
    occursIn m dom || occursInClosure m cod
  | .vLam _ body =>
    occursInClosure m body
  | .vNeutral _ neu => occursInNeutral m neu
  | .vIntLit _ => false
  | .vFloatLit _ => false
  | .vStringLit _ => false
  | .vRowEmpty => false
  | .vRowExtend label ty tail =>
    occursIn m label || occursIn m ty || occursIn m tail
  | .vRecord row => occursIn m row
  | .vVariant row => occursIn m row
  | .vLabelLit _ => false
  | .vRowSort | .vLabelSort => false
  | .vRecordVal fields =>
    fields.any (fun (_, v) => occursIn m v)
  | .vDataType _ params =>
    params.any (occursIn m)
  | .vConstructor _ _ args _ =>
    args.any (occursIn m)

partial def occursInNeutral (m : MetaId) (n : Neutral) : Bool :=
  occursInHead m n.head || n.spine.any (occursInElim m)

partial def occursInHead (m : MetaId) : Head → Bool
  | .hVar _ => false
  | .hConst _ _ => false
  | .hMeta id => id == m
  | .hErrored => false
  | .hCase scrutinees motive arms =>
    scrutinees.any (occursIn m) || occursIn m motive ||
    arms.any (fun arm => occursInClosure m arm.closure)

partial def occursInElim (m : MetaId) : Elim → Bool
  | .eApp arg => occursIn m arg
  | .eField _ => false

partial def occursInClosure (m : MetaId) (clos : Closure) : Bool :=
  match clos with
  | .const _ value =>
    -- HOAS-style closure: check if metavariable occurs in the stored value
    occursIn m value
  | .term _ env body =>
    -- Term-based closure: check environment and body
    let envOccurs := env.values.any fun (_, v) => occursIn m v
    envOccurs || occursInExpr m body
where
  /-- Check if a metavariable occurs in a Core.Expr -/
  occursInExpr (m : MetaId) : Soma.Core.Expr → Bool
    | .mvar id => id == m
    | .app fn arg => occursInExpr m fn || occursInExpr m arg
    | .lam _ _ dom body => occursInExpr m dom || occursInExpr m body
    | .let_ _ ty val body => occursInExpr m ty || occursInExpr m val || occursInExpr m body
    | .pi _ _ _ dom cod => occursInExpr m dom || occursInExpr m cod
    | .if_ c t e => occursInExpr m c || occursInExpr m t || occursInExpr m e
    | .«case» scruts motive arms =>
        scruts.any (occursInExpr m) || occursInExpr m motive ||
        arms.any fun arm => occursInExpr m arm.body
    | .rowExtend l t tail => occursInExpr m l || occursInExpr m t || occursInExpr m tail
    | .recordTy r => occursInExpr m r
    | .variantTy r => occursInExpr m r
    | .record fields => fields.any fun (_, e) => occursInExpr m e
    | .recordUpdate b us => occursInExpr m b || us.any fun (_, e) => occursInExpr m e
    | .fieldAccess e _ _ => occursInExpr m e
    | .construct _ _ args _ => args.any (occursInExpr m)
    | .inject _ args _ => args.any (occursInExpr m)
    | .closure _ caps ty => caps.any (occursInExpr m) || occursInExpr m ty
    | .array es _ => es.any (occursInExpr m)
    | .tuple es => es.any (occursInExpr m)
    | .dataTy _ ps => ps.any (occursInExpr m)
    | .ann x t => occursInExpr m x || occursInExpr m t
    | _ => false

end

mutual

/-- Check if a value only references variables within the given scope (levels) -/
partial def inScope (allowedLevels : List DeBruijnLvl) (v : Value) : Bool :=
  match v with
  | .vType _ => true
  | .vPi _ _ _ dom cod =>
    inScope allowedLevels dom && inScopeClosure allowedLevels cod
  | .vLam _ body =>
    inScopeClosure allowedLevels body
  | .vNeutral _ neu => inScopeNeutral allowedLevels neu
  | .vIntLit _ => true
  | .vFloatLit _ => true
  | .vStringLit _ => true
  | .vRowEmpty => true
  | .vRowExtend label ty tail =>
    inScope allowedLevels label && inScope allowedLevels ty && inScope allowedLevels tail
  | .vRecord row => inScope allowedLevels row
  | .vVariant row => inScope allowedLevels row
  | .vLabelLit _ => true
  | .vRowSort | .vLabelSort => true
  | .vRecordVal fields =>
    fields.all (fun (_, v) => inScope allowedLevels v)
  | .vDataType _ params =>
    params.all (inScope allowedLevels)
  | .vConstructor _ _ args _ =>
    args.all (inScope allowedLevels)

partial def inScopeNeutral (allowedLevels : List DeBruijnLvl) (n : Neutral) : Bool :=
  inScopeHead allowedLevels n.head && n.spine.all (inScopeElim allowedLevels)

partial def inScopeHead (allowedLevels : List DeBruijnLvl) : Head → Bool
  | .hVar v => allowedLevels.contains v.level
  | .hConst _ _ => true
  | .hMeta _ => true
  | .hErrored => true
  | .hCase scrutinees motive _ =>
    scrutinees.all (inScope allowedLevels) && inScope allowedLevels motive

partial def inScopeElim (allowedLevels : List DeBruijnLvl) : Elim → Bool
  | .eApp arg => inScope allowedLevels arg
  | .eField _ => true

partial def inScopeClosure (allowedLevels : List DeBruijnLvl) (clos : Closure) : Bool :=
  match clos with
  | .const _ val => inScope allowedLevels val
  | .term _ env _ => env.values.all fun (_, v) => inScope allowedLevels v

end

mutual

/-- Collect all free variables (by level) that appear in a value -/
partial def collectFreeVars (v : Value) : Array DeBruijnLvl :=
  match v with
  | .vType _ => #[]
  | .vPi _ _ _ dom cod =>
    collectFreeVars dom ++ collectFreeVarsClosure cod
  | .vLam _ body =>
    collectFreeVarsClosure body
  | .vNeutral _ neu => collectFreeVarsNeutral neu
  | .vIntLit _ => #[]
  | .vFloatLit _ => #[]
  | .vStringLit _ => #[]
  | .vRowEmpty => #[]
  | .vRowExtend label ty tail =>
    collectFreeVars label ++ collectFreeVars ty ++ collectFreeVars tail
  | .vRecord row => collectFreeVars row
  | .vVariant row => collectFreeVars row
  | .vLabelLit _ => #[]
  | .vRowSort | .vLabelSort => #[]
  | .vRecordVal fields =>
    fields.foldl (fun acc (_, v) => acc ++ collectFreeVars v) #[]
  | .vDataType _ params =>
    params.foldl (fun acc p => acc ++ collectFreeVars p) #[]
  | .vConstructor _ _ args _ =>
    args.foldl (fun acc a => acc ++ collectFreeVars a) #[]

partial def collectFreeVarsNeutral (n : Neutral) : Array DeBruijnLvl :=
  collectFreeVarsHead n.head ++
    n.spine.foldl (fun acc e => acc ++ collectFreeVarsElim e) #[]

partial def collectFreeVarsHead : Head → Array DeBruijnLvl
  | .hVar v => #[v.level]
  | .hConst _ _ => #[]
  | .hMeta _ => #[]
  | .hErrored => #[]
  | .hCase scrutinees motive arms =>
    scrutinees.foldl (fun acc s => acc ++ collectFreeVars s) #[] ++
    collectFreeVars motive ++
    arms.foldl (fun acc arm => acc ++ collectFreeVarsClosure arm.closure) #[]

partial def collectFreeVarsElim : Elim → Array DeBruijnLvl
  | .eApp arg => collectFreeVars arg
  | .eField _ => #[]

partial def collectFreeVarsClosure (clos : Closure) : Array DeBruijnLvl :=
  match clos with
  | .const _ value => collectFreeVars value
  | .term _ env _ =>
    env.values.foldl (fun acc (_, v) => acc ++ collectFreeVars v) #[]

end

/-- Extract metavariable and pattern spine (application args only) from a neutral -/
def getMetaWithSpine (neu : Neutral) : Option (MetaId × List Value) := Id.run do
  match neu.head with
  | .hMeta m =>
    let mut args : List Value := []
    for e in neu.spine do
      match e with
      | .eApp arg => args := args ++ [arg]
      | _ => return none
    return some (m, args)
  | _ => return none

def solveMetaProjectionSpine? (neu : Neutral) : Option (MetaId × Array Elim) :=
  match neu.head with
  | .hMeta m =>
    let hasProjection := neu.spine.any fun e =>
      match e with
      | .eApp _ => false
      | _ => true
    if hasProjection then some (m, neu.spine) else none
  | _ => none

/-- Build a neutral from a metavariable head and a spine of argument values -/
def buildMetaSpine (m : MetaId) (spine : List Value) : Neutral :=
  Neutral.mk (.hMeta m) (spine.foldl (fun acc arg => acc.push (.eApp arg)) #[])

/-- Convert a Value to a Neutral (for eta expansion) -/
def valueToNeutral (v : Value) : Neutral :=
  match v with
  | .vNeutral _ neu => neu
  | _ => .nVar ⟨"_eta", ⟨0⟩⟩

/-- Enumerate a list with indices starting from 0 -/
def enumList {α : Type} (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: rest => (i, x) :: go (i + 1) rest
  go 0 xs

/-- Check if a level appears in the spine -/
def levelInSpine (lvl : DeBruijnLvl) (spine : List Value) : Bool :=
  spine.any fun arg =>
    match asBoundVar arg with
    | some l => l == lvl
    | none => false

/-- A default span for internal use -/
def defaultSpan : Span := Span.uninhabited

/-- Throw a unification error -/
def getValueKind : Value → String
  | .vType _ => "vType"
  | .vPi _ _ _ _ _ => "vPi"
  | .vLam _ _ => "vLam"
  | .vNeutral _ n => s!"vNeutral({getNeutralKind n})"
  | .vIntLit _ => "vIntLit"
  | .vFloatLit _ => "vFloatLit"
  | .vStringLit _ => "vStringLit"
  | .vRowEmpty => "vRowEmpty"
  | .vRowExtend _ _ _ => "vRowExtend"
  | .vRecord _ => "vRecord"
  | .vVariant _ => "vVariant"
  | .vRecordVal _ => "vRecordVal"
  | .vLabelLit _ => "vLabelLit"
  | .vRowSort => "vRowSort"
  | .vLabelSort => "vLabelSort"
  | .vDataType id _ => s!"vDataType({id.original})"
  | .vConstructor n _ _ _ => s!"vConstructor({n})"
where
  getNeutralKind (n : Neutral) : String :=
    let headKind : String := match n.head with
      | .hVar v => s!"nVar({v.name})"
      | .hConst qn _ => s!"nConst({qn})"
      | .hMeta m => s!"nMeta({m.id})"
      | .hErrored => "hErrored"
      | .hCase _ _ _ => "nCase"
    let elimsStr := String.intercalate "," (n.spine.toList.map fun
      | .eApp _ => "app"
      | .eField f => s!"field({f})")
    if elimsStr.isEmpty then headKind else s!"{headKind}[{elimsStr}]"

/-- Build a `PpContext` for rendering values -/
private def diagnosticPpContext : TCM Soma.Core.PpContext := do
  let s ← TCM.getState
  let ctx ← TCM.getCtx
  let eqId := (ctx.globals.wiredIn.getUnique? .typeEq).map (·.name.id)
  return { Soma.Core.PpContext.ofMetas s.metas with eqInductiveId := eqId }

/-- Convert an `Array (MetaId × Value × String)` -/
private def renderInsertedImplicits
    (pp : Soma.Core.PpContext)
    (impls : Array (MetaId × Value × String))
    : TCM (Array Soma.Attach.InsertedImplicit) := do
  let mut out : Array Soma.Attach.InsertedImplicit := #[]
  for (mid, _ty, name) in impls do
    let info? ← TCM.lookupMeta mid
    let valueStr :=
      match info? with
      | some info =>
        match info.solution with
        | some sol => Soma.Core.Value.pp pp sol
        | none => s!"?{name}"
      | none => s!"?{name}"
    out := out.push { name, value := valueStr }
  return out

/-- Build a δ-reduction trace for a value by abbreviation -/
private partial def buildUnfoldTrace
    (pp : Soma.Core.PpContext) (v : Value)
    : TCM (Array Soma.Attach.UnfoldStep × Value) := do
  let initial : Soma.Attach.UnfoldStep :=
    { term := Soma.Core.Value.pp pp v, rule := none, stuck := false }
  let mut acc := #[initial]
  let mut cur := v
  let mut fuel := 32
  while fuel > 0 do
    fuel := fuel - 1
    match ← tryUnfoldOneStep cur with
    | some (cur', rule) =>
      let step : Soma.Attach.UnfoldStep :=
        { term := Soma.Core.Value.pp pp cur', rule := some rule, stuck := false }
      acc := acc.push step
      cur := cur'
    | none => fuel := 0
  return (acc, cur)

/-- Mark the last step in a trace as stuck -/
private def markTraceStuck (trace : Array Soma.Attach.UnfoldStep)
    : Array Soma.Attach.UnfoldStep :=
  if trace.isEmpty then trace
  else
    let last := trace.back!
    trace.set! (trace.size - 1) { last with stuck := true }

/-- Build a `headMismatch` failure from the current unify root + path -/
private def buildHeadMismatch (vLeaf1 vLeaf2 : Value) : TCM UnifyFailure := do
  let path ← TCM.getPath
  let (v1, v2) ←
    match ← TCM.getUnifyRoot with
    | some (root1, root2) => pure (root1, root2)
    | none => pure (vLeaf1, vLeaf2)
  let pp ← diagnosticPpContext
  let (trace1, v1Reduced) ← buildUnfoldTrace pp v1
  let (trace2, v2Reduced) ← buildUnfoldTrace pp v2
  let nonTrivial (t : Array Soma.Attach.UnfoldStep) : Bool := t.size > 1
  let trace : Array Soma.Attach.UnfoldStep :=
    if nonTrivial trace1 && nonTrivial trace2 then
      markTraceStuck trace1 ++ markTraceStuck trace2
    else if nonTrivial trace1 then markTraceStuck trace1
    else if nonTrivial trace2 then markTraceStuck trace2
    else #[]
  let s1 := Soma.Core.Value.pp pp v1
  let s2 := Soma.Core.Value.pp pp v2
  let rs1 := Soma.Core.Value.pp pp v1Reduced
  let rs2 := Soma.Core.Value.pp pp v2Reduced
  let reduced : Option (Value × Value) :=
    if s1 == rs1 && s2 == rs2 then none else some (v1Reduced, v2Reduced)
  let implicits : Option (String × Array Soma.Attach.InsertedImplicit) ←
    match ← TCM.getImplicits with
    | some (surface, impls) =>
      let rendered ← renderInsertedImplicits pp impls
      pure (some (surface, rendered))
    | none => pure none
  return UnifyFailure.headMismatch v1 v2 path reduced trace implicits

def throwUnifyError (v1 v2 : Value) (_msg : String := "") : TCM Unit := do
  let span ← TCM.getSpan
  let failure ← buildHeadMismatch v1 v2
  TCM.throw (.unificationFailed failure .general span #[] #[])

/-- Throw a rigid-rigid mismatch while preserving the current structural path and the roots -/
def throwRigidMismatch (n1 n2 : Neutral) : TCM Unit := do
  let span ← TCM.getSpan
  let path ← TCM.getPath
  let roots ← TCM.getUnifyRoot
  TCM.throw (.unificationFailed
    (.rigidMismatch n1 n2 path roots) .general span #[] #[])

/-- Throw a level-mismatch failure preserving path + roots -/
def throwLevelMismatch (l1 l2 : Level) : TCM Unit := do
  let span ← TCM.getSpan
  let path ← TCM.getPath
  let roots ← TCM.getUnifyRoot
  TCM.throw (.unificationFailed
    (.levelMismatch l1 l2 path roots) .general span #[] #[])

/-- Throw a row-label-not-found failure preserving path + roots -/
def throwRowLabelNotFound (label : String) (row : Value) : TCM Unit := do
  let span ← TCM.getSpan
  let path ← TCM.getPath
  let roots ← TCM.getUnifyRoot
  TCM.throw (.unificationFailed
    (.rowLabelNotFound label row path roots) .general span #[] #[])

/-- Throw a unification error with constraint chain context -/
def throwUnifyErrorWithContext (v1 v2 : Value) (chain : Array ConstraintInfo)
    (metas : Array MetaId) (purpose : CheckPurpose := .general) : TCM Unit := do
  let span ← TCM.getSpan
  let failure ← buildHeadMismatch v1 v2
  TCM.throw (.unificationFailed failure purpose span chain metas)

end Soma.Dependent
