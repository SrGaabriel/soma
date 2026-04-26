import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.Quote
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Error

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

/-- Collect all metavariable IDs in a value -/
partial def collectMetas (v : Value) : Array MetaId :=
  match v with
  | .vType _ => #[]
  | .vPi _ _ _ dom cod =>
    collectMetas dom ++ collectMetasClosure cod
  | .vLam _ body =>
    collectMetasClosure body
  | .vSigma _ _ fst snd =>
    collectMetas fst ++ collectMetasClosure snd
  | .vPair a b => collectMetas a ++ collectMetas b
  | .vNeutral ty neu => collectMetas ty ++ collectMetasNeutral neu
  | .vPrimTy _ => #[]
  | .vIntLit _ => #[]
  | .vFloatLit _ => #[]
  | .vStringLit _ => #[]
  | .vRowEmpty => #[]
  | .vRowExtend label ty tail =>
    collectMetas label ++ collectMetas ty ++ collectMetas tail
  | .vRecord row => collectMetas row
  | .vVariant row => collectMetas row
  | .vLabelLit _ => #[]
  | .vRowSort | .vLabelSort => #[]
  | .vRecordVal fields =>
    fields.foldl (fun acc (_, v) => acc ++ collectMetas v) #[]
  | .vDataType _ params =>
    params.foldl (fun acc p => acc ++ collectMetas p) #[]
  | .vConstructor _ _ args _ =>
    args.foldl (fun acc a => acc ++ collectMetas a) #[]
  | .vEq _ ty lhs rhs =>
    collectMetas ty ++ collectMetas lhs ++ collectMetas rhs
  | .vRefl ty x =>
    collectMetas ty ++ collectMetas x
  | .vTransport _ ty motive lhs rhs eq body =>
    collectMetas ty ++ collectMetas motive ++ collectMetas lhs ++
    collectMetas rhs ++ collectMetas eq ++ collectMetas body

partial def collectMetasNeutral (n : Neutral) : Array MetaId :=
  collectMetasHead n.head ++
    n.spine.foldl (fun acc e => acc ++ collectMetasElim e) #[]

partial def collectMetasHead : Head → Array MetaId
  | .hVar _ => #[]
  | .hConst _ _ => #[]
  | .hMeta id => #[id]
  | .hErrored => #[]
  | .hCase scrutinees motive arms =>
    scrutinees.foldl (fun acc s => acc ++ collectMetas s) #[] ++
    collectMetas motive ++
    arms.foldl (fun acc arm => acc ++ collectMetasClosure arm.closure) #[]

partial def collectMetasElim : Elim → Array MetaId
  | .eApp arg => collectMetas arg
  | .eFst | .eSnd | .eField _ => #[]

partial def collectMetasClosure (clos : Closure) : Array MetaId :=
  match clos with
  | .const _ value => collectMetas value
  | .term _ env body =>
    let envMetas := env.values.foldl (fun acc (_, v) => acc ++ collectMetas v) #[]
    let bodyMetas := collectExprMetas body
    envMetas ++ bodyMetas

/-- Collect metavariable IDs from a Core Expr -/
partial def collectExprMetas : Soma.Core.Expr → Array MetaId
  | .mvar mid => #[mid]
  | .app f a => collectExprMetas f ++ collectExprMetas a
  | .lam _ _ d b => collectExprMetas d ++ collectExprMetas b
  | .let_ _ t v b => collectExprMetas t ++ collectExprMetas v ++ collectExprMetas b
  | .pi _ _ _ d c => collectExprMetas d ++ collectExprMetas c
  | .sigma _ _ _ f s => collectExprMetas f ++ collectExprMetas s
  | .pair f s => collectExprMetas f ++ collectExprMetas s
  | .projFst e | .projSnd e => collectExprMetas e
  | .fvar _ t | .const _ t | .ann _ t => collectExprMetas t
  | _ => #[]

end

/-- Collect metas from a constraint -/
def collectMetasConstraint (c : Constraint) : Array MetaId :=
  match c with
  | .unify v1 v2 _ => (collectMetas v1 ++ collectMetas v2).toList.eraseDups.toArray
  | .subtype v1 v2 _ => (collectMetas v1 ++ collectMetas v2).toList.eraseDups.toArray
  | .levelEq _ _ => #[]
  | .levelLe _ _ => #[]
  | .resolveInstance metaId _ args _ =>
    (#[metaId] ++ args.foldl (fun acc v => acc ++ collectMetas v) #[]).toList.eraseDups.toArray
  | .deferredInstance metaId domTy _ =>
    (#[metaId] ++ collectMetas domTy).toList.eraseDups.toArray

mutual

/-- Structural occurs check -/
partial def occursIn (m : MetaId) (v : Value) : Bool :=
  match v with
  | .vType _ => false
  | .vPi _ _ _ dom cod =>
    occursIn m dom || occursInClosure m cod
  | .vLam _ body =>
    occursInClosure m body
  | .vSigma _ _ fst snd =>
    occursIn m fst || occursInClosure m snd
  | .vPair a b => occursIn m a || occursIn m b
  | .vNeutral _ neu => occursInNeutral m neu
  | .vPrimTy _ => false
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
  | .vEq _ ty lhs rhs =>
    occursIn m ty || occursIn m lhs || occursIn m rhs
  | .vRefl ty x =>
    occursIn m ty || occursIn m x
  | .vTransport _ ty motive lhs rhs eq body =>
    occursIn m ty || occursIn m motive || occursIn m lhs ||
    occursIn m rhs || occursIn m eq || occursIn m body

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
  | .eFst | .eSnd | .eField _ => false

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
    | .sigma _ _ _ fst snd => occursInExpr m fst || occursInExpr m snd
    | .pair a b => occursInExpr m a || occursInExpr m b
    | .projFst e => occursInExpr m e
    | .projSnd e => occursInExpr m e
    | .if_ c t e => occursInExpr m c || occursInExpr m t || occursInExpr m e
    | .«case» scruts motive arms =>
        scruts.any (occursInExpr m) || occursInExpr m motive ||
        arms.any fun arm => occursInExpr m arm.body
    | .eqTy _ ty l r => occursInExpr m ty || occursInExpr m l || occursInExpr m r
    | .refl ty x => occursInExpr m ty || occursInExpr m x
    | .transport _ ty mot l r eq b =>
        occursInExpr m ty || occursInExpr m mot || occursInExpr m l ||
        occursInExpr m r || occursInExpr m eq || occursInExpr m b
    | .rowExtend l t tail => occursInExpr m l || occursInExpr m t || occursInExpr m tail
    | .recordTy r => occursInExpr m r
    | .variantTy r => occursInExpr m r
    | .record fields => fields.any fun (_, e) => occursInExpr m e
    | .recordUpdate b us => occursInExpr m b || us.any fun (_, e) => occursInExpr m e
    | .fieldAccess e _ _ => occursInExpr m e
    | .construct _ _ args _ => args.any (occursInExpr m)
    | .inject _ args _ => args.any (occursInExpr m)
    | .closure _ caps => caps.any (occursInExpr m)
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
  | .vSigma _ _ fst snd =>
    inScope allowedLevels fst && inScopeClosure allowedLevels snd
  | .vPair a b => inScope allowedLevels a && inScope allowedLevels b
  | .vNeutral _ neu => inScopeNeutral allowedLevels neu
  | .vPrimTy _ => true
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
  | .vEq _ ty lhs rhs =>
    inScope allowedLevels ty && inScope allowedLevels lhs && inScope allowedLevels rhs
  | .vRefl ty x =>
    inScope allowedLevels ty && inScope allowedLevels x
  | .vTransport _ ty motive lhs rhs eq body =>
    inScope allowedLevels ty && inScope allowedLevels motive &&
    inScope allowedLevels lhs && inScope allowedLevels rhs &&
    inScope allowedLevels eq && inScope allowedLevels body

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
  | .eFst | .eSnd | .eField _ => true

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
  | .vSigma _ _ fst snd =>
    collectFreeVars fst ++ collectFreeVarsClosure snd
  | .vPair a b => collectFreeVars a ++ collectFreeVars b
  | .vNeutral _ neu => collectFreeVarsNeutral neu
  | .vPrimTy _ => #[]
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
  | .vEq _ ty lhs rhs =>
    collectFreeVars ty ++ collectFreeVars lhs ++ collectFreeVars rhs
  | .vRefl ty x =>
    collectFreeVars ty ++ collectFreeVars x
  | .vTransport _ ty motive lhs rhs eq body =>
    collectFreeVars ty ++ collectFreeVars motive ++ collectFreeVars lhs ++
    collectFreeVars rhs ++ collectFreeVars eq ++ collectFreeVars body

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
  | .eFst | .eSnd | .eField _ => #[]

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

/-- Eta-expand a value to a pair -/
def etaExpandPairValue (v : Value) : Value × Value :=
  match v with
  | .vPair a b => (a, b)
  | .vNeutral ty neu =>
    (Value.vNeutral ty (.nFst neu), Value.vNeutral ty (.nSnd neu))
  | _ => (v, v)  -- Shouldn't happen in well-typed code

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
  | .vSigma _ _ _ _ => "vSigma"
  | .vPair _ _ => "vPair"
  | .vNeutral _ n => s!"vNeutral({getNeutralKind n})"
  | .vPrimTy p => s!"vPrimTy({p})"
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
  | .vEq _ _ _ _ => "vEq"
  | .vRefl _ _ => "vRefl"
  | .vTransport _ _ _ _ _ _ _ => "vTransport"
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
      | .eFst => "fst"
      | .eSnd => "snd"
      | .eField f => s!"field({f})")
    if elimsStr.isEmpty then headKind else s!"{headKind}[{elimsStr}]"

def throwUnifyError (v1 v2 : Value) (_msg : String := "") : TCM Unit := do
  let span ← TCM.getSpan
  let failure := UnifyFailure.headMismatch v1 v2
  TCM.throw (.unificationFailed failure .general span #[] #[])

/-- Throw a unification error with constraint chain context -/
def throwUnifyErrorWithContext (v1 v2 : Value) (chain : Array ConstraintInfo)
    (metas : Array MetaId) (purpose : CheckPurpose := .general) : TCM Unit := do
  let span ← TCM.getSpan
  let failure := UnifyFailure.headMismatch v1 v2
  TCM.throw (.unificationFailed failure purpose span chain metas)

end Soma.Dependent
