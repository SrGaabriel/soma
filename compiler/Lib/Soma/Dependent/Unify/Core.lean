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

/-- A spine is the sequence of eliminations applied to a head -/
structure Spine where
  args : List Value
  deriving Inhabited

/-- Extract the spine from a neutral value (if it's just applications) -/
def getSpine : Neutral → Option Spine
  | .nVar _ => some ⟨[]⟩
  | .nMeta _ => some ⟨[]⟩
  | .nApp fn arg =>
    match getSpine fn with
    | some spine => some ⟨spine.args ++ [arg]⟩
    | none => none
  | _ => none -- Projections, field access, case not part of pattern spine

/-- Check if a value is a bound variable at a specific level -/
def asBoundVar : Value → Option DeBruijnLvl
  | .vNeutral _ (.nVar v) => some v.level
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
  | .vLam _ _ _ dom body =>
    collectMetas dom ++ collectMetasClosure body
  | .vSigma _ _ fst snd =>
    collectMetas fst ++ collectMetasClosure snd
  | .vPair a b => collectMetas a ++ collectMetas b
  | .vNeutral ty neu => collectMetas ty ++ collectMetasNeutral neu
  | .vPrimTy _ => #[]
  | .vHigherPrim _ => #[]
  | .vIntLit _ => #[]
  | .vStringLit _ => #[]
  | .vRowEmpty => #[]
  | .vRowExtend label ty tail =>
    collectMetas label ++ collectMetas ty ++ collectMetas tail
  | .vRecord row => collectMetas row
  | .vVariant row => collectMetas row
  | .vLabelLit _ => #[]
  | .vRecordVal fields =>
    fields.foldl (fun acc (_, v) => acc ++ collectMetas v) #[]
  | .vDataType _ params =>
    params.foldl (fun acc p => acc ++ collectMetas p) #[]
  | .vConstructor _ _ args =>
    args.foldl (fun acc a => acc ++ collectMetas a) #[]
  | .vEq _ ty lhs rhs =>
    collectMetas ty ++ collectMetas lhs ++ collectMetas rhs
  | .vRefl ty x =>
    collectMetas ty ++ collectMetas x
  | .vTransport _ ty motive lhs rhs eq body =>
    collectMetas ty ++ collectMetas motive ++ collectMetas lhs ++
    collectMetas rhs ++ collectMetas eq ++ collectMetas body

partial def collectMetasNeutral (n : Neutral) : Array MetaId :=
  match n with
  | .nVar _ => #[]
  | .nMeta id => #[id]
  | .nApp fn arg => collectMetasNeutral fn ++ collectMetas arg
  | .nFst pair => collectMetasNeutral pair
  | .nSnd pair => collectMetasNeutral pair
  | .nFieldAccess rec _ => collectMetasNeutral rec
  | .nCase scrut arms =>
    collectMetasNeutral scrut ++ arms.foldl (fun acc arm =>
      acc ++ collectMetasClosure arm.closure) #[]

partial def collectMetasClosure (clos : Closure) : Array MetaId :=
  match clos with
  | .const _ value => collectMetas value
  | .term _ env _ =>
    env.values.foldl (fun acc (_, v) => acc ++ collectMetas v) #[]

end

/-- Collect metas from a constraint -/
def collectMetasConstraint (c : Constraint) : Array MetaId :=
  match c with
  | .unify v1 v2 _ => (collectMetas v1 ++ collectMetas v2).toList.eraseDups.toArray
  | .subtype v1 v2 _ => (collectMetas v1 ++ collectMetas v2).toList.eraseDups.toArray
  | .levelEq _ _ => #[]
  | .levelLe _ _ => #[]

mutual

/-- Check if a metavariable occurs in a value (for occurs check) -/
partial def occursIn (m : MetaId) (v : Value) : Bool :=
  match v with
  | .vType _ => false
  | .vPi _ _ _ dom cod =>
    occursIn m dom || occursInClosure m cod
  | .vLam _ _ _ dom body =>
    occursIn m dom || occursInClosure m body
  | .vSigma _ _ fst snd =>
    occursIn m fst || occursInClosure m snd
  | .vPair a b => occursIn m a || occursIn m b
  | .vNeutral _ neu => occursInNeutral m neu
  | .vPrimTy _ => false
  | .vHigherPrim _ => false
  | .vIntLit _ => false
  | .vStringLit _ => false
  | .vRowEmpty => false
  | .vRowExtend label ty tail =>
    occursIn m label || occursIn m ty || occursIn m tail
  | .vRecord row => occursIn m row
  | .vVariant row => occursIn m row
  | .vLabelLit _ => false
  | .vRecordVal fields =>
    fields.any (fun (_, v) => occursIn m v)
  | .vDataType _ params =>
    params.any (occursIn m)
  | .vConstructor _ _ args =>
    args.any (occursIn m)
  | .vEq _ ty lhs rhs =>
    occursIn m ty || occursIn m lhs || occursIn m rhs
  | .vRefl ty x =>
    occursIn m ty || occursIn m x
  | .vTransport _ ty motive lhs rhs eq body =>
    occursIn m ty || occursIn m motive || occursIn m lhs ||
    occursIn m rhs || occursIn m eq || occursIn m body

partial def occursInNeutral (m : MetaId) (n : Neutral) : Bool :=
  match n with
  | .nVar _ => false
  | .nMeta id => id == m
  | .nApp fn arg => occursInNeutral m fn || occursIn m arg
  | .nFst pair => occursInNeutral m pair
  | .nSnd pair => occursInNeutral m pair
  | .nFieldAccess rec _ => occursInNeutral m rec
  | .nCase scrut arms =>
    occursInNeutral m scrut || arms.any (fun arm => occursInClosure m arm.closure)

partial def occursInClosure (m : MetaId) (clos : Closure) : Bool :=
  match clos with
  | .const _ value =>
    -- HOAS-style closure: check if metavariable occurs in the stored value
    occursIn m value
  | .term _ env body =>
    -- Term-based closure: check environment and body
    let envOccurs := env.values.any fun (_, v) => occursIn m v
    envOccurs || occursInTerm m body
where
  /-- Check if a metavariable occurs in a term -/
  occursInTerm (m : MetaId) : Term → Bool
    | .mvar id => id == m.id
    | .app fn args => occursInTerm m fn || args.any (occursInTerm m)
    | .lam _ body => occursInTerm m body
    | .pi _ _ _ dom cod => occursInTerm m dom || occursInTerm m cod
    | .sigma _ _ fst snd => occursInTerm m fst || occursInTerm m snd
    | .pair a b => occursInTerm m a || occursInTerm m b
    | .fst e => occursInTerm m e
    | .snd e => occursInTerm m e
    | .if_ c t e => occursInTerm m c || occursInTerm m t || occursInTerm m e
    | .case s arms => occursInTerm m s || arms.any fun (_, _, b) => occursInTerm m b
    | .eq _ ty l r => occursInTerm m ty || occursInTerm m l || occursInTerm m r
    | .refl ty x => occursInTerm m ty || occursInTerm m x
    | .transport _ ty mot l r eq b =>
        occursInTerm m ty || occursInTerm m mot || occursInTerm m l ||
        occursInTerm m r || occursInTerm m eq || occursInTerm m b
    | .rowExtend l t tail => occursInTerm m l || occursInTerm m t || occursInTerm m tail
    | .recordTy r => occursInTerm m r
    | .variantTy r => occursInTerm m r
    | .record fields => fields.any fun (_, t) => occursInTerm m t
    | .fieldAccess e _ => occursInTerm m e
    | .construct _ _ args => args.any (occursInTerm m)
    | _ => false

end

mutual

/-- Check if a value only references variables within the given scope (levels) -/
partial def inScope (allowedLevels : List DeBruijnLvl) (v : Value) : Bool :=
  match v with
  | .vType _ => true
  | .vPi _ _ _ dom cod =>
    inScope allowedLevels dom && inScopeClosure allowedLevels cod
  | .vLam _ _ _ dom body =>
    inScope allowedLevels dom && inScopeClosure allowedLevels body
  | .vSigma _ _ fst snd =>
    inScope allowedLevels fst && inScopeClosure allowedLevels snd
  | .vPair a b => inScope allowedLevels a && inScope allowedLevels b
  | .vNeutral _ neu => inScopeNeutral allowedLevels neu
  | .vPrimTy _ => true
  | .vHigherPrim _ => true
  | .vIntLit _ => true
  | .vStringLit _ => true
  | .vRowEmpty => true
  | .vRowExtend label ty tail =>
    inScope allowedLevels label && inScope allowedLevels ty && inScope allowedLevels tail
  | .vRecord row => inScope allowedLevels row
  | .vVariant row => inScope allowedLevels row
  | .vLabelLit _ => true
  | .vRecordVal fields =>
    fields.all (fun (_, v) => inScope allowedLevels v)
  | .vDataType _ params =>
    params.all (inScope allowedLevels)
  | .vConstructor _ _ args =>
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
  match n with
  | .nVar v => allowedLevels.contains v.level
  | .nMeta _ => true  -- Metas are always in scope
  | .nApp fn arg => inScopeNeutral allowedLevels fn && inScope allowedLevels arg
  | .nFst pair => inScopeNeutral allowedLevels pair
  | .nSnd pair => inScopeNeutral allowedLevels pair
  | .nFieldAccess rec _ => inScopeNeutral allowedLevels rec
  | .nCase scrut _ => inScopeNeutral allowedLevels scrut

partial def inScopeClosure (allowedLevels : List DeBruijnLvl) (clos : Closure) : Bool :=
  -- Check the closure's environment values are in scope
  let envInScope := clos.env.values.all fun (_, v) => inScope allowedLevels v
  if !envInScope then false
  else
    -- For the body, check if all variable references are in the allowed scope
    match clos.body with
    | some body =>
      -- The closure binds one variable, so extend allowed levels
      let extendedLevels := ⟨clos.env.size⟩ :: allowedLevels
      inScopeTerm extendedLevels body
    | none => true  -- Empty closure is always in scope
where
  /-- Check if all variable references in a term are in the allowed scope -/
  inScopeTerm (levels : List DeBruijnLvl) : Term → Bool
    | .var idx _ =>
      -- todo: don't be so conservative here (allowing it if it looks reasonable)
      idx < levels.length
    | .app fn args => inScopeTerm levels fn && args.all (inScopeTerm levels)
    | .lam _ body => inScopeTerm levels body  -- lam binds new vars
    | .pi _ _ _ dom cod => inScopeTerm levels dom && inScopeTerm levels cod
    | .sigma _ _ fst snd => inScopeTerm levels fst && inScopeTerm levels snd
    | .pair a b => inScopeTerm levels a && inScopeTerm levels b
    | .fst e => inScopeTerm levels e
    | .snd e => inScopeTerm levels e
    | .if_ c t e => inScopeTerm levels c && inScopeTerm levels t && inScopeTerm levels e
    | .case s arms => inScopeTerm levels s && arms.all fun (_, _, b) => inScopeTerm levels b
    | .eq _ ty l r => inScopeTerm levels ty && inScopeTerm levels l && inScopeTerm levels r
    | .refl ty x => inScopeTerm levels ty && inScopeTerm levels x
    | .transport _ ty mot l r eq b =>
        inScopeTerm levels ty && inScopeTerm levels mot && inScopeTerm levels l &&
        inScopeTerm levels r && inScopeTerm levels eq && inScopeTerm levels b
    | .rowExtend l t tail => inScopeTerm levels l && inScopeTerm levels t && inScopeTerm levels tail
    | .recordTy r => inScopeTerm levels r
    | .variantTy r => inScopeTerm levels r
    | .record fields => fields.all fun (_, t) => inScopeTerm levels t
    | .fieldAccess e _ => inScopeTerm levels e
    | .construct _ _ args => args.all (inScopeTerm levels)
    | _ => true

end

mutual

/-- Collect all free variables (by level) that appear in a value -/
partial def collectFreeVars (v : Value) : Array DeBruijnLvl :=
  match v with
  | .vType _ => #[]
  | .vPi _ _ _ dom cod =>
    collectFreeVars dom ++ collectFreeVarsClosure cod
  | .vLam _ _ _ dom body =>
    collectFreeVars dom ++ collectFreeVarsClosure body
  | .vSigma _ _ fst snd =>
    collectFreeVars fst ++ collectFreeVarsClosure snd
  | .vPair a b => collectFreeVars a ++ collectFreeVars b
  | .vNeutral _ neu => collectFreeVarsNeutral neu
  | .vPrimTy _ => #[]
  | .vHigherPrim _ => #[]
  | .vIntLit _ => #[]
  | .vStringLit _ => #[]
  | .vRowEmpty => #[]
  | .vRowExtend label ty tail =>
    collectFreeVars label ++ collectFreeVars ty ++ collectFreeVars tail
  | .vRecord row => collectFreeVars row
  | .vVariant row => collectFreeVars row
  | .vLabelLit _ => #[]
  | .vRecordVal fields =>
    fields.foldl (fun acc (_, v) => acc ++ collectFreeVars v) #[]
  | .vDataType _ params =>
    params.foldl (fun acc p => acc ++ collectFreeVars p) #[]
  | .vConstructor _ _ args =>
    args.foldl (fun acc a => acc ++ collectFreeVars a) #[]
  | .vEq _ ty lhs rhs =>
    collectFreeVars ty ++ collectFreeVars lhs ++ collectFreeVars rhs
  | .vRefl ty x =>
    collectFreeVars ty ++ collectFreeVars x
  | .vTransport _ ty motive lhs rhs eq body =>
    collectFreeVars ty ++ collectFreeVars motive ++ collectFreeVars lhs ++
    collectFreeVars rhs ++ collectFreeVars eq ++ collectFreeVars body

partial def collectFreeVarsNeutral (n : Neutral) : Array DeBruijnLvl :=
  match n with
  | .nVar v => #[v.level]
  | .nMeta _ => #[] -- Metas don't contribute free vars for pruning
  | .nApp fn arg => collectFreeVarsNeutral fn ++ collectFreeVars arg
  | .nFst pair => collectFreeVarsNeutral pair
  | .nSnd pair => collectFreeVarsNeutral pair
  | .nFieldAccess rec _ => collectFreeVarsNeutral rec
  | .nCase scrut arms =>
    collectFreeVarsNeutral scrut ++ arms.foldl (fun acc arm =>
      acc ++ collectFreeVarsClosure arm.closure) #[]

partial def collectFreeVarsClosure (clos : Closure) : Array DeBruijnLvl :=
  match clos with
  | .const _ value => collectFreeVars value
  | .term _ env _ =>
    env.values.foldl (fun acc (_, v) => acc ++ collectFreeVars v) #[]

end

/-- Extract metavariable and spine from a neutral -/
def getMetaWithSpine (neu : Neutral) : Option (MetaId × List Value) :=
  match neu with
  | .nMeta m => some (m, [])
  | .nApp fn arg =>
    match getMetaWithSpine fn with
    | some (m, spine) => some (m, spine ++ [arg])
    | none => none
  | _ => none

/-- Build a neutral from a metavariable and a spine (inverse of getMetaWithSpine) -/
def buildMetaSpine (m : MetaId) (spine : List Value) : Neutral :=
  spine.foldl (fun neu arg => .nApp neu arg) (.nMeta m)

/-- Convert a Value to a Neutral (for eta expansion) -/
def valueToNeutral (v : Value) : Neutral :=
  match v with
  | .vNeutral _ neu => neu
  | _ => .nVar ⟨"_eta", ⟨0⟩⟩  -- Placeholder

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
  | .vLam _ _ _ _ _ => "vLam"
  | .vSigma _ _ _ _ => "vSigma"
  | .vPair _ _ => "vPair"
  | .vNeutral _ n => s!"vNeutral({getNeutralKind n})"
  | .vPrimTy p => s!"vPrimTy({p})"
  | .vHigherPrim p => s!"vHigherPrim({p})"
  | .vIntLit _ => "vIntLit"
  | .vStringLit _ => "vStringLit"
  | .vRowEmpty => "vRowEmpty"
  | .vRowExtend _ _ _ => "vRowExtend"
  | .vRecord _ => "vRecord"
  | .vVariant _ => "vVariant"
  | .vRecordVal _ => "vRecordVal"
  | .vLabelLit _ => "vLabelLit"
  | .vDataType id _ => s!"vDataType({id.name})"
  | .vConstructor n _ _ => s!"vConstructor({n})"
  | .vEq _ _ _ _ => "vEq"
  | .vRefl _ _ => "vRefl"
  | .vTransport _ _ _ _ _ _ _ => "vTransport"
where
  getNeutralKind : Neutral → String
    | .nVar v => s!"nVar({v.name})"
    | .nMeta m => s!"nMeta({m.id})"
    | .nApp _ _ => "nApp"
    | .nFst _ => "nFst"
    | .nSnd _ => "nSnd"
    | .nFieldAccess _ f => s!"nFieldAccess({f})"
    | .nCase _ _ => "nCase"

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
