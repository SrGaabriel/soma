import Soma.Core.Value

namespace Soma.Dependent.Value

open Soma.Core

/-- A monoid for combining traversal results -/
class TraversalMonoid (α : Type) extends Inhabited α where
  empty : α
  combine : α → α → α

instance : TraversalMonoid (Array β) where
  default := #[]
  empty := #[]
  combine := (· ++ ·)

instance : TraversalMonoid Bool where
  default := false
  empty := false
  combine := (· || ·)

instance : TraversalMonoid Unit where
  default := ()
  empty := ()
  combine _ _ := ()

/-- Conjunction monoid for Bool (all must be true) -/
structure AllTrue where
  val : Bool := true
  deriving Inhabited

instance : TraversalMonoid AllTrue where
  default := ⟨true⟩
  empty := ⟨true⟩
  combine a b := ⟨a.val && b.val⟩

/-- Action to take at each node during traversal -/
structure TraversalAction (α : Type) [TraversalMonoid α] where
  /-- Action for metavariables -/
  onMeta : MetaId → α := fun _ => TraversalMonoid.empty
  /-- Action for bound variables -/
  onVar : BoundVar → α := fun _ => TraversalMonoid.empty
  /-- Action for neutral terms (called before recursing) -/
  onNeutral : Neutral → Option α := fun _ => none
  /-- Action for values (called before recursing) -/
  onValue : Value → Option α := fun _ => none

namespace TraversalAction

/-- Create an action that collects metavariables -/
def collectMetas : TraversalAction (Array MetaId) where
  onMeta m := #[m]

/-- Create an action that checks if a specific meta occurs -/
def metaOccurs (target : MetaId) : TraversalAction Bool where
  onMeta m := m == target

/-- Create an action that collects free variables -/
def collectFreeVars : TraversalAction (Array DeBruijnLvl) where
  onVar v := #[v.level]

/-- Create an action that checks if a value is in scope -/
def inScope (allowedLevels : List DeBruijnLvl) : TraversalAction AllTrue where
  onVar v := ⟨allowedLevels.contains v.level⟩

end TraversalAction

variable {α : Type} [inst : TraversalMonoid α]

mutual

/-- Traverse a Value and collect results using a TraversalAction -/
partial def traverseValue (action : TraversalAction α) (v : Value) : α :=
  -- Check if action wants to short-circuit
  match action.onValue v with
  | some result => result
  | none =>
    match v with
    | .vType _ => inst.empty

    | .vPi _ _ _ dom cod =>
      inst.combine (traverseValue action dom) (traverseClosure action cod)

    | .vLam _ body =>
      traverseClosure action body

    | .vSigma _ _ fst snd =>
      inst.combine (traverseValue action fst) (traverseClosure action snd)

    | .vPair a b =>
      inst.combine (traverseValue action a) (traverseValue action b)

    | .vNeutral ty neu =>
      inst.combine (traverseValue action ty) (traverseNeutral action neu)

    | .vPrimTy _ => inst.empty
    | .vIntLit _ => inst.empty
    | .vStringLit _ => inst.empty
    | .vRowEmpty => inst.empty
    | .vLabelLit _ => inst.empty
    | .vRowSort | .vLabelSort => inst.empty

    | .vRowExtend label ty tail =>
      inst.combine
        (inst.combine (traverseValue action label) (traverseValue action ty))
        (traverseValue action tail)

    | .vRecord row => traverseValue action row
    | .vVariant row => traverseValue action row

    | .vRecordVal fields =>
      fields.foldl (fun acc (_, v) =>
        inst.combine acc (traverseValue action v)) inst.empty

    | .vDataType _ params =>
      params.foldl (fun acc p =>
        inst.combine acc (traverseValue action p)) inst.empty

    | .vConstructor _ _ args rty =>
      let argsResult := args.foldl (fun acc a =>
        inst.combine acc (traverseValue action a)) inst.empty
      inst.combine argsResult (traverseValue action rty)

    | .vEq _ ty lhs rhs =>
      inst.combine
        (inst.combine (traverseValue action ty) (traverseValue action lhs))
        (traverseValue action rhs)

    | .vRefl ty x =>
      inst.combine (traverseValue action ty) (traverseValue action x)

    | .vTransport _ ty motive lhs rhs eq body =>
      let r1 := inst.combine (traverseValue action ty) (traverseValue action motive)
      let r2 := inst.combine (traverseValue action lhs) (traverseValue action rhs)
      let r3 := inst.combine (traverseValue action eq) (traverseValue action body)
      inst.combine (inst.combine r1 r2) r3

/-- Traverse a Neutral term -/
partial def traverseNeutral (action : TraversalAction α) (n : Neutral) : α :=
  -- Check if action wants to short-circuit
  match action.onNeutral n with
  | some result => result
  | none =>
    match n with
    | .nVar v => action.onVar v
    | .nMeta m => action.onMeta m

    | .nApp fn arg =>
      inst.combine (traverseNeutral action fn) (traverseValue action arg)

    | .nFst pair => traverseNeutral action pair
    | .nSnd pair => traverseNeutral action pair
    | .nFieldAccess rec _ => traverseNeutral action rec

    | .nCase scrut arms rty =>
      let scrutResult := traverseNeutral action scrut
      let armsResult := arms.foldl (fun acc arm =>
        inst.combine acc (traverseClosure action arm.closure)) scrutResult
      inst.combine armsResult (traverseValue action rty)

/-- Traverse a Closure -/
partial def traverseClosure (action : TraversalAction α) (clos : Closure) : α :=
  match clos with
  | .const _ value => traverseValue action value
  | .term _ env _ =>
    env.values.foldl (fun acc (_, v) =>
      inst.combine acc (traverseValue action v)) inst.empty

end

/-- Collect all metavariable IDs in a value -/
def collectMetas (v : Value) : Array MetaId :=
  traverseValue TraversalAction.collectMetas v

/-- Collect all metavariable IDs in a neutral -/
def collectMetasNeutral (n : Neutral) : Array MetaId :=
  traverseNeutral TraversalAction.collectMetas n

/-- Collect all metavariable IDs in a closure -/
def collectMetasClosure (c : Closure) : Array MetaId :=
  traverseClosure TraversalAction.collectMetas c

/-- Check if a metavariable occurs in a value -/
def occursIn (m : MetaId) (v : Value) : Bool :=
  traverseValue (TraversalAction.metaOccurs m) v

/-- Check if a metavariable occurs in a neutral -/
def occursInNeutral (m : MetaId) (n : Neutral) : Bool :=
  traverseNeutral (TraversalAction.metaOccurs m) n

/-- Check if a metavariable occurs in a closure -/
def occursInClosure (m : MetaId) (c : Closure) : Bool :=
  traverseClosure (TraversalAction.metaOccurs m) c

/-- Collect all free variables (by level) in a value -/
def collectFreeVars (v : Value) : Array DeBruijnLvl :=
  traverseValue TraversalAction.collectFreeVars v

/-- Collect all free variables in a neutral -/
def collectFreeVarsNeutral (n : Neutral) : Array DeBruijnLvl :=
  traverseNeutral TraversalAction.collectFreeVars n

/-- Collect all free variables in a closure -/
def collectFreeVarsClosure (c : Closure) : Array DeBruijnLvl :=
  traverseClosure TraversalAction.collectFreeVars c

/-- Check if a value only references variables within the given scope -/
def inScope (allowedLevels : List DeBruijnLvl) (v : Value) : Bool :=
  (traverseValue (TraversalAction.inScope allowedLevels) v).val

/-- Check if a neutral only references variables within the given scope -/
def inScopeNeutral (allowedLevels : List DeBruijnLvl) (n : Neutral) : Bool :=
  (traverseNeutral (TraversalAction.inScope allowedLevels) n).val

variable {M : Type → Type} [Monad M]

/-- Monadic traversal action -/
structure MTraversalAction (M : Type → Type) (α : Type) [Monad M] [TraversalMonoid α] where
  /-- Action for metavariables -/
  onMeta : MetaId → M α := fun _ => pure TraversalMonoid.empty
  /-- Action for bound variables -/
  onVar : BoundVar → M α := fun _ => pure TraversalMonoid.empty
  /-- Action for values (called before recursing, return some to short-circuit) -/
  onValue : Value → M (Option α) := fun _ => pure none
  /-- Action for neutrals (called before recursing) -/
  onNeutral : Neutral → M (Option α) := fun _ => pure none

variable [instM : Inhabited (M α)]

mutual

/-- Monadic traversal of a Value -/
partial def traverseValueM
    (action : MTraversalAction M α) (v : Value) : M α := do
  -- Check if action wants to short-circuit
  match ← action.onValue v with
  | some result => return result
  | none =>
    match v with
    | .vType _ => return inst.empty

    | .vPi _ _ _ dom cod =>
      let r1 ← traverseValueM action dom
      let r2 ← traverseClosureM action cod
      return inst.combine r1 r2

    | .vLam _ body =>
      traverseClosureM action body

    | .vSigma _ _ fst snd =>
      let r1 ← traverseValueM action fst
      let r2 ← traverseClosureM action snd
      return inst.combine r1 r2

    | .vPair a b =>
      let r1 ← traverseValueM action a
      let r2 ← traverseValueM action b
      return inst.combine r1 r2

    | .vNeutral ty neu =>
      let r1 ← traverseValueM action ty
      let r2 ← traverseNeutralM action neu
      return inst.combine r1 r2

    | .vPrimTy _ => return inst.empty
    | .vIntLit _ => return inst.empty
    | .vStringLit _ => return inst.empty
    | .vRowEmpty => return inst.empty
    | .vLabelLit _ => return inst.empty
    | .vRowSort | .vLabelSort => return inst.empty

    | .vRowExtend label ty tail =>
      let r1 ← traverseValueM action label
      let r2 ← traverseValueM action ty
      let r3 ← traverseValueM action tail
      return inst.combine (inst.combine r1 r2) r3

    | .vRecord row => traverseValueM action row
    | .vVariant row => traverseValueM action row

    | .vRecordVal fields =>
      let mut result := inst.empty
      for (_, v) in fields do
        let r ← traverseValueM action v
        result := inst.combine result r
      return result

    | .vDataType _ params =>
      let mut result := inst.empty
      for p in params do
        let r ← traverseValueM action p
        result := inst.combine result r
      return result

    | .vConstructor _ _ args rty =>
      let mut result := inst.empty
      for a in args do
        let r ← traverseValueM action a
        result := inst.combine result r
      let rtyResult ← traverseValueM action rty
      return inst.combine result rtyResult

    | .vEq _ ty lhs rhs =>
      let r1 ← traverseValueM action ty
      let r2 ← traverseValueM action lhs
      let r3 ← traverseValueM action rhs
      return inst.combine (inst.combine r1 r2) r3

    | .vRefl ty x =>
      let r1 ← traverseValueM action ty
      let r2 ← traverseValueM action x
      return inst.combine r1 r2

    | .vTransport _ ty motive lhs rhs eq body =>
      let r1 ← traverseValueM action ty
      let r2 ← traverseValueM action motive
      let r3 ← traverseValueM action lhs
      let r4 ← traverseValueM action rhs
      let r5 ← traverseValueM action eq
      let r6 ← traverseValueM action body
      let c1 := inst.combine r1 r2
      let c2 := inst.combine r3 r4
      let c3 := inst.combine r5 r6
      return inst.combine (inst.combine c1 c2) c3

/-- Monadic traversal of a Neutral -/
partial def traverseNeutralM
    (action : MTraversalAction M α) (n : Neutral) : M α := do
  match ← action.onNeutral n with
  | some result => return result
  | none =>
    match n with
    | .nVar v => action.onVar v
    | .nMeta m => action.onMeta m

    | .nApp fn arg =>
      let r1 ← traverseNeutralM action fn
      let r2 ← traverseValueM action arg
      return inst.combine r1 r2

    | .nFst pair => traverseNeutralM action pair
    | .nSnd pair => traverseNeutralM action pair
    | .nFieldAccess rec _ => traverseNeutralM action rec

    | .nCase scrut arms rty =>
      let mut result ← traverseNeutralM action scrut
      for arm in arms do
        let r ← traverseClosureM action arm.closure
        result := inst.combine result r
      let rtyResult ← traverseValueM action rty
      return inst.combine result rtyResult

/-- Monadic traversal of a Closure -/
partial def traverseClosureM
    (action : MTraversalAction M α) (clos : Closure) : M α := do
  match clos with
  | .const _ value => traverseValueM action value
  | .term _ env _ =>
    let mut result := inst.empty
    for (_, v) in env.values do
      let r ← traverseValueM action v
      result := inst.combine result r
    return result

end

/-- A transformer that rewrites values during traversal -/
structure ValueTransformer (M : Type → Type) [Monad M] where
  /-- Transform a value (return none to continue with default recursion) -/
  transformValue : Value → M (Option Value) := fun _ => pure none
  /-- Transform a neutral -/
  transformNeutral : Neutral → M (Option Neutral) := fun _ => pure none
  /-- Transform a closure -/
  transformClosure : Closure → M (Option Closure) := fun _ => pure none

variable [Inhabited (M Value)] [Inhabited (M Neutral)] [Inhabited (M Closure)]

mutual

/-- Transform a Value using a ValueTransformer -/
partial def transformValueM (t : ValueTransformer M) (v : Value) : M Value := do
  -- Check if transformer wants to handle this value directly
  match ← t.transformValue v with
  | some result => return result
  | none =>
    match v with
    | .vType l => return .vType l

    | .vPi qty binder name dom cod =>
      let dom' ← transformValueM t dom
      let cod' ← transformClosureM t cod
      return .vPi qty binder name dom' cod'

    | .vLam name body =>
      let body' ← transformClosureM t body
      return .vLam name body'

    | .vSigma qty name fst snd =>
      let fst' ← transformValueM t fst
      let snd' ← transformClosureM t snd
      return .vSigma qty name fst' snd'

    | .vPair a b =>
      let a' ← transformValueM t a
      let b' ← transformValueM t b
      return .vPair a' b'

    | .vNeutral ty neu =>
      let ty' ← transformValueM t ty
      let neu' ← transformNeutralM t neu
      return .vNeutral ty' neu'

    | .vPrimTy p => return .vPrimTy p
    | .vIntLit n => return .vIntLit n
    | .vStringLit s => return .vStringLit s
    | .vRowEmpty => return .vRowEmpty
    | .vLabelLit name => return .vLabelLit name
    | .vRowSort => return .vRowSort
    | .vLabelSort => return .vLabelSort

    | .vRowExtend label ty tail =>
      let label' ← transformValueM t label
      let ty' ← transformValueM t ty
      let tail' ← transformValueM t tail
      return .vRowExtend label' ty' tail'

    | .vRecord row =>
      let row' ← transformValueM t row
      return .vRecord row'

    | .vVariant row =>
      let row' ← transformValueM t row
      return .vVariant row'

    | .vRecordVal fields =>
      let fields' ← fields.mapM fun (name, v) => do
        let v' ← transformValueM t v
        return (name, v')
      return .vRecordVal fields'

    | .vDataType id params =>
      let params' ← params.mapM (transformValueM t)
      return .vDataType id params'

    | .vConstructor name tag args rty =>
      let args' ← args.mapM (transformValueM t)
      let rty' ← transformValueM t rty
      return .vConstructor name tag args' rty'

    | .vEq tyLevel ty lhs rhs =>
      let ty' ← transformValueM t ty
      let lhs' ← transformValueM t lhs
      let rhs' ← transformValueM t rhs
      return .vEq tyLevel ty' lhs' rhs'

    | .vRefl ty x =>
      let ty' ← transformValueM t ty
      let x' ← transformValueM t x
      return .vRefl ty' x'

    | .vTransport tyLevel ty motive lhs rhs eq body =>
      let ty' ← transformValueM t ty
      let motive' ← transformValueM t motive
      let lhs' ← transformValueM t lhs
      let rhs' ← transformValueM t rhs
      let eq' ← transformValueM t eq
      let body' ← transformValueM t body
      return .vTransport tyLevel ty' motive' lhs' rhs' eq' body'

/-- Transform a Neutral using a ValueTransformer -/
partial def transformNeutralM (t : ValueTransformer M) (n : Neutral) : M Neutral := do
  match ← t.transformNeutral n with
  | some result => return result
  | none =>
    match n with
    | .nVar v => return .nVar v
    | .nMeta m => return .nMeta m

    | .nApp fn arg =>
      let fn' ← transformNeutralM t fn
      let arg' ← transformValueM t arg
      return .nApp fn' arg'

    | .nFst pair =>
      let pair' ← transformNeutralM t pair
      return .nFst pair'

    | .nSnd pair =>
      let pair' ← transformNeutralM t pair
      return .nSnd pair'

    | .nFieldAccess rec field =>
      let rec' ← transformNeutralM t rec
      return .nFieldAccess rec' field

    | .nCase scrut arms rty =>
      let scrut' ← transformNeutralM t scrut
      let arms' ← arms.mapM fun arm => do
        let clos' ← transformClosureM t arm.closure
        return ArmClosure.mk arm.pattern clos'
      let rty' ← transformValueM t rty
      return .nCase scrut' arms' rty'

/-- Transform a Closure using a ValueTransformer -/
partial def transformClosureM (t : ValueTransformer M) (clos : Closure) : M Closure := do
  match ← t.transformClosure clos with
  | some result => return result
  | none =>
    match clos with
    | .const name value =>
      let value' ← transformValueM t value
      return .const name value'
    | .term name env body =>
      let values' ← env.values.mapM fun (n, v) => do
        let v' ← transformValueM t v
        return (n, v')
      return .term name (Env.mk values' env.size) body

end

end Soma.Dependent.Value
