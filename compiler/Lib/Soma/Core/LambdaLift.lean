import Soma.Core.Function
import Soma.Core.Module
import Soma.Core.Value
import Soma.Core.Expr
import Soma.Core.Eval
import Soma.Core.Quote
import Std.Data.HashMap
import Std.Data.HashSet

namespace Soma.Core.LambdaLift

open Soma.Syntax (Span)
open Soma.Core (Value QualifiedName TypedFunction)
open Std (HashMap HashSet)

/-- Key for a constructor's field-type metadata -/
structure ConstructorKey where
  parent : Soma.Unique
  tag : Nat
  deriving BEq, Hashable, Inhabited

structure ConstructorTypeInfo where
  fieldTypes : Array Value
  deriving Inhabited

abbrev ConstructorTypeRegistry := HashMap ConstructorKey ConstructorTypeInfo

namespace ConstructorTypeRegistry

def register (reg : ConstructorTypeRegistry) (parent : Soma.Unique) (tag : Nat)
    (info : ConstructorTypeInfo) : ConstructorTypeRegistry :=
  reg.insert ⟨parent, tag⟩ info

def lookup (reg : ConstructorTypeRegistry) (parent : Soma.Unique) (tag : Nat)
    : Option ConstructorTypeInfo :=
  reg.get? ⟨parent, tag⟩

end ConstructorTypeRegistry

/-- Extract explicit constructor field types from an elaborated constructor type -/
partial def constructorTypeInfoFromElaboratedType (ctorTy : Value)
    : ConstructorTypeInfo :=
  { fieldTypes := go ctorTy 0 #[] }
where
  go (ty : Value) (level : Nat) (acc : Array Value) : Array Value :=
    match ty with
    | .vPi _qty binder name dom cod =>
      let arg : Value := .vNeutral dom (.nVar ⟨name, ⟨level⟩⟩)
      let next := cod.applyPure arg
      if binder.isImplicit then
        go next (level + 1) acc
      else
        go next (level + 1) (acc.push dom)
    | _ => acc

structure LiftState where
  nextId : Nat := 0
  liftedFunctions : Array TypedFunction := #[]
  globalNames : HashSet QualifiedName := {}
  moduleName : String
  globalEnv : Soma.Core.GlobalEnv := .empty
  unfoldTy : Value → Value := id
  typeParamEnv : Soma.Core.Env := .empty
  metas : Soma.Core.MetaState := .empty
  /-- Qualified name of `io_bind` (when known) for pre-lift inlining -/
  ioBindName? : Option QualifiedName := none
  /-- Qualified name of `pure_io` (when known) for pre-lift inlining -/
  pureIOName? : Option QualifiedName := none
  /-- Unique id of the wired-in `World` type -/
  worldUnique? : Option Soma.Unique := none
  /-- Qualified name of the `Pair::Mk` constructor and its tag -/
  pairCtorName? : Option QualifiedName := none
  pairCtorTag : Nat := 0
  /-- Unique id of the wired-in `Pair` type (the inductive itself, not the `Mk` ctor) -/
  pairUnique? : Option Soma.Unique := none
  /-- Constructor field-type metadata keyed by parent data type and constructor tag -/
  ctorTypes : ConstructorTypeRegistry := {}
  deriving Inhabited

abbrev LiftM := StateM LiftState

namespace LiftM

def run (m : LiftM α) (moduleName : String) (globalNames : HashSet QualifiedName)
    (startId : Nat := 0) (globalEnv : Soma.Core.GlobalEnv := .empty)
    (unfoldTy : Value → Value := id)
    (metas : Soma.Core.MetaState := .empty)
    (ioBindName? : Option QualifiedName := none)
    (pureIOName? : Option QualifiedName := none)
    (worldUnique? : Option Soma.Unique := none)
    (pairCtorName? : Option QualifiedName := none)
    (pairCtorTag : Nat := 0)
    (pairUnique? : Option Soma.Unique := none)
    (ctorTypes : ConstructorTypeRegistry := {}) : α × LiftState :=
  StateT.run m { moduleName, globalNames, nextId := startId, globalEnv, unfoldTy, metas,
                 ioBindName?, pureIOName?, worldUnique?, pairCtorName?, pairCtorTag,
                 pairUnique?, ctorTypes }

def freshId : LiftM Nat := do
  let st ← get
  let id := st.nextId
  set { st with nextId := id + 1 }
  pure id

def freshUnique (name : String) : LiftM Soma.Unique := do
  let st ← get
  let id ← freshId
  pure { id := id, module := st.moduleName, original := name }

def freshLambdaName : LiftM QualifiedName := do
  let st ← get
  let id ← freshId
  let original := s!"lambda${id}"
  let unique : Soma.Unique := { id := id, module := st.moduleName, original }
  pure ⟨unique⟩

def addLiftedFunction (fn : TypedFunction) : LiftM Unit := do
  let st ← get
  set { st with
    liftedFunctions := st.liftedFunctions.push fn
    globalNames := st.globalNames.insert fn.name
  }

def isGlobal (name : QualifiedName) : LiftM Bool := do
  let st ← get
  pure (st.globalNames.contains name)

end LiftM

def buildFnType (paramTypes : Array Value) (resultType : Value) : Value :=
  paramTypes.foldr (init := resultType) fun paramTy acc =>
    Value.vPi Soma.Core.Quantity.omega Soma.Core.BinderInfo.explicit "_" paramTy
      (Soma.Core.Closure.const "_" acc)

/-- Apply an argument to an expression, pushing the application down through
    control-flow scaffolding so it reaches the point where the function is
    actually available.

    Used by η-expansion and by the `io_bind` inliner's continuation step:
    when an IO function's body evaluates to a term of type
    `World -> Pair World X` that's guarded by `case` / `let` / `if`, a naive
    `App(body, w)` parks the world application OUTSIDE the guard — Circuit
    lowering can't thread `w` into the inner computation. Pushing down
    instead lets each inner IO-producing branch see its `w` directly, so
    `io_bind m f w` reaches the inliner saturated and inlines to a let
    chain.

    - `lambda`: β-reduce (substitute `arg` for the binder)
    - `case`: distribute into each arm's body
    - `let_`: push into the in-body
    - `if`: push into both branches
    - else: just `App(expr, arg)` -/
partial def applyPushingDown (expr : Soma.Core.Expr) (arg : Soma.Core.Expr)
    : Soma.Core.Expr :=
  match expr with
  | .lam _ _ _ body => Soma.Core.Expr.instantiate body arg
  | .«case» scruts motive arms =>
    let arms' := arms.map fun arm =>
      Soma.Core.Arm.mk arm.patterns (applyPushingDown arm.body arg)
    .«case» scruts motive arms'
  | .let_ name ty val body =>
    .let_ name ty val (applyPushingDown body arg)
  | .if_ c t e =>
    .if_ c (applyPushingDown t arg) (applyPushingDown e arg)
  | _ => .app expr arg

/-- Substitute data-type parameters for the neutral variables used by elaborated constructor types -/
partial def substituteCtorTypeParams (v : Value) (params : Array Value) : Value :=
  match v with
  | .vNeutral ty neu =>
    if neu.isBareHead then
      match neu.head with
      | .hVar bv => params[bv.level.lvl]?.getD v
      | _ => .vNeutral (substituteCtorTypeParams ty params) neu
    else
      .vNeutral (substituteCtorTypeParams ty params) neu
  | .vPi qty binder name dom cod =>
    let dom' := substituteCtorTypeParams dom params
    let cod' := match cod with
      | .const n body => .const n (substituteCtorTypeParams body params)
      | other => other
    .vPi qty binder name dom' cod'
  | .vDataType uid ps =>
    .vDataType uid (ps.map (substituteCtorTypeParams · params))
  | .vRecord row => .vRecord (substituteCtorTypeParams row params)
  | .vVariant row => .vVariant (substituteCtorTypeParams row params)
  | .vRowExtend l f t =>
    .vRowExtend (substituteCtorTypeParams l params)
      (substituteCtorTypeParams f params)
      (substituteCtorTypeParams t params)
  | .vConstructor name tag args rty =>
    .vConstructor name tag (args.map (substituteCtorTypeParams · params))
      (substituteCtorTypeParams rty params)
  | other => other

private def rowFieldTypeByLabel (row : Value) (label : String) : Option Value :=
  match row with
  | .vRowExtend (.vLabelLit name) fieldTy tail =>
    if name == label then some fieldTy else rowFieldTypeByLabel tail label
  | .vRowExtend _ _ tail => rowFieldTypeByLabel tail label
  | _ => none

private def dataCtorFieldTypes (st : LiftState) (scrutTy : Value)
    (ctorName : QualifiedName) (tag arity : Nat) : Array Value :=
  match st.unfoldTy scrutTy with
  | .vDataType uid params =>
    match st.ctorTypes.lookup uid tag with
    | some info =>
      info.fieldTypes.map (substituteCtorTypeParams · params.toArray)
    | none =>
      if arity == 0 then #[]
      else panic! s!"lambda lift: missing constructor metadata for {ctorName.display} at {uid.display}#{tag}"
  | _ =>
    if arity == 0 then #[]
    else panic! s!"lambda lift: cannot compute field types for constructor {ctorName.display}"

partial def collectPatternBindingTypes (st : LiftState)
    (pat : Soma.Core.Pattern) (expectedTy : Value)
    : Array (Soma.Unique × Value) :=
  match pat with
  | .var (some u) => #[(u, st.unfoldTy expectedTy)]
  | .var none | .wildcard | .lit _ => #[]
  | .ctor name tag fields =>
    let fieldTypes := dataCtorFieldTypes st expectedTy name tag fields.size
    let rec go (i : Nat) (acc : Array (Soma.Unique × Value)) : Array (Soma.Unique × Value) :=
      if h : i < fields.size then
        let fieldTy := fieldTypes[i]?.getD
          (panic! s!"lambda lift: constructor {name.display} field {i} missing type")
        go (i + 1) (acc ++ collectPatternBindingTypes st fields[i] fieldTy)
      else acc
    go 0 #[]
  | .inject label arg? =>
    match arg? with
    | none => #[]
    | some arg =>
      match st.unfoldTy expectedTy with
      | .vVariant row =>
        match rowFieldTypeByLabel row label with
        | some fieldTy => collectPatternBindingTypes st arg fieldTy
        | none => panic! s!"lambda lift: variant label '{label}' not present in scrutinee type"
      | _ =>
        panic! s!"lambda lift: inject pattern '{label}' over non-variant type"

def collectArmBindingTypes (st : LiftState) (patterns : Array Soma.Core.Pattern)
    (scrutTypes : Array Value) : Array (Soma.Unique × Value) :=
  let rec go (i : Nat) (acc : Array (Soma.Unique × Value)) : Array (Soma.Unique × Value) :=
    if h : i < patterns.size then
      let scrutTy := scrutTypes[i]?.getD
        (panic! s!"lambda lift: missing scrutinee type for pattern column {i}")
      go (i + 1) (acc ++ collectPatternBindingTypes st patterns[i] scrutTy)
    else acc
  go 0 #[]

/-- Inline `pure_io x w` and `io_bind m f w` at saturated calls -/
partial def inlineIOBind (e : Soma.Core.Expr) : LiftM Soma.Core.Expr := do
  match e with
  | .app .. =>
    let (head, rawArgs) := Soma.Core.Expr.collectAppSpine e
    match head with
    | .const qn _ =>
      let st ← get
      let isPureIO := st.pureIOName?.any (· == qn)
      let isIOBind := st.ioBindName?.any (· == qn)
      let rawExplicit := rawArgs.filter (!·.isTypeLevelExpr)
      -- Saturated io_bind m f w → case (m w) | Pair::Mk w' v => f v w'.
      if isIOBind && rawExplicit.size == 3 then
        match st.pairCtorName? with
        | some pairQn =>
          let m ← inlineIOBind rawExplicit[0]!
          let f := rawExplicit[1]!
          let w ← inlineIOBind rawExplicit[2]!
          let mApplied := Soma.Core.Expr.app m w
          let wFresh ← LiftM.freshUnique "_w"
          let valFresh ← LiftM.freshUnique "_v"
          let worldTyExpr : Soma.Core.Expr := match st.worldUnique? with
            | some wU => .dataTy wU #[]
            | none => Soma.Core.Expr.sort .zero
          let valTyExpr := Soma.Core.Expr.sort .zero
          let pairPat : Soma.Core.Pattern :=
            .ctor pairQn st.pairCtorTag
              #[.var (some wFresh), .var (some valFresh)]
          let appliedBody : Soma.Core.Expr := match f with
            | .lam _ _ _ innerBody =>
              let opened := Soma.Core.Expr.instantiate innerBody
                (.fvar valFresh valTyExpr)
              applyPushingDown opened (.fvar wFresh worldTyExpr)
            | _ =>
              applyPushingDown (.app f (.fvar valFresh valTyExpr))
                (.fvar wFresh worldTyExpr)
          let appliedBody' ← inlineIOBind appliedBody
          -- Close the fresh fvars into bvars so the arm body matches the
          -- locally-nameless convention the rest of the compiler expects.
          let closedBody :=
            (appliedBody'.abstractFVar wFresh).abstractFVar valFresh
          let motive : Soma.Core.Expr :=
            .lam .explicit "_" (.sort .zero) (.sort .zero)
          return .case #[mApplied] motive #[Soma.Core.Arm.mk #[pairPat] closedBody]
        | none => pure ()
      -- Saturated pure_io x w → Pair::Mk w x. Emit a Pair construct literal
      -- whose stated result type is a real `vDataType pairUid [World, X]`
      if isPureIO && rawExplicit.size == 2 then
        match st.pairCtorName?, st.pairUnique?, st.worldUnique? with
        | some pairQn, some pairU, some worldU =>
          let x ← inlineIOBind rawExplicit[0]!
          let w ← inlineIOBind rawExplicit[1]!
          let xTyExpr : Soma.Core.Expr :=
            Soma.Core.Expr.typeOf x st.globalEnv st.unfoldTy st.metas
              |> Soma.Core.quoteExpr ⟨0⟩
          let worldTyExpr : Soma.Core.Expr := .dataTy worldU #[]
          let resultTy : Soma.Core.Expr :=
            .dataTy pairU #[worldTyExpr, xTyExpr]
          return .construct pairQn st.pairCtorTag #[w, x] resultTy
        | _, _, _ => pure ()
      if isPureIO && rawExplicit.size == 1 then
        return ← inlineIOBind rawExplicit[0]!
      let args ← rawArgs.mapM inlineIOBind
      return Soma.Core.Expr.rebuildAppSpine head args
    | _ =>
      let head' ← inlineIOBind head
      let args ← rawArgs.mapM inlineIOBind
      return Soma.Core.Expr.rebuildAppSpine head' args

  | .lam info name domain body =>
    let domain' ← inlineIOBind domain
    let u ← LiftM.freshUnique name
    let opened := Soma.Core.Expr.instantiate body (.fvar u domain')
    let body' ← inlineIOBind opened
    return .lam info name domain' (Soma.Core.Expr.abstractFVar body' u)
  | .let_ name ty val body =>
    let ty' ← inlineIOBind ty
    let val' ← inlineIOBind val
    let u ← LiftM.freshUnique name
    let opened := Soma.Core.Expr.instantiate body (.fvar u ty')
    let body' ← inlineIOBind opened
    return .let_ name ty' val' (Soma.Core.Expr.abstractFVar body' u)
  | .pi q info name dom cod =>
    let dom' ← inlineIOBind dom
    let u ← LiftM.freshUnique name
    let opened := Soma.Core.Expr.instantiate cod (.fvar u dom')
    let cod' ← inlineIOBind opened
    return .pi q info name dom' (Soma.Core.Expr.abstractFVar cod' u)
  | .construct n t args rty =>
    return .construct n t (← args.mapM inlineIOBind) (← inlineIOBind rty)
  | .«case» scruts motive arms =>
    let scruts' ← scruts.mapM inlineIOBind
    let motive' ← inlineIOBind motive
    let st ← get
    let scrutTypes := scruts'.map fun scrut =>
      Soma.Core.Expr.typeOf scrut st.globalEnv st.unfoldTy st.metas
    let arms' ← arms.mapM fun arm => do
      let bindings := collectArmBindingTypes st arm.patterns scrutTypes
      let openedBody := bindings.foldr
        (fun (uid, ty) body =>
          body.instantiate (.fvar uid (Soma.Core.quoteExpr ⟨0⟩ ty)))
        arm.body
      let liftedBody ← inlineIOBind openedBody
      let closedBody := bindings.foldl
        (fun body (uid, _) => body.abstractFVar uid)
        liftedBody
      return Soma.Core.Arm.mk arm.patterns closedBody
    return .case scruts' motive' arms'
  | .record fields =>
    let fields' ← fields.mapM fun (n, x) => do return (n, ← inlineIOBind x)
    return .record fields'
  | .recordUpdate base updates =>
    let updates' ← updates.mapM fun (n, x) => do return (n, ← inlineIOBind x)
    return .recordUpdate (← inlineIOBind base) updates'
  | .fieldAccess x f i =>
    return .fieldAccess (← inlineIOBind x) f i
  | .inject l args rty =>
    return .inject l (← args.mapM inlineIOBind) (← inlineIOBind rty)
  | .if_ c t el =>
    return .if_ (← inlineIOBind c) (← inlineIOBind t) (← inlineIOBind el)
  | .closure n caps ty =>
    return .closure n (← caps.mapM inlineIOBind) (← inlineIOBind ty)
  | .array es ety =>
    return .array (← es.mapM inlineIOBind) (← inlineIOBind ety)
  | .tuple es =>
    return .tuple (← es.mapM inlineIOBind)
  | .rowExtend l f t =>
    return .rowExtend (← inlineIOBind l) (← inlineIOBind f) (← inlineIOBind t)
  | .recordTy r => return .recordTy (← inlineIOBind r)
  | .variantTy r => return .variantTy (← inlineIOBind r)
  | .dataTy id ps =>
    return .dataTy id (← ps.mapM inlineIOBind)
  | .ann x t =>
    return .ann (← inlineIOBind x) (← inlineIOBind t)
  | _ => pure e

/-- Collect free variables with their type expressions from an expression tree -/
partial def collectFVarsWithTypes (e : Soma.Core.Expr) : HashMap Soma.Unique Soma.Core.Expr :=
  go e {}
where
  go (e : Soma.Core.Expr) (acc : HashMap Soma.Unique Soma.Core.Expr)
      : HashMap Soma.Unique Soma.Core.Expr :=
    match e with
    | .fvar u ty => go ty (acc.insert u ty)
    | .const _ ty => go ty acc
    | .bvar _ | .mvar _ | .sort _ | .rowSort
    | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
    | .lit _ | .tyvar _ _ => acc
    | .app f a => go a (go f acc)
    | .lam _ _ d b => go b (go d acc)
    | .let_ _ t v b => go b (go v (go t acc))
    | .pi _ _ _ d c => go c (go d acc)
    | .construct _ _ args rty => go rty (args.foldl (fun a e => go e a) acc)
    | .«case» scruts motive arms =>
      let acc := scruts.foldl (fun a e => go e a) acc
      let acc := go motive acc
      arms.foldl (fun a arm => go arm.body a) acc
    | .record fields => fields.foldl (fun a (_, e) => go e a) acc
    | .recordUpdate b us =>
      let acc := go b acc
      us.foldl (fun a (_, e) => go e a) acc
    | .fieldAccess x _ _ => go x acc
    | .inject _ args rty => go rty (args.foldl (fun a e => go e a) acc)
    | .if_ c t el => go el (go t (go c acc))
    | .closure _ caps ty => go ty (caps.foldl (fun a e => go e a) acc)
    | .array es ety => go ety (es.foldl (fun a e => go e a) acc)
    | .tuple es => es.foldl (fun a e => go e a) acc
    | .rowExtend l f t => go t (go f (go l acc))
    | .recordTy r => go r acc
    | .variantTy r => go r acc
    | .dataTy _ ps => ps.foldl (fun a e => go e a) acc
    | .ann x t => go t (go x acc)

/-- Collect free variables with their type expressions in deterministic first-occurrence order -/
partial def collectFVarsOrderedWithTypes (e : Soma.Core.Expr)
    : Array (Soma.Unique × Soma.Core.Expr) :=
  (go e ({} : HashSet Soma.Unique) #[]).2
where
  add (u : Soma.Unique) (ty : Soma.Core.Expr)
      (seen : HashSet Soma.Unique) (acc : Array (Soma.Unique × Soma.Core.Expr))
      : HashSet Soma.Unique × Array (Soma.Unique × Soma.Core.Expr) :=
    if seen.contains u then (seen, acc)
    else (seen.insert u, acc.push (u, ty))
  go (e : Soma.Core.Expr) (seen : HashSet Soma.Unique)
      (acc : Array (Soma.Unique × Soma.Core.Expr))
      : HashSet Soma.Unique × Array (Soma.Unique × Soma.Core.Expr) :=
    match e with
    | .fvar u ty =>
      let (seen, acc) := add u ty seen acc
      go ty seen acc
    | .const _ ty => go ty seen acc
    | .bvar _ | .mvar _ | .sort _ | .rowSort
    | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
    | .lit _ | .tyvar _ _ => (seen, acc)
    | .app f a =>
      let (seen, acc) := go f seen acc
      go a seen acc
    | .lam _ _ d b | .pi _ _ _ d b =>
      let (seen, acc) := go d seen acc
      go b seen acc
    | .let_ _ t v b =>
      let (seen, acc) := go t seen acc
      let (seen, acc) := go v seen acc
      go b seen acc
    | .construct _ _ args rty | .inject _ args rty =>
      let (seen, acc) := args.foldl
        (fun (seen, acc) e => go e seen acc) (seen, acc)
      go rty seen acc
    | .«case» scruts motive arms =>
      let (seen, acc) := scruts.foldl
        (fun (seen, acc) e => go e seen acc) (seen, acc)
      let (seen, acc) := go motive seen acc
      arms.foldl (fun (seen, acc) arm => go arm.body seen acc) (seen, acc)
    | .record fields =>
      fields.foldl (fun (seen, acc) (_, e) => go e seen acc) (seen, acc)
    | .recordUpdate b us =>
      let (seen, acc) := go b seen acc
      us.foldl (fun (seen, acc) (_, e) => go e seen acc) (seen, acc)
    | .fieldAccess x _ _ => go x seen acc
    | .if_ c t el =>
      let (seen, acc) := go c seen acc
      let (seen, acc) := go t seen acc
      go el seen acc
    | .closure _ caps ty =>
      let (seen, acc) := caps.foldl (fun (seen, acc) e => go e seen acc) (seen, acc)
      go ty seen acc
    | .tuple caps =>
      caps.foldl (fun (seen, acc) e => go e seen acc) (seen, acc)
    | .array es ety =>
      let (seen, acc) := es.foldl
        (fun (seen, acc) e => go e seen acc) (seen, acc)
      go ety seen acc
    | .rowExtend l f t =>
      let (seen, acc) := go l seen acc
      let (seen, acc) := go f seen acc
      go t seen acc
    | .recordTy r | .variantTy r => go r seen acc
    | .dataTy _ ps =>
      ps.foldl (fun (seen, acc) e => go e seen acc) (seen, acc)
    | .ann x t =>
      let (seen, acc) := go x seen acc
      go t seen acc

mutual

partial def liftCoreExpr (e : Soma.Core.Expr) : LiftM Soma.Core.Expr := do
  match e with
  | .fvar _ _ | .bvar _ | .mvar _ | .const _ _ | .sort _ | .rowSort
  | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .lit _
  | .tyvar _ _ =>
    pure e

  | .lam .. => liftLambdaChain e

  | .closure n caps ty => do
    let caps' ← caps.mapM (liftCoreExpr ·)
    let ty' ← liftCoreExpr ty
    pure (.closure n caps' ty')
  | .app fn arg => do
    pure (.app (← liftCoreExpr fn) (← liftCoreExpr arg))
  | .let_ n t v b => do
    let liftedT ← liftCoreExpr t
    let liftedV ← liftCoreExpr v
    let u ← LiftM.freshUnique n
    let openedB := Soma.Core.Expr.instantiate b (Soma.Core.Expr.fvar u liftedT)
    let liftedB ← liftCoreExpr openedB
    let closedB := Soma.Core.Expr.abstractFVar liftedB u
    pure (.let_ n liftedT liftedV closedB)
  | .pi q info n d c => do
    let d' ← liftCoreExpr d
    let u ← LiftM.freshUnique n
    let openedC := Soma.Core.Expr.instantiate c (Soma.Core.Expr.fvar u d')
    let liftedC ← liftCoreExpr openedC
    pure (.pi q info n d' (Soma.Core.Expr.abstractFVar liftedC u))
  | .construct n t args rty => do
    pure (.construct n t (← args.mapM (liftCoreExpr ·)) (← liftCoreExpr rty))
  | .«case» scruts motive arms => do
    let scruts' ← scruts.mapM (liftCoreExpr ·)
    let motive' ← liftCoreExpr motive
    let st ← get
    let scrutTypes := scruts'.map fun scrut =>
      Soma.Core.Expr.typeOf scrut st.globalEnv st.unfoldTy st.metas
    let arms' ← arms.mapM fun arm => do
      let bindings := collectArmBindingTypes st arm.patterns scrutTypes
      let openedBody := bindings.foldr
        (fun (uid, ty) body =>
          body.instantiate (.fvar uid (Soma.Core.quoteExpr ⟨0⟩ ty)))
        arm.body
      let liftedBody ← liftCoreExpr openedBody
      let closedBody := bindings.foldl
        (fun body (uid, _) => body.abstractFVar uid)
        liftedBody
      pure (Soma.Core.Arm.mk arm.patterns closedBody)
    pure (.«case» scruts' motive' arms')
  | .record fields => do
    let fields' ← fields.mapM fun (n, e') => do pure (n, ← liftCoreExpr e')
    pure (.record fields')
  | .recordUpdate base updates => do
    let base' ← liftCoreExpr base
    let updates' ← updates.mapM fun (n, e') => do pure (n, ← liftCoreExpr e')
    pure (.recordUpdate base' updates')
  | .fieldAccess x f i => do pure (.fieldAccess (← liftCoreExpr x) f i)
  | .inject l args rty => do pure (.inject l (← args.mapM (liftCoreExpr ·)) (← liftCoreExpr rty))
  | .if_ c t el => do
    pure (.if_ (← liftCoreExpr c) (← liftCoreExpr t)
               (← liftCoreExpr el))
  | .array es ety => do pure (.array (← es.mapM (liftCoreExpr ·)) (← liftCoreExpr ety))
  | .tuple es => do pure (.tuple (← es.mapM (liftCoreExpr ·)))
  | .rowExtend l f t => do
    pure (.rowExtend (← liftCoreExpr l) (← liftCoreExpr f)
                     (← liftCoreExpr t))
  | .recordTy r => do pure (.recordTy (← liftCoreExpr r))
  | .variantTy r => do pure (.variantTy (← liftCoreExpr r))
  | .dataTy id ps => do pure (.dataTy id (← ps.mapM (liftCoreExpr ·)))
  | .ann x t => do
    pure (.ann (← liftCoreExpr x) (← liftCoreExpr t))

/-- Lift a maximal chain of consecutive `.lam` binders as a single multi-argument top-level function -/
partial def liftLambdaChain (e : Soma.Core.Expr) : LiftM Soma.Core.Expr := do
  let mut chain : Array (Soma.Core.BinderInfo × String × Soma.Core.Expr × Soma.Unique) := #[]
  let mut current : Soma.Core.Expr := e
  let mut walking := true
  while walking do
    match current with
    | .lam info name domain body =>
      let preOpenU ← LiftM.freshUnique name
      let openedBody := Soma.Core.Expr.instantiate body
        (Soma.Core.Expr.fvar preOpenU domain)
      chain := chain.push (info, name, domain, preOpenU)
      current := openedBody
    | _ => walking := false

  let liftedBody ← liftCoreExpr current

  let chainFvarSet : Std.HashSet Soma.Unique :=
    chain.foldl (fun acc (_, _, _, u) => acc.insert u) {}
  let mut captures : Array (Soma.Unique × String × Soma.Core.Expr) := #[]
  for (fv, tyExpr) in collectFVarsOrderedWithTypes liftedBody do
    if chainFvarSet.contains fv then continue
    let isGlob ← LiftM.isGlobal ⟨fv⟩
    if isGlob then continue
    captures := captures.push (fv, fv.original, tyExpr)

  let mut captureParams : Array (Soma.Unique × String × Soma.Core.Expr) := #[]
  let mut renamedBody : Soma.Core.Expr := liftedBody
  for (oldU, capName, tyExpr) in captures do
    let newU ← LiftM.freshUnique capName
    captureParams := captureParams.push (newU, capName, tyExpr)
    renamedBody := Soma.Core.Expr.replaceFVar renamedBody oldU
      (Soma.Core.Expr.fvar newU tyExpr)

  let liftedName ← LiftM.freshLambdaName

  let st ← get
  let evalCtx : Soma.Core.EvalCtx :=
    { env := st.typeParamEnv, globals := st.globalEnv, metas := .empty }
  let captureValueTypes := captureParams.map fun (_, _, tyExpr) =>
    Soma.Core.evalCoreExpr evalCtx tyExpr
  let chainDomainValues := chain.map fun (_, _, dom, _) =>
    Soma.Core.evalCoreExpr evalCtx dom
  let bodyTyValue := Soma.Core.Expr.typeOf renamedBody st.globalEnv
    st.unfoldTy st.metas
  let liftedFnType :=
    buildFnType (captureValueTypes ++ chainDomainValues) bodyTyValue

  let bodyTyExpr := Soma.Core.quoteExpr ⟨0⟩ bodyTyValue
  let mut natTyExpr : Soma.Core.Expr := bodyTyExpr
  for i in [:chain.size] do
    let idx := chain.size - 1 - i
    let (info, name, domain, fvarU) := chain[idx]!
    natTyExpr := Soma.Core.Expr.abstractFVar natTyExpr fvarU
    natTyExpr := .pi Quantity.omega info name domain natTyExpr

  let captureBindings : Array (Soma.Unique × String) :=
    captureParams.map fun (u, n, _) => (u, n)
  let chainBindings : Array (Soma.Unique × String) :=
    chain.map fun (_, name, _, u) => (u, name)
  let allParams := captureBindings ++ chainBindings

  let liftedFn : TypedFunction := {
    name := liftedName
    params := allParams
    body := renamedBody
    fnType := liftedFnType
    closureInfo := some { capturedVars := captures.map fun (u, n, _) => (u, n) }
    attrs := {}
  }
  LiftM.addLiftedFunction liftedFn

  let captureExprs := captures.map fun (u, _, tyExpr) =>
    Soma.Core.Expr.fvar u tyExpr
  pure (Soma.Core.Expr.closure liftedName captureExprs natTyExpr)

end

/-- Walk past leading explicit-param Pi binders to find the remaining "result" type after `n` params are consumed -/
private partial def peelExplicitParams (ty : Value) (n : Nat) (st : LiftState) : Value :=
  match n, ty with
  | 0, _ => ty
  | _, _ =>
    let ty := st.unfoldTy ty
    match ty with
    | .vPi _ _ name dom cod =>
      let neutral := Value.vNeutral dom (.nVar ⟨name, ⟨0⟩⟩)
      let body := match cod with
        | .const _ v => v
        | .term _ _ _ => cod.applyPure neutral
      peelExplicitParams body (n - 1) st
    | _ => ty

/-- True iff `ty` is the wired-in `World` type (after unfolding aliases) -/
private def isWorldTyValue (ty : Value) (st : LiftState) : Bool :=
  let ty := st.unfoldTy ty
  match ty with
  | .vDataType uid _ => st.worldUnique?.any (· == uid)
  | _ => false

def liftTypedFunction (fn : TypedFunction) : LiftM TypedFunction := do
  let mut tyParamEnv : Soma.Core.Env := .empty
  let mut fnTy := fn.fnType
  let mut cont := true
  while cont do
    match fnTy with
    | .vPi _ binder name dom cod =>
      let isErasedImplicit := match binder with
        | .implicit | .strictImplicit =>
          match dom with
          | .vType _ | .vRowSort | .vLabelSort => true
          | _ => false
        | _ => false
      if isErasedImplicit then
        let neutral := Value.vNeutral dom (.nVar ⟨name, tyParamEnv.level⟩)
        tyParamEnv := tyParamEnv.extend name neutral
        fnTy := match cod with
          | .const _ body => body
          | .term _ _ _ => cod.applyPure neutral
      else
        cont := false
    | _ => cont := false
  modify fun st => { st with typeParamEnv := tyParamEnv }

  -- η-expand IO functions: if the function's body type (after consuming
  -- explicit params) unfolds to `World -> Pair World X`, add a synthetic `w`
  -- parameter and apply the body to it
  let st0 ← get
  let bodyTy := peelExplicitParams fnTy fn.params.size st0
  let needsEta : Bool :=
    match st0.unfoldTy bodyTy with
    | .vPi _ _ _ dom _ => isWorldTyValue dom st0
    | _ => false
  let (etaParams, etaBody) ← if needsEta then do
      let wName := "_w"
      let wId ← LiftM.freshUnique wName
      let wTyExpr : Soma.Core.Expr :=
        match st0.worldUnique? with
        | some uid => .dataTy uid #[]
        | none => .sort .zero
      let body' := applyPushingDown fn.body (.fvar wId wTyExpr)
      pure (fn.params ++ #[(wId, wName)], body')
    else
      pure (fn.params, fn.body)

  let inlinedBody ← inlineIOBind etaBody
  let coreBody' ← liftCoreExpr inlinedBody
  pure { fn with params := etaParams, body := coreBody' }

abbrev TypedFunctionMap := Std.HashMap String TypedFunction

def liftTypedFunctions (typedFunctions : TypedFunctionMap) (moduleName : String) (startId : Nat)
    (globalEnv : Soma.Core.GlobalEnv) (unfoldTy : Value → Value := id)
    (metas : Soma.Core.MetaState := .empty)
    (ioBindName? : Option QualifiedName := none)
    (pureIOName? : Option QualifiedName := none)
    (worldUnique? : Option Soma.Unique := none)
    (pairCtorName? : Option QualifiedName := none)
    (pairCtorTag : Nat := 0)
    (pairUnique? : Option Soma.Unique := none)
    (ctorTypes : ConstructorTypeRegistry := {})
    : TypedFunctionMap × Array TypedFunction := Id.run do
  let globalNames : HashSet QualifiedName := typedFunctions.fold (init := {}) fun acc _ fn =>
    acc.insert fn.name

  let (liftedFunctions, finalState) := LiftM.run (do
    let mut result : TypedFunctionMap := {}
    for (fnName, fn) in typedFunctions.toList do
      let fn' ← liftTypedFunction fn
      result := result.insert fnName fn'
    pure result
  ) moduleName globalNames startId globalEnv unfoldTy metas ioBindName? pureIOName?
    worldUnique? pairCtorName? pairCtorTag pairUnique? ctorTypes

  (liftedFunctions, finalState.liftedFunctions)

def liftAll (typedFunctions : TypedFunctionMap) (moduleName : String) (startId : Nat)
    (globalEnv : Soma.Core.GlobalEnv) (unfoldTy : Value → Value := id)
    (metas : Soma.Core.MetaState := .empty)
    (ioBindName? : Option QualifiedName := none)
    (pureIOName? : Option QualifiedName := none)
    (worldUnique? : Option Soma.Unique := none)
    (pairCtorName? : Option QualifiedName := none)
    (pairCtorTag : Nat := 0)
    (pairUnique? : Option Soma.Unique := none)
    (ctorTypes : ConstructorTypeRegistry := {})
    : TypedFunctionMap :=
  let (lifted, generated) :=
    liftTypedFunctions typedFunctions moduleName startId globalEnv
      unfoldTy metas ioBindName? pureIOName? worldUnique? pairCtorName? pairCtorTag pairUnique? ctorTypes
  generated.foldl (init := lifted) fun acc fn =>
    acc.insert fn.name.display fn

end Soma.Core.LambdaLift
