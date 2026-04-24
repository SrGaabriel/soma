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
    (pairUnique? : Option Soma.Unique := none) : α × LiftState :=
  StateT.run m { moduleName, globalNames, nextId := startId, globalEnv, unfoldTy, metas,
                 ioBindName?, pureIOName?, worldUnique?, pairCtorName?, pairCtorTag,
                 pairUnique? }

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
    return .lam info name (← inlineIOBind domain) (← inlineIOBind body)
  | .let_ name ty val body =>
    return .let_ name (← inlineIOBind ty) (← inlineIOBind val) (← inlineIOBind body)
  | .pi q info name dom cod =>
    return .pi q info name (← inlineIOBind dom) (← inlineIOBind cod)
  | .sigma q info name f s =>
    return .sigma q info name (← inlineIOBind f) (← inlineIOBind s)
  | .pair f s =>
    return .pair (← inlineIOBind f) (← inlineIOBind s)
  | .projFst x => return .projFst (← inlineIOBind x)
  | .projSnd x => return .projSnd (← inlineIOBind x)
  | .construct n t args rty =>
    return .construct n t (← args.mapM inlineIOBind) (← inlineIOBind rty)
  | .«case» scruts motive arms =>
    let scruts' ← scruts.mapM inlineIOBind
    let motive' ← inlineIOBind motive
    let arms' ← arms.mapM fun arm => do
      return Soma.Core.Arm.mk arm.patterns (← inlineIOBind arm.body)
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
  | .closure n caps =>
    return .closure n (← caps.mapM inlineIOBind)
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
  | .eqTy lv t l r =>
    return .eqTy lv (← inlineIOBind t) (← inlineIOBind l) (← inlineIOBind r)
  | .refl t x =>
    return .refl (← inlineIOBind t) (← inlineIOBind x)
  | .transport lv t m l r ep b =>
    return .transport lv (← inlineIOBind t) (← inlineIOBind m) (← inlineIOBind l)
      (← inlineIOBind r) (← inlineIOBind ep) (← inlineIOBind b)
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
    | .bvar _ | .mvar _ | .sort _ | .primTy _ | .rowSort
    | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _
    | .lit _ => acc
    | .app f a => go a (go f acc)
    | .lam _ _ d b => go b (go d acc)
    | .let_ _ t v b => go b (go v (go t acc))
    | .pi _ _ _ d c => go c (go d acc)
    | .sigma _ _ _ f s => go s (go f acc)
    | .pair f s => go s (go f acc)
    | .projFst x => go x acc
    | .projSnd x => go x acc
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
    | .closure _ caps => caps.foldl (fun a e => go e a) acc
    | .array es ety => go ety (es.foldl (fun a e => go e a) acc)
    | .tuple es => es.foldl (fun a e => go e a) acc
    | .rowExtend l f t => go t (go f (go l acc))
    | .recordTy r => go r acc
    | .variantTy r => go r acc
    | .dataTy _ ps => ps.foldl (fun a e => go e a) acc
    | .eqTy _ t l r => go r (go l (go t acc))
    | .refl t x => go x (go t acc)
    | .transport _ t m l r ep b =>
      go b (go ep (go r (go l (go m (go t acc)))))
    | .ann x t => go t (go x acc)

mutual

partial def liftCoreExpr (e : Soma.Core.Expr) : LiftM Soma.Core.Expr := do
  match e with
  | .fvar _ _ | .bvar _ | .mvar _ | .const _ _ | .sort _ | .primTy _ | .rowSort
  | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .lit _ =>
    pure e

  | .lam info name domain body => do
    let preOpenU ← LiftM.freshUnique name
    let preOpenedBody := Soma.Core.Expr.instantiate body
      (Soma.Core.Expr.fvar preOpenU domain)
    let body' ← liftCoreExpr preOpenedBody
    let closedBody' := Soma.Core.Expr.abstractFVar body' preOpenU
    let liftedLam : Soma.Core.Expr := Soma.Core.Expr.lam info name domain closedBody'

    let fvarTypes := collectFVarsWithTypes liftedLam

    let fvarSet := Soma.Core.Expr.collectFVars liftedLam

    let mut captures : Array (Soma.Unique × String × Soma.Core.Expr) := #[]
    for fv in fvarSet do
      let isGlob ← LiftM.isGlobal ⟨fv⟩
      if !isGlob then
        let tyExpr := fvarTypes.get? fv |>.getD (.sort .zero)
        captures := captures.push (fv, fv.original, tyExpr)

    let mut captureParams : Array (Soma.Unique × String × Soma.Core.Expr) := #[]
    let mut replacements : Array (Soma.Unique × Soma.Unique × Soma.Core.Expr) := #[]
    for (oldU, capName, tyExpr) in captures do
      let newU ← LiftM.freshUnique capName
      captureParams := captureParams.push (newU, capName, tyExpr)
      replacements := replacements.push (oldU, newU, tyExpr)

    -- Replace old fvars with new ones in the lambda body
    let mut substituted : Soma.Core.Expr := liftedLam
    for (oldU, newU, tyExpr) in replacements do
      substituted := Soma.Core.Expr.replaceFVar substituted oldU
        (Soma.Core.Expr.fvar newU tyExpr)

    -- Extract the lambda binder into an explicit param
    let lamParamUnique ← LiftM.freshUnique name

    let innerBody : Soma.Core.Expr := match substituted with
      | .lam _ _ _ b => b
      | other => other

    -- Open the binder: replace bvar(0) with fvar(lamParamUnique)
    let openedBody := Soma.Core.Expr.instantiate innerBody
      (Soma.Core.Expr.fvar lamParamUnique domain)

    let liftedName ← LiftM.freshLambdaName

    let captureBindings : Array (Soma.Unique × String) := captureParams.map fun (u, n, _) =>
      (u, n)
    let lamParamBinding := lamParamUnique
    let allParams := captureBindings ++ #[(lamParamBinding, name)]

    let st ← get
    let genv := st.globalEnv
    let tyParamEnv := st.typeParamEnv
    let evalCtx : Soma.Core.EvalCtx := { env := tyParamEnv, globals := genv, metas := .empty }
    let captureValueTypes := captureParams.map fun (_, _, tyExpr) => Soma.Core.evalCoreExpr evalCtx tyExpr
    let domainTy := Soma.Core.evalCoreExpr evalCtx domain
    let bodyTy := Soma.Core.Expr.typeOf openedBody genv (← get).unfoldTy (← get).metas
    let allParamTypes := captureValueTypes ++ #[domainTy]
    let liftedFnType := buildFnType allParamTypes bodyTy

    let liftedFn : TypedFunction := {
      name := liftedName
      params := allParams
      body := openedBody
      fnType := liftedFnType
      closureInfo := some { capturedVars := captures.map fun (u, n, _) => (u, n) }
      attrs := {}
    }
    LiftM.addLiftedFunction liftedFn

    let captureExprs := captures.map fun (u, _, tyExpr) =>
      Soma.Core.Expr.fvar u tyExpr
    pure (Soma.Core.Expr.closure liftedName captureExprs)

  | .closure n caps => do
    let caps' ← caps.mapM (liftCoreExpr ·)
    pure (.closure n caps')
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
    pure (.pi q info n (← liftCoreExpr d) (← liftCoreExpr c))
  | .sigma q info n f s => do
    pure (.sigma q info n (← liftCoreExpr f) (← liftCoreExpr s))
  | .pair f s => do
    pure (.pair (← liftCoreExpr f) (← liftCoreExpr s))
  | .projFst x => do pure (.projFst (← liftCoreExpr x))
  | .projSnd x => do pure (.projSnd (← liftCoreExpr x))
  | .construct n t args rty => do
    pure (.construct n t (← args.mapM (liftCoreExpr ·)) (← liftCoreExpr rty))
  | .«case» scruts motive arms => do
    let scruts' ← scruts.mapM (liftCoreExpr ·)
    let arms' ← arms.mapM fun arm => do
      let bindingIds := arm.patterns.foldl
        (fun acc p => acc ++ p.collectBindingIds) #[]
      let mut openedBody := arm.body
      let mut freshIds : Array Soma.Unique := #[]
      for uid in bindingIds.reverse do
        let freshU ← LiftM.freshUnique uid.original
        freshIds := freshIds.push freshU
        openedBody := openedBody.instantiate (.fvar freshU (.sort (.lit 0)))
      let liftedBody ← liftCoreExpr openedBody
      let closedBody := freshIds.reverse.foldl
        (fun body u => body.abstractFVar u) liftedBody
      pure (Soma.Core.Arm.mk arm.patterns closedBody)
    pure (.«case» scruts' motive arms')
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
  | .eqTy lv t l r => do
    pure (.eqTy lv (← liftCoreExpr t) (← liftCoreExpr l)
                    (← liftCoreExpr r))
  | .refl t x => do
    pure (.refl (← liftCoreExpr t) (← liftCoreExpr x))
  | .transport lv t m l r ep b => do
    pure (.transport lv (← liftCoreExpr t) (← liftCoreExpr m)
                     (← liftCoreExpr l) (← liftCoreExpr r)
                     (← liftCoreExpr ep) (← liftCoreExpr b))
  | .ann x t => do
    pure (.ann (← liftCoreExpr x) (← liftCoreExpr t))

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
  | .vPrimTy .world => true
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
      let wTyExpr : Soma.Core.Expr := .primTy .world
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
    worldUnique? pairCtorName? pairCtorTag pairUnique?

  (liftedFunctions, finalState.liftedFunctions)

def liftAll (typedFunctions : TypedFunctionMap) (moduleName : String) (startId : Nat)
    (globalEnv : Soma.Core.GlobalEnv) (unfoldTy : Value → Value := id)
    (metas : Soma.Core.MetaState := .empty)
    (ioBindName? : Option QualifiedName := none)
    (pureIOName? : Option QualifiedName := none)
    (worldUnique? : Option Soma.Unique := none)
    (pairCtorName? : Option QualifiedName := none)
    (pairCtorTag : Nat := 0)
    (pairUnique? : Option Soma.Unique := none) : TypedFunctionMap :=
  let (lifted, generated) := liftTypedFunctions typedFunctions moduleName startId globalEnv
    unfoldTy metas ioBindName? pureIOName? worldUnique? pairCtorName? pairCtorTag pairUnique?
  generated.foldl (init := lifted) fun acc fn =>
    acc.insert fn.name.display fn

end Soma.Core.LambdaLift
