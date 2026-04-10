import Soma.Core.Function
import Soma.Core.Module
import Soma.Core.Value
import Soma.Core.Expr
import Soma.Core.Eval
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
  deriving Inhabited

abbrev LiftM := StateM LiftState

namespace LiftM

def run (m : LiftM α) (moduleName : String) (globalNames : HashSet QualifiedName)
    (startId : Nat := 0) (globalEnv : Soma.Core.GlobalEnv := .empty)
    (unfoldTy : Value → Value := id)
    (metas : Soma.Core.MetaState := .empty) : α × LiftState :=
  StateT.run m { moduleName, globalNames, nextId := startId, globalEnv, unfoldTy, metas }

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
    | .«case» scruts arms rty =>
      let acc := scruts.foldl (fun a e => go e a) acc
      let acc := arms.foldl (fun a arm => go arm.body a) acc
      go rty acc
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
  | .«case» scruts arms rty => do
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
    pure (.«case» scruts' arms' (← liftCoreExpr rty))
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

/-! ## Function and Module Lifting -/

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
  let coreBody' ← liftCoreExpr fn.body
  pure { fn with body := coreBody' }

abbrev TypedFunctionMap := Std.HashMap String TypedFunction

def liftTypedFunctions (typedFunctions : TypedFunctionMap) (moduleName : String) (startId : Nat)
    (globalEnv : Soma.Core.GlobalEnv) (unfoldTy : Value → Value := id)
    (metas : Soma.Core.MetaState := .empty)
    : TypedFunctionMap × Array TypedFunction := Id.run do
  let globalNames : HashSet QualifiedName := typedFunctions.fold (init := {}) fun acc _ fn =>
    acc.insert fn.name

  let (liftedFunctions, finalState) := LiftM.run (do
    let mut result : TypedFunctionMap := {}
    for (fnName, fn) in typedFunctions.toList do
      let fn' ← liftTypedFunction fn
      result := result.insert fnName fn'
    pure result
  ) moduleName globalNames startId globalEnv unfoldTy metas

  (liftedFunctions, finalState.liftedFunctions)

def liftAll (typedFunctions : TypedFunctionMap) (moduleName : String) (startId : Nat)
    (globalEnv : Soma.Core.GlobalEnv) (unfoldTy : Value → Value := id)
    (metas : Soma.Core.MetaState := .empty) : TypedFunctionMap :=
  let (lifted, generated) := liftTypedFunctions typedFunctions moduleName startId globalEnv unfoldTy metas
  generated.foldl (init := lifted) fun acc fn =>
    acc.insert fn.name.display fn

end Soma.Core.LambdaLift
