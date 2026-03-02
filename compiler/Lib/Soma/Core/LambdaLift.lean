import Soma.Core.Function
import Soma.Core.Module
import Soma.Core.Value
import Soma.Core.Expr
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
  deriving Inhabited

abbrev LiftM := StateM LiftState

namespace LiftM

def run (m : LiftM α) (moduleName : String) (globalNames : HashSet QualifiedName) : α × LiftState :=
  StateT.run m { moduleName, globalNames }

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

def defaultTy : Value := Value.vType Soma.Core.Level.zero

def buildFnType (paramTypes : Array Value) (resultType : Value) : Value :=
  paramTypes.foldr (init := resultType) fun paramTy acc =>
    Value.vPi Soma.Core.Quantity.omega Soma.Core.BinderInfo.explicit "_" paramTy
      (Soma.Core.Closure.const "_" acc)

mutual

partial def liftCoreExpr (e : Soma.Core.Expr) : LiftM Soma.Core.Expr := do
  match e with
  | .fvar _ _ | .bvar _ | .mvar _ | .const _ _ | .sort _ | .primTy _ | .rowSort
  | .labelSort | .rowEmpty | .labelLit _ | .panic _ | .proj _ _ _ | .lit _ =>
    pure e

  | .lam info name domain body => do
    let body' ← liftCoreExpr body
    let liftedLam : Soma.Core.Expr := Soma.Core.Expr.lam info name domain body'
    let fvars := Soma.Core.Expr.collectFVars liftedLam

    -- Filter out globals
    let mut captures : Array (Soma.Unique × String × Value) := #[]
    for fv in fvars do
      let isGlob ← LiftM.isGlobal ⟨fv⟩
      if !isGlob then
        captures := captures.push (fv, fv.original, defaultTy)

    -- Generate fresh fvars for capture parameters
    let mut captureParams : Array (Soma.Unique × String × Value) := #[]
    let mut replacements : Array (Soma.Unique × Soma.Unique) := #[]
    for (oldU, capName, ty) in captures do
      let newU ← LiftM.freshUnique capName
      captureParams := captureParams.push (newU, capName, ty)
      replacements := replacements.push (oldU, newU)

    -- Replace old fvars with new ones in the lambda body
    let mut substituted : Soma.Core.Expr := liftedLam
    for (oldU, newU) in replacements do
      substituted := Soma.Core.Expr.replaceFVar substituted oldU (Soma.Core.Expr.fvar newU (.sort .zero))

    -- Extract the lambda binder into an explicit param
    let lamParamUnique ← LiftM.freshUnique name

    let innerBody : Soma.Core.Expr := match substituted with
      | .lam _ _ _ b => b
      | other => other

    -- Open the binder: replace bvar(0) with fvar(lamParamUnique)
    let openedBody := Soma.Core.Expr.instantiate innerBody (Soma.Core.Expr.fvar lamParamUnique (.sort .zero))

    let liftedName ← LiftM.freshLambdaName

    let captureBindings : Array (Soma.Unique × String) := captureParams.map fun (u, n, _) =>
      (u, n)
    let lamParamBinding := lamParamUnique
    let allParams := captureBindings ++ #[(lamParamBinding, name)]
    let allParamTypes := captureParams.map (·.2.2) ++ #[defaultTy]
    let liftedFnType := buildFnType allParamTypes defaultTy

    let liftedFn : TypedFunction := {
      name := liftedName
      params := allParams
      body := openedBody
      fnType := liftedFnType
      closureInfo := some { capturedVars := captures.map fun (u, n, _) => (u, n) }
      attrs := {}
    }
    LiftM.addLiftedFunction liftedFn

    let captureExprs := captures.map fun (u, _, _) => Soma.Core.Expr.fvar u (.sort .zero)
    pure (Soma.Core.Expr.closure liftedName captureExprs)

  | .closure n caps => do
    let caps' ← caps.mapM (liftCoreExpr ·)
    pure (.closure n caps')
  | .app fn arg => do
    pure (.app (← liftCoreExpr fn) (← liftCoreExpr arg))
  | .let_ n t v b => do
    pure (.let_ n (← liftCoreExpr t) (← liftCoreExpr v)
                   (← liftCoreExpr b))
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
      pure (Soma.Core.Arm.mk arm.patterns (← liftCoreExpr arm.body))
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
  let coreBody' ← liftCoreExpr fn.body
  pure { fn with body := coreBody' }

abbrev TypedFunctionMap := Std.HashMap String TypedFunction

def liftTypedFunctions (typedFunctions : TypedFunctionMap) (moduleName : String)
    : TypedFunctionMap × Array TypedFunction := Id.run do
  let globalNames : HashSet QualifiedName := typedFunctions.fold (init := {}) fun acc _ fn =>
    acc.insert fn.name

  let (liftedFunctions, finalState) := LiftM.run (do
    let mut result : TypedFunctionMap := {}
    for (fnName, fn) in typedFunctions.toList do
      let fn' ← liftTypedFunction fn
      result := result.insert fnName fn'
    pure result
  ) moduleName globalNames

  (liftedFunctions, finalState.liftedFunctions)

def liftAll (typedFunctions : TypedFunctionMap) (moduleName : String) : TypedFunctionMap :=
  let (lifted, generated) := liftTypedFunctions typedFunctions moduleName
  generated.foldl (init := lifted) fun acc fn =>
    acc.insert fn.name.display fn

end Soma.Core.LambdaLift
