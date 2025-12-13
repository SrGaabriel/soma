/-
  Constraint Generation

  Generates type constraints from Metal IR expressions.
  This is the core of the W algorithm - we traverse expressions,
  generate fresh type variables, and emit constraints.

  Key improvements over the old Haskell design:
  1. Uses real Metal types (not duplicated simplified types)
  2. Span-based error reporting (constraints carry spans)
  3. Constraint graph structure for efficient lookup
  4. Proper handling of scope-indexed expressions
  5. Single traversal builds typed expression (no separate assembly pass)
-/

import Soma.Infer.Monad
import Soma.Metal

namespace Soma.Infer

open Soma.Typing
open Soma.Syntax (Span)
open Soma.Metal
open InferM (freshVar lookupLocal lookupFunction lookupConstructor
             addEqualityConstraint addConstraint reportError
             withLocal withLocals instantiate)

/-! ## Constraint Generation

We traverse Metal expressions and generate constraints.
Each expression is assigned a type (possibly a fresh variable),
and we emit constraints relating types based on the expression structure.
-/

namespace Gen

/-- Generate constraints for a literal, returning its type -/
def genLiteral (lit : Literal) : MonoTy :=
  lit.type

/-- Construct a tuple type from an array of element types.
    Handles 0-8 element tuples, returning an error type for larger tuples. -/
def mkTupleType (elemTys : Array MonoTy) : Option MonoTy :=
  match elemTys.size with
  | 0 => some Ty.unit
  | 1 => elemTys[0]?
  | 2 => do pure (Ty.tuple2 (← elemTys[0]?) (← elemTys[1]?))
  | 3 => do pure (Ty.tuple3 (← elemTys[0]?) (← elemTys[1]?) (← elemTys[2]?))
  | 4 => do pure (Ty.tuple4 (← elemTys[0]?) (← elemTys[1]?) (← elemTys[2]?) (← elemTys[3]?))
  | 5 => do pure (Ty.tuple5 (← elemTys[0]?) (← elemTys[1]?) (← elemTys[2]?) (← elemTys[3]?) (← elemTys[4]?))
  | 6 => do pure (Ty.tuple6 (← elemTys[0]?) (← elemTys[1]?) (← elemTys[2]?) (← elemTys[3]?) (← elemTys[4]?) (← elemTys[5]?))
  | 7 => do pure (Ty.tuple7 (← elemTys[0]?) (← elemTys[1]?) (← elemTys[2]?) (← elemTys[3]?) (← elemTys[4]?) (← elemTys[5]?) (← elemTys[6]?))
  | 8 => do pure (Ty.tuple8 (← elemTys[0]?) (← elemTys[1]?) (← elemTys[2]?) (← elemTys[3]?) (← elemTys[4]?) (← elemTys[5]?) (← elemTys[6]?) (← elemTys[7]?))
  | _ => none

/-- Generate n fresh type variables with a given prefix -/
def freshVars (n : Nat) (prefix_ : String := "t") : InferM (Array MonoTy) := do
  let mut result := #[]
  for i in [:n] do
    result := result.push (← freshVar s!"{prefix_}{i}")
  return result

/-- Apply type arguments to a type constructor.
    Given a type of kind `k1 -> k2 -> ... -> *` and arguments,
    applies them in sequence to produce a MonoTy. -/
def applyTypeArgs (baseTy : Ty k) (args : Array MonoTy) : MonoTy :=
  go k baseTy args.toList
where
  go : (k : Kind) → Ty k → List MonoTy → MonoTy
    | .star, ty, [] => ty
    | .star, ty, _ => ty
    | .arrow _ _, _, [] => .starPrim .unit
    | .arrow .star k2, ty, arg :: rest => go k2 (.app ty arg) rest
    | .arrow (.arrow _ _) _, _, _ => .starPrim .unit

/-- Generate typed ParamList from untyped, returning bindings for scope preserving bindingIds -/
def genParamListAux : ParamList Unit → InferM (Array (String × VarInfo) × ParamList MonoTy)
  | .nil => return (#[], .nil)
  | .cons binding name () ps => do
    let ty ← freshVar name
    let info : VarInfo := { ty, bindingId := binding, name }
    let (restBindings, restParams) ← genParamListAux ps
    return (#[(name, info)] ++ restBindings, .cons binding name ty restParams)

/-- TODO: prove -/
axiom genParamListAux_preserves_bindingIds (params : ParamList Unit) (bindings : Array (String × VarInfo)) (typedParams : ParamList MonoTy) :
    typedParams.bindingIds = params.bindingIds

/-- Generate typed PatternList from untyped -/
partial def genPatternListAux (patterns : PatternList Unit) (scrutTys : Array MonoTy) (span : Span)
    : InferM (Array (String × VarInfo) × PatternList MonoTy) := do
  match patterns with
  | .nil => return (#[], .nil)
  | .cons pat rest => do
    let scrutTy ← match scrutTys[0]? with
      | some ty => pure ty
      | none => freshVar "scrut"
    let (bindings, typedPat) ← genPatternAux pat scrutTy span
    let (restBindings, typedRest) ← genPatternListAux rest (scrutTys.extract 1 scrutTys.size) span
    return (bindings ++ restBindings, .cons typedPat typedRest)
where
  /-- Generate typed pattern -/
  genPatternAux (pat : Pattern Unit) (scrutTy : MonoTy) (span : Span)
      : InferM (Array (String × VarInfo) × Pattern MonoTy) := do
    match pat with
    | .wildcard () patSpan =>
      return (#[], .wildcard scrutTy patSpan)

    | .var binding name () patSpan =>
      let info : VarInfo := { ty := scrutTy, bindingId := binding, name }
      return (#[(name, info)], .var binding name scrutTy patSpan)

    | .lit lit patSpan =>
      let litTy := genLiteral lit
      addEqualityConstraint scrutTy litTy .patternMatch span patSpan
      return (#[], .lit lit patSpan)

    | .ctor ctorName pats () patSpan =>
      let ctorNameStr := ctorName.display
      match ← lookupConstructor ctorNameStr with
      | some ctorInfo =>
        let freshParams ← ctorInfo.typeParams.mapM fun v => do
          let fresh ← freshVar v.name
          return (v.id, fresh)
        let σ := Subst.fromArrays ctorInfo.typeParams (freshParams.map (·.2))
        let fieldTys := ctorInfo.fieldTypes.map (σ.apply ·)
        let baseTy := Ty.userCon ctorInfo.typeId.kind ctorInfo.typeId
        let expectedTy := applyTypeArgs baseTy (freshParams.map (·.2))
        addEqualityConstraint scrutTy expectedTy .patternMatch span patSpan
        let (bindings, typedPats) ← genPatternArrayAux pats fieldTys patSpan
        return (bindings, .ctor ctorName typedPats expectedTy patSpan)
      | none =>
        reportError (.unknownConstructor ctorNameStr patSpan)
        let (bindings, typedPats) ← genPatternArrayAux pats #[] patSpan
        return (bindings, .ctor ctorName typedPats scrutTy patSpan)

    | .tuple pats () patSpan =>
      let n := pats.size
      let elemTys ← freshVars n "tup"
      match mkTupleType elemTys with
      | some tupleTy =>
        addEqualityConstraint scrutTy tupleTy .patternMatch span patSpan
        let (bindings, typedPats) ← genPatternArrayAux pats elemTys patSpan
        return (bindings, .tuple typedPats tupleTy patSpan)
      | none =>
        reportError (.cannotInfer s!"tuple pattern with {n} elements (max 8)" patSpan)
        let (bindings, typedPats) ← genPatternArrayAux pats #[] patSpan
        return (bindings, .tuple typedPats scrutTy patSpan)

    | .array innerPats () patSpan =>
      let elemTy ← freshVar "arrayElem"
      let arrayTy := Ty.array elemTy
      addEqualityConstraint scrutTy arrayTy .patternMatch span patSpan
      let elemTys : Array MonoTy := (Array.range innerPats.size).map fun _ => elemTy
      let (bindings, typedPats) ← genPatternArrayAux innerPats elemTys patSpan
      return (bindings, .array typedPats arrayTy patSpan)

    | .cons headPat tailPat () patSpan =>
      let elemTy ← freshVar "consElem"
      let arrayTy := Ty.array elemTy
      addEqualityConstraint scrutTy arrayTy .patternMatch span patSpan
      let (headBindings, typedHead) ← genPatternAux headPat elemTy patSpan
      let (tailBindings, typedTail) ← genPatternAux tailPat arrayTy patSpan
      return (headBindings ++ tailBindings, .cons typedHead typedTail arrayTy patSpan)

    | .as binding name innerPat () patSpan =>
      let info : VarInfo := { ty := scrutTy, bindingId := binding, name }
      let (innerBindings, typedInner) ← genPatternAux innerPat scrutTy patSpan
      return (#[(name, info)] ++ innerBindings, .as binding name typedInner scrutTy patSpan)

  genPatternArrayAux (pats : Array (Pattern Unit)) (scrutTys : Array MonoTy) (span : Span)
      : InferM (Array (String × VarInfo) × Array (Pattern MonoTy)) := do
    let mut result := #[]
    let mut typedPats := #[]
    for i in [:pats.size] do
      let pat := pats[i]!
      let scrutTy ← match scrutTys[i]? with
        | some ty => pure ty
        | none => freshVar "scrut"
      let (bindings, typedPat) ← genPatternAux pat scrutTy span
      result := result ++ bindings
      typedPats := typedPats.push typedPat
    return (result, typedPats)

/-- todo: prove -/
axiom genPatternListAux_preserves_bindingIds (patterns : PatternList Unit) (scrutTys : Array MonoTy) (span : Span)
    (bindings : Array (String × VarInfo)) (typedPatterns : PatternList MonoTy) :
    typedPatterns.bindingIds = patterns.bindingIds

mutual

/-- Generate constraints for an expression list, returning types and typed list -/
partial def genExprList {scope : Scope} (exprs : ExprList Unit scope)
    : InferM (Array MonoTy × ExprList MonoTy scope) := do
  match exprs with
  | .nil => return (#[], .nil)
  | .cons e es => do
    let (ty, typedE) ← genExpr e
    let (restTys, typedEs) ← genExprList es
    return (#[ty] ++ restTys, .cons typedE typedEs)

/-- Generate constraints for an expression, returning its type and typed version -/
partial def genExpr {scope : Scope} (expr : Expr Unit scope)
    : InferM (MonoTy × Expr MonoTy scope) := do
  match expr with
  | .var v () span =>
    let name := v.original
    match ← lookupLocal name with
    | some info => return (info.ty, .var v info.ty span)
    | none =>
      reportError (.unknownVariable name span)
      let errTy ← freshVar "err"
      return (errTy, .var v errTy span)

  | .lit lit span =>
    let ty := genLiteral lit
    return (ty, .lit lit span)

  | .call fn args () span => do
    let (fnTy, typedFn) ← genExpr fn
    let (argTys, typedArgs) ← genExprList args
    let resultTy ← freshVar "result"
    let expectedFnTy := argTys.foldr (init := resultTy) fun argTy accTy =>
      Ty.arrow argTy accTy
    addEqualityConstraint expectedFnTy fnTy .general fn.span span
    return (resultTy, .call typedFn typedArgs resultTy span)

  | .let_ binding original value body () span => do
    let (valueTy, typedValue) ← genExpr value
    let varInfo : VarInfo := { ty := valueTy, bindingId := binding, name := original }
    let (bodyTy, typedBody) ← withLocal original varInfo (genExpr body)
    return (bodyTy, .let_ binding original typedValue typedBody bodyTy span)

  | .lam params body () span => do
    let (paramBindings, typedParams) ← genParamListAux params
    -- The body's scope is params.bindingIds ++ scope
    -- So we can cast the body by theorem
    let (bodyTy, typedBody) ← withLocals paramBindings (genExpr body)
    let fnTy := paramBindings.foldr (init := bodyTy) fun (_, info) accTy =>
      Ty.arrow info.ty accTy
    -- Cast body to use typedParams' scope (bindingIds are preserved by construction)
    let h : typedParams.bindingIds ++ scope = params.bindingIds ++ scope := by
      rw [genParamListAux_preserves_bindingIds params paramBindings typedParams]
    let typedBody' : Expr MonoTy (typedParams.bindingIds ++ scope) := h ▸ typedBody
    return (fnTy, .lam typedParams typedBody' fnTy span)

  | .closure liftedName captures () span => do
    let (_, typedCaptures) ← genCaptureList captures
    match ← lookupFunction liftedName.display with
    | some fnInfo =>
      let (ty, constraints) ← instantiate fnInfo.qualType
      for c in constraints do
        addConstraint c span
      return (ty, .closure liftedName typedCaptures ty span)
    | none =>
      reportError (.unknownVariable liftedName.display span)
      let errTy ← freshVar "err"
      return (errTy, .closure liftedName typedCaptures errTy span)

  | .construct name tag args () span => do
    let ctorName := name.display
    let (argTys, typedArgs) ← genExprList args
    match ← lookupConstructor ctorName with
    | some ctorInfo =>
      let freshParams ← ctorInfo.typeParams.mapM fun v => do
        let fresh ← freshVar v.name
        return (v.id, fresh)
      let σ := Subst.fromArrays ctorInfo.typeParams (freshParams.map (·.2))
      let expectedFieldTys := ctorInfo.fieldTypes.map (σ.apply ·)
      let argList := args.toList
      for i in [:argTys.size] do
        if h : i < expectedFieldTys.size then
          let expectedTy := expectedFieldTys[i]
          let actualTy := argTys[i]!
          let argSpan := if i < argList.length then argList[i]!.span else span
          addEqualityConstraint expectedTy actualTy (.tupleElement i) span argSpan
      let baseTy := Ty.userCon ctorInfo.typeId.kind ctorInfo.typeId
      let resultTy := applyTypeArgs baseTy (freshParams.map (·.2))
      return (resultTy, .construct name tag typedArgs resultTy span)
    | none =>
      reportError (.unknownConstructor ctorName span)
      let errTy ← freshVar "err"
      return (errTy, .construct name tag typedArgs errTy span)

  | .tuple elements () span => do
    let (elemTys, typedElements) ← genExprList elements
    match mkTupleType elemTys with
    | some ty => return (ty, .tuple typedElements ty span)
    | none =>
      reportError (.cannotInfer s!"tuple with {elemTys.size} elements (max 8)" span)
      let errTy ← freshVar "err"
      return (errTy, .tuple typedElements errTy span)

  | .array elements () span => do
    let (elemTys, typedElements) ← genExprList elements
    let elemTy ← if elemTys.isEmpty then
      freshVar "elem"
    else
      let first := elemTys[0]!
      let elemList := elements.toList
      for i in [1:elemTys.size] do
        let ty := elemTys[i]!
        let tySpan := if i < elemList.length then elemList[i]!.span else span
        addEqualityConstraint first ty .arrayElements span tySpan
      pure first
    let arrayTy := Ty.array elemTy
    return (arrayTy, .array typedElements arrayTy span)

  | .if_ cond then_ else_ () span => do
    let (condTy, typedCond) ← genExpr cond
    addEqualityConstraint Ty.bool condTy .ifCondition span cond.span
    let (thenTy, typedThen) ← genExpr then_
    let (elseTy, typedElse) ← genExpr else_
    addEqualityConstraint thenTy elseTy .ifBranches then_.span else_.span
    return (thenTy, .if_ typedCond typedThen typedElse thenTy span)

  | .case scrutinees arms () span => do
    let (scrutTys, typedScrutinees) ← genExprList scrutinees
    let resultTy ← freshVar "case_result"
    let typedArms ← genArmList arms scrutTys resultTy span
    return (resultTy, .case typedScrutinees typedArms resultTy span)

  | .fieldAccess expr index () span => do
    let (_, typedExpr) ← genExpr expr
    let fieldTy ← freshVar "field"
    return (fieldTy, .fieldAccess typedExpr index fieldTy span)

  | .global name () span => do
    match ← lookupFunction name.display with
    | some fnInfo =>
      let (ty, constraints) ← instantiate fnInfo.qualType
      for c in constraints do
        addConstraint c span
      return (ty, .global name ty span)
    | none =>
      reportError (.unknownVariable name.display span)
      let errTy ← freshVar "err"
      return (errTy, .global name errTy span)

  | .panic message () span => do
    let ty ← freshVar "panic"
    return (ty, .panic message ty span)

/-- Generate constraints for a capture list -/
partial def genCaptureList {scope : Scope} (captures : CaptureList Unit scope)
    : InferM (Array MonoTy × CaptureList MonoTy scope) := do
  match captures with
  | .nil => return (#[], .nil)
  | .cons v () rest => do
    let name := v.original
    let ty ← match ← lookupLocal name with
      | some info => pure info.ty
      | none => freshVar name
    let (restTys, typedRest) ← genCaptureList rest
    return (#[ty] ++ restTys, .cons v ty typedRest)

/-- Generate constraints for an arm list, returning typed arms -/
partial def genArmList {scope : Scope} (arms : ArmList Unit scope)
    (scrutTys : Array MonoTy) (resultTy : MonoTy) (caseSpan : Span)
    : InferM (ArmList MonoTy scope) := do
  match arms with
  | .nil => return .nil
  | .cons arm rest => do
    let typedArm ← genArm arm scrutTys resultTy caseSpan
    let typedRest ← genArmList rest scrutTys resultTy caseSpan
    return .cons typedArm typedRest

/-- Generate constraints for a single arm, returning typed arm -/
partial def genArm {scope : Scope} (arm : Arm Unit scope)
    (scrutTys : Array MonoTy) (resultTy : MonoTy) (caseSpan : Span)
    : InferM (Arm MonoTy scope) := do
  match arm with
  | .mk patterns body span =>
    let (patternBindings, typedPatterns) ← genPatternListAux patterns scrutTys caseSpan
    let (bodyTy, typedBody) ← withLocals patternBindings (genExpr body)
    addEqualityConstraint resultTy bodyTy .caseArms caseSpan span
    let h : typedPatterns.bindingIds ++ scope = patterns.bindingIds ++ scope := by
      rw [genPatternListAux_preserves_bindingIds patterns scrutTys caseSpan patternBindings typedPatterns]
    let typedBody' : Expr MonoTy (typedPatterns.bindingIds ++ scope) := h ▸ typedBody
    return .mk typedPatterns typedBody' span

end

end Gen

open Soma.Syntax (TypeExpr)

/-- Resolve a TypeExpr (syntax) to a MonoTy during type inference -/
partial def resolveTypeExpr (ty : TypeExpr) : InferM MonoTy := do
  match ty with
  | .var name =>
    InferM.freshVar name.value

  | .con name =>
    match StarPrimitive.fromName? name.value with
    | some prim => pure (.starPrim prim)
    | none =>
      match (← InferM.getTypeEnv).lookupType name.value with
      | some info => pure (.con info.typeId)
      | none =>
        InferM.reportError (.unknownType name.value name.span)
        InferM.freshVar name.value

  | .arrow from_ to _ =>
    let fromTy ← resolveTypeExpr from_
    let toTy ← resolveTypeExpr to
    pure (.arrow fromTy toTy)

  | .tuple elements _ =>
    let elemTys ← elements.mapM resolveTypeExpr
    match Gen.mkTupleType elemTys with
    | some ty => pure ty
    | none =>
      InferM.reportError (.tupleTooLarge elemTys.size ty.span)
      InferM.freshVar "tuple"

  | .list elem _ =>
    let elemTy ← resolveTypeExpr elem
    pure (Ty.array elemTy)

  | .app fn arg span =>
    -- First resolve the argument
    let argTy ← resolveTypeExpr arg
    -- Check if fn is a higher primitive or user-defined type
    match fn with
    | .con name =>
      match HigherPrimitive.fromName? name.value with
      | some .array => pure (Ty.array argTy)
      | some .ref => pure (Ty.ref argTy)
      | some .io => pure (Ty.io argTy)
      | none =>
        -- Look up user-defined parameterized type
        match (← InferM.getTypeEnv).lookupType name.value with
        | some typeInfo =>
          -- Create the type constructor with its proper kind and apply the argument
          let baseTy := Ty.userCon typeInfo.typeId.kind typeInfo.typeId
          pure (Gen.applyTypeArgs baseTy #[argTy])
        | none =>
          InferM.reportError (.unknownType name.value name.span)
          InferM.freshVar "app"
    | .app _ _ _ =>
      -- Nested application like `Map String Int` - recursively resolve the function part
      -- This collects all arguments and applies them at once
      let (baseName, allArgs) ← collectTypeApp fn #[argTy]
      match baseName with
      | some name =>
        match HigherPrimitive.fromName? name with
        | some .array => pure (Ty.array (allArgs[0]?.getD argTy))
        | some .ref => pure (Ty.ref (allArgs[0]?.getD argTy))
        | some .io => pure (Ty.io (allArgs[0]?.getD argTy))
        | none =>
          match (← InferM.getTypeEnv).lookupType name with
          | some typeInfo =>
            let baseTy := Ty.userCon typeInfo.typeId.kind typeInfo.typeId
            pure (Gen.applyTypeArgs baseTy allArgs)
          | none =>
            InferM.reportError (.unknownType name span)
            InferM.freshVar "app"
      | none =>
        InferM.reportError (.unknownType "invalid nested type application" span)
        InferM.freshVar "app"
    | _ =>
      InferM.reportError (.unknownType "invalid type application" span)
      InferM.freshVar "app"

  | .forall_ _ body _ =>
    -- Type variables are handled at generalization time, not during constraint generation
    resolveTypeExpr body

  | .constrained _ body _ =>
    -- Constraints are collected separately during generalization
    resolveTypeExpr body

  | .parens inner _ =>
    resolveTypeExpr inner

  | .kinded ty _ _ =>
    resolveTypeExpr ty
where
  span : Span := match ty with
    | .app _ _ s | .arrow _ _ s | .tuple _ s | .list _ s
    | .forall_ _ _ s | .constrained _ _ s | .parens _ s | .kinded _ _ s => s
    | .var n | .con n => n.span

  /-- Collect the base type name and all arguments from nested type applications  -/
  collectTypeApp (ty : TypeExpr) (args : Array MonoTy) : InferM (Option String × Array MonoTy) := do
    match ty with
    | .con name => pure (some name.value, args)
    | .app fn arg _ =>
      let argTy ← resolveTypeExpr arg
      collectTypeApp fn (#[argTy] ++ args)
    | .parens inner _ => collectTypeApp inner args
    | _ => pure (none, args)

/-- Generate constraints for a top-level function, returning typed body -/
def genFunctionBody {scope : Scope} (fn : UntypedFunction)
    (body : Expr Unit scope)
    : InferM (MonoTy × Expr MonoTy scope × Array (BindingId × String × MonoTy)) := do
  -- Generate fresh type variables for parameters
  let mut paramInfos : Array (BindingId × String × MonoTy) := #[]
  let mut localBindings : Array (String × VarInfo) := #[]

  for (binding, name) in fn.params do
    let ty ← freshVar name
    paramInfos := paramInfos.push (binding, name, ty)
    localBindings := localBindings.push (name, { ty, bindingId := binding, name })

  -- Infer the body type with parameters in scope
  let (bodyTy, typedBody) ← InferM.withLocals localBindings do
    Gen.genExpr body

  -- If there's a declared type annotation, add a constraint
  match fn.declaredTypeSyntax with
  | some declaredTy =>
    let declaredMonoTy ← resolveTypeExpr declaredTy
    let returnTy := declaredMonoTy.stripArrows fn.params.size
    InferM.addEqualityConstraint bodyTy returnTy .typeAnnotation body.span declaredTy.span
  | none => pure ()

  return (bodyTy, typedBody, paramInfos)

end Soma.Infer
