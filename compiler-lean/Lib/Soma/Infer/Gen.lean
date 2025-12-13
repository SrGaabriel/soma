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

/-- Generate VarInfo for a parameter list -/
partial def genParamListImpl {α : Type} (params : ParamList α) : InferM (Array (String × VarInfo)) := do
  let rec go (acc : Array (String × VarInfo)) : ParamList α → InferM (Array (String × VarInfo))
    | .nil => return acc
    | .cons binding name _info ps => do
      let ty ← freshVar name
      let info : VarInfo := { ty, bindingId := binding, name }
      go (acc.push (name, info)) ps
  go #[] params

/-- Apply type arguments to a type constructor.
    Given a type of kind `k1 -> k2 -> ... -> *` and arguments,
    applies them in sequence to produce a MonoTy.
    If the kind doesn't match (not enough arrows), returns the type as-is
    (which will cause a type error elsewhere). -/
def applyTypeArgs (baseTy : Ty k) (args : Array MonoTy) : MonoTy :=
  go k baseTy args.toList
where
  go : (k : Kind) → Ty k → List MonoTy → MonoTy
    | .star, ty, [] => ty
    | .star, ty, _ => ty  -- Extra args ignored (shouldn't happen with well-formed input)
    | .arrow _ _, _, [] =>
      -- Not enough arguments - return a placeholder (shouldn't happen)
      .starPrim .unit
    | .arrow .star k2, ty, arg :: rest =>
      go k2 (.app ty arg) rest
    | .arrow (.arrow _ _) _, _, _ =>
      -- Higher-kinded argument - not supported in this simple version
      .starPrim .unit

/-! ### Mutually recursive constraint generation functions -/

mutual

/-- Generate constraints for an expression list, returning types for each -/
partial def genExprList {scope : Scope} (exprs : ExprList Unit scope)
    : InferM (Array MonoTy) := do
  match exprs with
  | .nil => return #[]
  | .cons e es => do
    let ty ← genExpr e
    let rest ← genExprList es
    return #[ty] ++ rest

/-- Generate constraints for an expression, returning its type -/
partial def genExpr {scope : Scope} (expr : Expr Unit scope) : InferM MonoTy := do
  match expr with
  | .var v _info span =>
    -- Look up the variable in the type environment
    let name := v.original
    match ← lookupLocal name with
    | some info => return info.ty
    | none =>
      reportError (.unknownVariable name span)
      freshVar "err"

  | .lit lit _span =>
    return genLiteral lit

  | .call fn args _info span => do
    let fnTy ← genExpr fn
    let argTys ← genExprList args
    let resultTy ← freshVar "result"
    let expectedFnTy := argTys.foldr (init := resultTy) fun argTy accTy =>
      Ty.arrow argTy accTy
    let fnSpan := fn.span
    addEqualityConstraint expectedFnTy fnTy .general fnSpan span
    return resultTy

  | .let_ binding original value body _info _span => do
    let valueTy ← genExpr value
    let varInfo : VarInfo := {
      ty := valueTy
      bindingId := binding
      name := original
    }
    withLocal original varInfo (genExpr body)

  | .lam params body _info _span => do
    let paramInfos ← genParamListImpl params
    let bodyTy ← withLocals paramInfos (genExpr body)
    let fnTy := paramInfos.foldr (init := bodyTy) fun (_, info) accTy =>
      Ty.arrow info.ty accTy
    return fnTy

  | .closure liftedName _captures _info span => do
    match ← lookupFunction liftedName.display with
    | some fnInfo =>
      let (ty, constraints) ← instantiate fnInfo.qualType
      for c in constraints do
        addConstraint c span
      return ty
    | none =>
      reportError (.unknownVariable liftedName.display span)
      freshVar "err"

  | .construct name _tag args _info span => do
    let ctorName := name.display
    match ← lookupConstructor ctorName with
    | some ctorInfo =>
      let freshParams ← ctorInfo.typeParams.mapM fun v => do
        let fresh ← freshVar v.name
        return (v.id, fresh)
      let σ := Subst.fromArrays ctorInfo.typeParams (freshParams.map (·.2))
      let expectedFieldTys := ctorInfo.fieldTypes.map (σ.apply ·)
      let argTys ← genExprList args
      let argList := args.toList
      for i in [:argTys.size] do
        if h : i < expectedFieldTys.size then
          let expectedTy := expectedFieldTys[i]
          let actualTy := argTys[i]!
          let argSpan := if i < argList.length then argList[i]!.span else span
          addEqualityConstraint expectedTy actualTy (.tupleElement i) span argSpan
      let baseTy := Ty.userCon ctorInfo.typeId.kind ctorInfo.typeId
      let resultTy := applyTypeArgs baseTy (freshParams.map (·.2))
      return resultTy
    | none =>
      reportError (.unknownConstructor ctorName span)
      freshVar "err"

  | .tuple elements _info span => do
    let elemTys ← genExprList elements
    match mkTupleType elemTys with
    | some ty => return ty
    | none =>
      reportError (.cannotInfer s!"tuple with {elemTys.size} elements (max 8)" span)
      freshVar "err"

  | .array elements _info span => do
    let elemTys ← genExprList elements
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
    return Ty.array elemTy

  | .if_ cond then_ else_ _info span => do
    let condTy ← genExpr cond
    addEqualityConstraint Ty.bool condTy .ifCondition span cond.span
    let thenTy ← genExpr then_
    let elseTy ← genExpr else_
    addEqualityConstraint thenTy elseTy .ifBranches then_.span else_.span
    return thenTy

  | .case scrutinees arms _info span => do
    let scrutTys ← genExprList scrutinees
    let resultTy ← freshVar "case_result"
    genArmList arms scrutTys resultTy span
    return resultTy

  | .fieldAccess expr _index _info _span => do
    let _ ← genExpr expr
    let fieldTy ← freshVar "field"
    return fieldTy

  | .global name _info span => do
    match ← lookupFunction name.display with
    | some fnInfo =>
      let (ty, constraints) ← instantiate fnInfo.qualType
      for c in constraints do
        addConstraint c span
      return ty
    | none =>
      reportError (.unknownVariable name.display span)
      freshVar "err"

  | .panic _message _info _span => do
    freshVar "panic"

/-- Generate constraints for an arm list -/
partial def genArmList {scope : Scope} (arms : ArmList Unit scope)
    (scrutTys : Array MonoTy) (resultTy : MonoTy) (caseSpan : Span)
    : InferM Unit := do
  match arms with
  | .nil => return ()
  | .cons arm rest => do
    genArm arm scrutTys resultTy caseSpan
    genArmList rest scrutTys resultTy caseSpan

/-- Generate constraints for a single arm -/
partial def genArm {scope : Scope} (arm : Arm Unit scope)
    (scrutTys : Array MonoTy) (resultTy : MonoTy) (caseSpan : Span)
    : InferM Unit := do
  match arm with
  | .mk patterns body span =>
    let patternBindings ← genPatternList patterns scrutTys caseSpan
    let bodyTy ← withLocals patternBindings (genExpr body)
    addEqualityConstraint resultTy bodyTy .caseArms caseSpan span

/-- Generate constraints and bindings from a pattern list -/
partial def genPatternList {α : Type} (patterns : PatternList α)
    (scrutTys : Array MonoTy) (span : Span)
    : InferM (Array (String × VarInfo)) := do
  match patterns with
  | .nil => return #[]
  | .cons pat rest => do
    let scrutTy ← match scrutTys[0]? with
      | some ty => pure ty
      | none => freshVar "scrut"
    let bindings ← genPattern pat scrutTy span
    let restBindings ← genPatternList rest (scrutTys.extract 1 scrutTys.size) span
    return bindings ++ restBindings

/-- Generate constraints and bindings from a single pattern -/
partial def genPattern {α : Type} (pat : Pattern α) (scrutTy : MonoTy) (span : Span)
    : InferM (Array (String × VarInfo)) := do
  match pat with
  | .wildcard _ _ =>
    return #[]

  | .var binding name _ _patSpan =>
    let info : VarInfo := { ty := scrutTy, bindingId := binding, name }
    return #[(name, info)]

  | .lit lit patSpan =>
    let litTy := genLiteral lit
    addEqualityConstraint scrutTy litTy .patternMatch span patSpan
    return #[]

  | .ctor ctorName pats _ patSpan =>
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
      -- pats is Array (Pattern α), need to generate bindings for each
      genPatternArray pats fieldTys patSpan
    | none =>
      reportError (.unknownConstructor ctorNameStr patSpan)
      return #[]

  | .tuple pats _ patSpan =>
    let n := pats.size
    -- Generate fresh type variables for each tuple element
    let elemTys ← freshVars n "tup"
    match mkTupleType elemTys with
    | some tupleTy =>
      addEqualityConstraint scrutTy tupleTy .patternMatch span patSpan
      genPatternArray pats elemTys patSpan
    | none =>
      reportError (.cannotInfer s!"tuple pattern with {n} elements (max 8)" patSpan)
      pure #[]

  | .array _ _ _ | .cons _ _ _ _ | .as _ _ _ _ _ =>
    -- Not yet implemented, but needed for exhaustiveness
    reportError (.cannotInfer "array/cons/as pattern" span)
    return #[]

/-- Generate constraints and bindings from a pattern array -/
partial def genPatternArray {α : Type} (pats : Array (Pattern α))
    (scrutTys : Array MonoTy) (span : Span)
    : InferM (Array (String × VarInfo)) := do
  let mut result := #[]
  for i in [:pats.size] do
    let pat := pats[i]!
    let scrutTy ← match scrutTys[i]? with
      | some ty => pure ty
      | none => freshVar "scrut"
    let bindings ← genPattern pat scrutTy span
    result := result ++ bindings
  return result

end

end Gen

/-- Generate constraints for a top-level function -/
def genFunction (name : String) (params : Array (String × BindingId))
    (bodyFn : {scope : Scope} → Expr Unit scope) (declaredType : Option QualifiedType)
    (span : Span) : InferM MonoTy := do
  -- Generate fresh type variables for parameters
  let paramInfos ← params.mapM fun (paramName, binding) => do
    let ty ← freshVar paramName
    let info : VarInfo := { ty, bindingId := binding, name := paramName }
    return (paramName, info)

  -- We need to provide a concrete scope for the body
  -- For now, we use the empty scope (the body should be closed)
  let body : Expr Unit Scope.empty := bodyFn
  let bodyTy ← InferM.withLocals paramInfos (Gen.genExpr body)

  -- Build function type
  let fnTy := paramInfos.foldr (init := bodyTy) fun (_, info) accTy =>
    Ty.arrow info.ty accTy

  -- If there's a declared type, constrain to match
  match declaredType with
  | some qt =>
    let (declTy, constraints) ← instantiate qt
    for c in constraints do
      addConstraint c span
    addEqualityConstraint declTy fnTy (.functionBody name) span span
  | none => pure ()

  return fnTy

end Soma.Infer
