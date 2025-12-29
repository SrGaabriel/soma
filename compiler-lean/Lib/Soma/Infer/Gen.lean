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
open InferM (freshVar freshRowVar freshLabelVar lookupLocal lookupFunction lookupConstructor lookupType
             addEqualityConstraint addConstraint reportError
             withLocal withLocals instantiate getFreshId)

namespace Gen

/-- Generate constraints for a literal, returning its type -/
def genLiteral (lit : Literal) : MonoTy :=
  lit.type

/-- Construct a tuple type from an array of element types.
    Returns Unit for empty, unwraps singletons, creates tuple for 2+ elements. -/
def mkTupleType (elemTys : Array MonoTy) : Option MonoTy :=
  match elemTys.toList with
  | [] => some Ty.unit
  | [x] => some x
  | fst :: snd :: rest => some (.tuple fst snd rest)

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
    | .arrow .label _, _, _ => .starPrim .unit -- Labels don't take type args
    | .arrow .row _, _, _ => .starPrim .unit -- Rows don't take type args
    | .label, _, _ => .starPrim .unit -- Labels are not star-kinded
    | .row, _, _ => .starPrim .unit -- Rows are not star-kinded

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
        reportError (.cannotInfer s!"tuple pattern with {n} elements" patSpan)
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

    | .variant label arg () patSpan =>
      -- Generate fresh type variable for the argument type (if present) and row tail
      let argTy ← match arg with
        | some _ => freshVar s!"variant_{label}"
        | none => pure Ty.unit
      let rowTail ← InferM.freshRowVar s!"r_{label}"
      -- The scrutinee must be a variant containing this case
      let expectedVariantTy := Ty.variant (.rowExtend (Ty.labelLit label) argTy rowTail)
      addEqualityConstraint scrutTy expectedVariantTy .patternMatch span patSpan
      -- Generate constraints for the argument pattern if present
      match arg with
      | some argPat =>
        let (argBindings, typedArgPat) ← genPatternAux argPat argTy patSpan
        return (argBindings, .variant label (some typedArgPat) scrutTy patSpan)
      | none =>
        return (#[], .variant label none scrutTy patSpan)

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

/-- Generate constraints for a normal function call -/
partial def genFunctionCall {scope : Scope}
    (fn : Expr Unit scope) (args : ExprList Unit scope) (span : Span)
    : InferM (MonoTy × Expr MonoTy scope) := do
  let (fnTy, typedFn) ← genExpr fn
  let (argTys, typedArgs) ← genExprList args
  let resultTy ← freshVar "result"
  let expectedFnTy := argTys.foldr (init := resultTy) fun argTy accTy =>
    Ty.arrow argTy accTy
  addEqualityConstraint expectedFnTy fnTy .general fn.span span
  return (resultTy, .call typedFn typedArgs resultTy span)

/-- Generate constraints for an expression, returning its type and typed version -/
partial def genExpr {scope : Scope} (expr : Expr Unit scope)
    : InferM (MonoTy × Expr MonoTy scope) := do
  match expr with
  | .var v () span =>
    let name := v.original
    match ← lookupLocal name with
    | some info =>
      return (info.ty, .var v info.ty span)
    | none =>
      -- Check if this might be a constructor
      let isUppercase := name.get? ⟨0⟩ |>.map Char.isUpper |>.getD false
      if isUppercase then
        match ← lookupConstructor name with
        | some ctorInfo =>
          -- Instantiate with fresh type variables
          let freshParams ← ctorInfo.typeParams.mapM fun tv => do
            let fresh ← freshVar tv.name
            return (tv.id, fresh)
          let σ := Subst.fromArrays ctorInfo.typeParams (freshParams.map (·.2))
          let expectedFieldTys := ctorInfo.fieldTypes.map (σ.apply ·)
          -- Build the constructor name
          let typeUnique : Unique := ⟨ctorInfo.typeId.unique, ctorInfo.typeId.module, ctorInfo.typeId.name⟩
          let ctorName := Name.ctor typeUnique name ctorInfo.tag
          -- For nullary constructors, just return the type
          if expectedFieldTys.isEmpty then
            let baseTy := Ty.userCon ctorInfo.typeId.kind ctorInfo.typeId
            let resultTy := applyTypeArgs baseTy (freshParams.map (·.2))
            return (resultTy, .construct ctorName ctorInfo.tag .nil resultTy span)
          else
            -- Constructor needs arguments - return as a function type
            let baseTy := Ty.userCon ctorInfo.typeId.kind ctorInfo.typeId
            let resultTy := applyTypeArgs baseTy (freshParams.map (·.2))
            let ctorFnTy := expectedFieldTys.foldr (init := resultTy) fun argTy accTy =>
              Ty.arrow argTy accTy
            return (ctorFnTy, .construct ctorName ctorInfo.tag .nil ctorFnTy span)
        | none =>
          reportError (.unknownVariable name span)
          let errTy ← freshVar "err"
          return (errTy, .var v errTy span)
      else
        -- Check for global function
        match ← lookupFunction name with
        | some fnInfo =>
          -- Instantiate the qualified type with fresh type variables
          let freshVars ← fnInfo.qualType.vars.mapM fun tv => do
            let fresh ← freshVar tv.name
            return (tv.id, fresh)
          let σ := Subst.fromArrays fnInfo.qualType.vars (freshVars.map (·.2))
          let instTy := σ.apply fnInfo.qualType.body
          return (instTy, .var v instTy span)
        | none =>
          reportError (.unknownVariable name span)
          let errTy ← freshVar "err"
          return (errTy, .var v errTy span)

  | .lit lit span =>
    let ty := genLiteral lit
    return (ty, .lit lit span)

  | .call fn args () span => do
    -- Check for label-polymorphic field access pattern: rec @label
    match args with
    | .cons (.typeApp (.label labelName) () _labelSpan) .nil =>
      -- First, check if fn is syntactically a record-like expression
      let isLikelyRecord := match fn with
        | .record .. | .recordUpdate .. => true
        | .global .. => false  -- Global names are functions, not records
        | .var .. => true  -- Local variables might be record parameters
        | _ => true  -- Other expressions might be records
      if isLikelyRecord then
        -- This is `record @label` - treat as label-polymorphic field access
        let (recTy, typedRec) ← genExpr fn
        -- Generate fresh variables for field type and row tail
        let fieldTy ← freshVar s!"field_{labelName}"
        let rowTail ← InferM.freshRowVar s!"r_{labelName}"
        -- Check if labelName refers to a label type variable in scope
        let labelTy : LabelTy ← match ← InferM.lookupLabelVar labelName with
          | some labelVar => pure labelVar  -- Use the label type variable
          | none => pure (Ty.labelLit labelName)  -- Use concrete label literal
        -- The record must have a field with this label
        let expectedRecordTy := Ty.record (.rowExtend labelTy fieldTy rowTail)
        addEqualityConstraint recTy expectedRecordTy (.fieldAccess labelName) fn.span span
        -- Return as field access
        return (fieldTy, .fieldAccess typedRec labelName 0 fieldTy span)
      else
        -- This is `function @label`, treat as type application (label instantiation) followed by normal function call semantics
        genFunctionCall fn args span
    | _ => genFunctionCall fn args span

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
      reportError (.cannotInfer s!"tuple with {elemTys.size} elements" span)
      let errTy ← freshVar "err"
      return (errTy, .tuple typedElements errTy span)

  | .record fields () span => do
    -- Build a row type from the fields
    let mut typedFieldsList : List (String × Expr MonoTy scope) := []
    let mut rowTy : RowTy := .rowEmpty
    -- Process fields in reverse to build row type correctly (first field at top)
    for (fieldName, fieldExpr) in fields.toList.reverse do
      let (fieldTy, typedFieldExpr) ← genExpr fieldExpr
      typedFieldsList := (fieldName, typedFieldExpr) :: typedFieldsList
      rowTy := .rowExtend (Ty.labelLit fieldName) fieldTy rowTy
    let recordTy := Ty.record rowTy
    return (recordTy, .record (RecordFieldList.fromList typedFieldsList) recordTy span)

  | .recordUpdate base updates () span => do
    -- Type the base expression
    let (baseTy, typedBase) ← genExpr base
    -- Type each update field
    let mut typedUpdatesList : List (String × Expr MonoTy scope) := []
    for (fieldName, fieldExpr) in updates.toList.reverse do
      let (_, typedFieldExpr) ← genExpr fieldExpr
      typedUpdatesList := (fieldName, typedFieldExpr) :: typedUpdatesList
    -- The base must be a record containing at least the updated fields
    -- Constraint: baseTy ~ { f1 :: T1, f2 :: T2, ... | rest } where T1, T2 are the types of the update expressions
    let restRowVar ← freshRowVar "rest"
    let expectedRowTy := typedUpdatesList.foldr (init := restRowVar) fun (fieldName, expr) acc =>
      .rowExtend (Ty.labelLit fieldName) (expr.getInfo.getD (.starPrim .unit)) acc
    addEqualityConstraint baseTy (Ty.record expectedRowTy) .recordUpdate base.span span
    -- Result type is the same as base type
    return (baseTy, .recordUpdate typedBase (RecordFieldList.fromList typedUpdatesList) baseTy span)

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

  | .fieldAccess expr fieldName _index () span => do
    let (exprTy, typedExpr) ← genExpr expr
    -- Generate fresh variables for field type and row tail
    let fieldTy ← freshVar s!"field_{fieldName}"
    let rowTail ← InferM.freshRowVar s!"r_{fieldName}"
    -- The expression must be a record with this field (using concrete label)
    -- exprTy ~ { fieldName :: fieldTy | rowTail }
    let expectedRecordTy := Ty.record (.rowExtend (Ty.labelLit fieldName) fieldTy rowTail)
    addEqualityConstraint exprTy expectedRecordTy (.fieldAccess fieldName) expr.span span
    -- Index is 0 for now but it will be resolved after monomorphization (todo: review)
    return (fieldTy, .fieldAccess typedExpr fieldName 0 fieldTy span)

  | .global name () span => do
    match ← lookupFunction name.display with
    | some fnInfo =>
      let (ty, constraints) ← instantiate fnInfo.qualType
      for c in constraints do
        addConstraint c span
      return (ty, .global name ty span)
    | none =>
      -- Check if this is a constructor reference (Name.ctor)
      match name with
      | .ctor _typeUnique _ctorName _tag =>
        -- Use the full qualified name for lookup (e.g., "Maybe.Just")
        match ← lookupConstructor name.display with
        | some ctorInfo =>
          -- Instantiate with fresh type variables
          let freshParams ← ctorInfo.typeParams.mapM fun tv => do
            let fresh ← freshVar tv.name
            return (tv.id, fresh)
          let σ := Subst.fromArrays ctorInfo.typeParams (freshParams.map (·.2))
          let expectedFieldTys := ctorInfo.fieldTypes.map (σ.apply ·)
          -- For nullary constructors, just return the constructed value
          if expectedFieldTys.isEmpty then
            let baseTy := Ty.userCon ctorInfo.typeId.kind ctorInfo.typeId
            let resultTy := applyTypeArgs baseTy (freshParams.map (·.2))
            return (resultTy, .construct name ctorInfo.tag .nil resultTy span)
          else
            -- Constructor needs arguments - treat it as a function (global reference)
            -- It will be fully applied later via .call
            let baseTy := Ty.userCon ctorInfo.typeId.kind ctorInfo.typeId
            let resultTy := applyTypeArgs baseTy (freshParams.map (·.2))
            let ctorFnTy := expectedFieldTys.foldr (init := resultTy) fun argTy accTy =>
              Ty.arrow argTy accTy
            return (ctorFnTy, .global name ctorFnTy span)
        | none =>
          reportError (.unknownVariable name.display span)
          let errTy ← freshVar "err"
          return (errTy, .global name errTy span)
      | _ =>
        reportError (.unknownVariable name.display span)
        let errTy ← freshVar "err"
        return (errTy, .global name errTy span)

  | .panic message () span => do
    let ty ← freshVar "panic"
    return (ty, .panic message ty span)

  | .proj typeName fieldName fieldIndex () span => do
    match ← lookupType typeName.display with
    | some typeInfo =>
      match typeInfo.lookupField fieldName with
      | some (_, fieldTy) =>
        -- Instantiate type parameters with fresh variables
        let freshParams ← typeInfo.params.mapM fun v => freshVar v.name
        let σ := Subst.fromArrays typeInfo.params freshParams
        let instFieldTy := σ.apply fieldTy
        let baseTy := Ty.userCon typeInfo.typeId.kind typeInfo.typeId
        let recordTy := applyTypeArgs baseTy freshParams
        let projTy := Ty.arrow recordTy instFieldTy
        return (projTy, .proj typeName fieldName fieldIndex projTy span)
      | none =>
        reportError (.unknownField typeName.display fieldName span)
        let errTy ← freshVar "err"
        return (errTy, .proj typeName fieldName fieldIndex errTy span)
    | none =>
      reportError (.unknownType typeName.display span)
      let errTy ← freshVar "err"
      return (errTy, .proj typeName fieldName fieldIndex errTy span)

  | .typeApp arg () span => do
    -- At this stage, we just give it a fresh type, the actual instantiation happens when the function call context resolves the type arguments.
    let ty ← freshVar "typeApp"
    let metalArg : Metal.TypeArg := match arg with
      | .label name => .label name
      | .type tyExpr =>
        -- todo: use the type env
        .type ⟨.star, .starPrim .unit⟩
    return (ty, .typeApp metalArg ty span)

  | .inject label args () span => do
    let (argTys, typedArgs) ← genExprList args
    let argTy ← match argTys.toList with
      | [] => pure Ty.unit
      | [ty] => pure ty
      | tys =>
        -- Multiple args: use tuple type
        match tys with
        | fst :: snd :: rest => pure (.tuple fst snd rest)
        | _ => pure Ty.unit
    let rowTail ← InferM.freshRowVar s!"r_{label}"
    let variantTy := Ty.variant (.rowExtend (Ty.labelLit label) argTy rowTail)
    return (variantTy, .inject label typedArgs variantTy span)

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

/-- Environment mapping type variable names to their resolved MonoTy -/
abbrev TyVarEnv := Std.HashMap String MonoTy

/-- Resolve a TypeExpr (syntax) to a MonoTy during type inference, with bound type variables -/
partial def resolveTypeExprWithEnv (tyVarEnv : TyVarEnv) (ty : TypeExpr) : InferM MonoTy := do
  match ty with
  | .var name =>
    -- Check if type variable is already bound
    match tyVarEnv.get? name.value with
    | some boundTy => pure boundTy
    | none => InferM.freshVar name.value

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
    let fromTy ← resolveTypeExprWithEnv tyVarEnv from_
    let toTy ← resolveTypeExprWithEnv tyVarEnv to
    pure (.arrow fromTy toTy)

  | .tuple elements _ =>
    let elemTys ← elements.mapM (resolveTypeExprWithEnv tyVarEnv)
    match Gen.mkTupleType elemTys with
    | some ty => pure ty
    | none =>
      InferM.reportError (.tupleTooLarge elemTys.size ty.span)
      InferM.freshVar "tuple"

  | .list elem _ =>
    let elemTy ← resolveTypeExprWithEnv tyVarEnv elem
    pure (Ty.array elemTy)

  | .app fn arg span =>
    -- First resolve the argument
    let argTy ← resolveTypeExprWithEnv tyVarEnv arg
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
      let (baseName, allArgs) ← collectTypeApp tyVarEnv fn #[argTy]
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

  | .forall_ binders body _ =>
    -- Extend tyVarEnv with fresh type variables for the bound names
    let mut newEnv := tyVarEnv
    for binder in binders do
      let varName := binder.name.value
      let kind := binder.kind.map (Kind.fromString ·.value) |>.getD .star
      let freshTy ← InferM.freshVarOfKind varName kind
      newEnv := newEnv.insert varName freshTy
    resolveTypeExprWithEnv newEnv body

  | .constrained _ body _ =>
    -- Constraints are collected separately during generalization
    resolveTypeExprWithEnv tyVarEnv body

  | .parens inner _ =>
    resolveTypeExprWithEnv tyVarEnv inner

  | .kinded ty _ _ =>
    resolveTypeExprWithEnv tyVarEnv ty

  | .record fields tail _ =>
    -- First, determine the base row (either empty or a row variable for polymorphism)
    let baseRow : RowTy ← match tail with
      | some tailName =>
        match tyVarEnv.get? tailName.value with
        | some (.var tyVarId) =>
          -- Use the variable if it was bound with row kind
          -- kind error but we create a fresh row variable to avoid crashes for now
          if tyVarId.kind == .row then
            pure (.var tyVarId)
          else
            -- Star-kinded variable used as row tail
            -- could be an error, but we're lenient for now
            InferM.freshRowVar tailName.value
        | some _ =>
          -- Bound to a non-variable type, create fresh row var
          InferM.freshRowVar tailName.value
        | none =>
          -- Unbound variable - create fresh row variable
          InferM.freshRowVar tailName.value
      | none =>
        pure .rowEmpty
    -- Build the row type from fields
    let mut rowTy := baseRow
    -- Build a TyVarId map from tyVarEnv for lookupOrLiteralLabel
    let tyVarIdMap : Std.HashMap String TyVarId := tyVarEnv.fold (init := {}) fun acc name ty =>
      match ty with
      | .var v => acc.insert name v
      | _ => acc
    for (fieldName, fieldTy) in fields.reverse do
      let fieldMonoTy ← resolveTypeExprWithEnv tyVarEnv fieldTy
      let labelTy := Ty.lookupOrLiteralLabel fieldName.value tyVarIdMap
      rowTy := .rowExtend labelTy fieldMonoTy rowTy
    pure (.record rowTy)

  | .variant cases tail _ =>
    -- First, determine the base row (either empty or a row variable for polymorphism)
    let baseRow : RowTy ← match tail with
      | some tailName =>
        match tyVarEnv.get? tailName.value with
        | some (.var tyVarId) =>
          if tyVarId.kind == .row then
            pure (.var tyVarId)
          else
            InferM.freshRowVar tailName.value
        | some _ =>
          InferM.freshRowVar tailName.value
        | none =>
          InferM.freshRowVar tailName.value
      | none =>
        pure .rowEmpty
    -- Build the row type from cases
    let mut rowTy := baseRow
    let tyVarIdMap : Std.HashMap String TyVarId := tyVarEnv.fold (init := {}) fun acc name ty =>
      match ty with
      | .var v => acc.insert name v
      | _ => acc
    for (caseName, caseTy) in cases.reverse do
      let caseMonoTy ← resolveTypeExprWithEnv tyVarEnv caseTy
      let labelTy := Ty.lookupOrLiteralLabel caseName.value tyVarIdMap
      rowTy := .rowExtend labelTy caseMonoTy rowTy
    pure (.variant rowTy)
where
  span : Span := match ty with
    | .app _ _ s | .arrow _ _ s | .tuple _ s | .list _ s
    | .forall_ _ _ s | .constrained _ _ s | .parens _ s | .kinded _ _ s
    | .record _ _ s | .variant _ _ s => s
    | .var n | .con n => n.span

  /-- Collect the base type name and all arguments from nested type applications  -/
  collectTypeApp (env : TyVarEnv) (ty : TypeExpr) (args : Array MonoTy) : InferM (Option String × Array MonoTy) := do
    match ty with
    | .con name => pure (some name.value, args)
    | .app fn arg _ =>
      let argTy ← resolveTypeExprWithEnv env arg
      collectTypeApp env fn (#[argTy] ++ args)
    | .parens inner _ => collectTypeApp env inner args
    | _ => pure (none, args)

/-- Resolve a TypeExpr (syntax) to a MonoTy during type inference -/
def resolveTypeExpr (ty : TypeExpr) : InferM MonoTy := do
  let varNames := ty.collectVarNames
  let mut tyVarEnv : TyVarEnv := {}
  for name in varNames do
    let freshTy ← InferM.freshVar name
    tyVarEnv := tyVarEnv.insert name freshTy
  resolveTypeExprWithEnv tyVarEnv ty

/-- Extract label type variable binders from a forall type expression -/
def extractLabelBinders (ty : Soma.Syntax.TypeExpr) : InferM (Array (String × LabelTy)) := do
  match ty with
  | .forall_ vars body _ =>
    let mut labelBindings : Array (String × LabelTy) := #[]
    for binder in vars do
      match binder.kind with
      | some kindName =>
        let kind := Kind.fromString kindName.value
        if kind == .label then
          let freshId ← InferM.getFreshId
          let tyVarId : TyVarId := ⟨binder.name.value, freshId, .label⟩
          labelBindings := labelBindings.push (binder.name.value, .var tyVarId)
      | none => pure ()
    let innerLabels ← extractLabelBinders body
    return labelBindings ++ innerLabels
  | .parens inner _ => extractLabelBinders inner
  | .constrained _ body _ => extractLabelBinders body
  | _ => return #[]

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

  -- Extract label binders from type annotation (if any) before inferring body
  let labelBindings ← match fn.declaredTypeSyntax with
    | some declaredTy => extractLabelBinders declaredTy
    | none => pure #[]

  -- Infer the body type with parameters and label variables in scope
  let (bodyTy, typedBody) ← InferM.withLabelVars labelBindings do
    InferM.withLocals localBindings do
      Gen.genExpr body

  -- If there's a declared type annotation, add constraints for params and return type
  match fn.declaredTypeSyntax with
  | some declaredTy =>
    let declaredMonoTy ← resolveTypeExpr declaredTy
    -- Extract parameter types from the declared type and constrain them
    let mut currentTy := declaredMonoTy
    for (_, _, paramTy) in paramInfos do
      match currentTy with
      | .arrow fromTy toTy =>
        InferM.addEqualityConstraint paramTy fromTy .typeAnnotation body.span declaredTy.span
        currentTy := toTy
      | _ => break -- Not enough arrows in the type
    -- Constrain return type
    let returnTy := declaredMonoTy.stripArrows fn.params.size
    InferM.addEqualityConstraint bodyTy returnTy .typeAnnotation body.span declaredTy.span
  | none => pure ()

  return (bodyTy, typedBody, paramInfos)

end Soma.Infer
