import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.Quote
import Soma.Dependent.Monad
import Soma.Dependent.Elaborate
import Soma.Dependent.Infer
import Soma.Dependent.Instance
import Soma.Dependent.Zonk
import Soma.Core.Module
import Soma.Syntax.Ast

namespace Soma.Dependent.TraitElaborate

open Soma (Unique)
open Soma.Core
open Soma.Syntax (Span TypeVarBinder)
open Soma.Dependent.Elaborate (ElabEnv elaborateType)

/-- Maps source spans to their elaborated instance info -/
abbrev InstanceMap := Std.HashMap Span InstanceInfo

/-- Scope-aware class-name resolution -/
def resolveClassName (qn : Soma.Syntax.QualName)
    : TCM (Option (QualifiedName × ClassInfo)) := do
  match ← TCM.resolve qn.path qn.name with
  | some resolved =>
    match ← TCM.lookupClass resolved.id with
    | some info =>
      TCM.recordGlobalDep resolved
      return some (resolved, info)
    | none =>
      TCM.addError (.unknownClass qn.name qn.span)
      return none
  | none =>
    let env ← TCM.getInstanceEnv
    let existsGlobally := env.classes.toList.any fun (u, _) => u.original == qn.name
    if existsGlobally then
      TCM.addError (.classNotInScope qn.name qn.span)
    else
      TCM.addError (.unknownClass qn.name qn.span)
    return none

/-- Build an evaluation Env of the given size with neutral variables at each level -/
private def buildSubstEnv (depth : Nat) : Env :=
  if depth == 0 then Env.mk [] 0
  else
    let bindings := (List.range depth).reverse.map fun lvl =>
      let name := s!"_sv{lvl}"
      (name, Value.vNeutral (.vType .zero) (.nVar ⟨name, ⟨lvl⟩⟩))
    Env.mk bindings depth

mutual

/-- Substitute type parameters by name in a value -/
partial def substituteTypeArgsInValue (v : Value) (paramNames : Array String)
    (typeArgs : Array Value) (depth : Nat) : TCM Value := do
  let v' ← force v
  match v' with
  | .vNeutral ty neu =>
    let ty' ← substituteTypeArgsInValue ty paramNames typeArgs depth
    let spine' ← neu.spine.mapM (substituteElim · paramNames typeArgs depth)
    match neu.head with
    | .hVar var =>
      match paramNames.findIdx? (· == var.name) with
      | some idx =>
        if h : idx < typeArgs.size then
          applySpine typeArgs[idx] spine'
        else
          return .vNeutral ty' (.mk neu.head spine')
      | none =>
        return .vNeutral ty' (.mk neu.head spine')
    | _ =>
      let head' ← substituteHead neu.head paramNames typeArgs depth
      return .vNeutral ty' (.mk head' spine')
  | .vPi qty binder name dom cod =>
    let dom' ← substituteTypeArgsInValue dom paramNames typeArgs depth
    let dummyArg := Value.vNeutral dom' (.nVar ⟨name, ⟨depth⟩⟩)
    let codVal ← applyClosure cod dummyArg
    let codVal' ← substituteTypeArgsInValue codVal paramNames typeArgs (depth + 1)
    let closureEnv := buildSubstEnv depth
    let bodyExpr := Soma.Core.quoteExpr ⟨depth + 1⟩ codVal'
    return .vPi qty binder name dom' (Closure.term name closureEnv bodyExpr)
  | .vSigma qty name fst snd =>
    let fst' ← substituteTypeArgsInValue fst paramNames typeArgs depth
    let dummyArg := Value.vNeutral fst' (.nVar ⟨name, ⟨depth⟩⟩)
    let sndVal ← applyClosure snd dummyArg
    let sndVal' ← substituteTypeArgsInValue sndVal paramNames typeArgs (depth + 1)
    let closureEnv := buildSubstEnv depth
    let bodyExpr := Soma.Core.quoteExpr ⟨depth + 1⟩ sndVal'
    return .vSigma qty name fst' (Closure.term name closureEnv bodyExpr)
  | .vRecord row =>
    let row' ← substituteTypeArgsInValue row paramNames typeArgs depth
    return .vRecord row'
  | .vRowExtend label ty tail =>
    let ty' ← substituteTypeArgsInValue ty paramNames typeArgs depth
    let tail' ← substituteTypeArgsInValue tail paramNames typeArgs depth
    return .vRowExtend label ty' tail'
  | .vDataType id params =>
    let params' ← params.mapM (substituteTypeArgsInValue · paramNames typeArgs depth)
    return .vDataType id params'
  | _ => return v'

partial def substituteHead (h : Head) (paramNames : Array String)
    (typeArgs : Array Value) (depth : Nat) : TCM Head := do
  match h with
  | .hVar _ => return h
  | .hMeta _ => return h
  | .hErrored => return h
  | .hConst name ty =>
    let ty' ← substituteTypeArgsInValue ty paramNames typeArgs depth
    return .hConst name ty'
  | .hCase scrutinees arms rty =>
    let scrutinees' ← scrutinees.mapM (substituteTypeArgsInValue · paramNames typeArgs depth)
    let rty' ← substituteTypeArgsInValue rty paramNames typeArgs depth
    return .hCase scrutinees' arms rty'

partial def substituteElim (e : Elim) (paramNames : Array String)
    (typeArgs : Array Value) (depth : Nat) : TCM Elim := do
  match e with
  | .eApp arg =>
    let arg' ← substituteTypeArgsInValue arg paramNames typeArgs depth
    return .eApp arg'
  | .eFst => return .eFst
  | .eSnd => return .eSnd
  | .eField n => return .eField n

end


/-! ## Trait Elaboration

Elaborate a type class (trait) declaration into a ClassInfo structure.
The record type for the class is built from the method signatures.
-/

/-- Build the record type for a type class.

For a trait like:
  trait Eq a where
    def eq :: a -> a -> Bool

The record type is:
  forall {a : Type}. { eq : a -> a -> Bool }

We build this by:
1. Creating an elaboration environment with type parameters bound
2. Elaborating each method signature in that environment
3. Building a record row from the method types
4. Wrapping in implicit foralls for type parameters
-/
def elaborateClassRecordType (params : Array TypeVarBinder)
  (methods : Array (QualifiedName × Soma.Syntax.Expr)) : TCM Value := do
  let N := params.size

  -- Resolve each type-param's kind once, outside the bindings
  let mut paramKindExprs : Array Soma.Core.Expr := #[]
  let mut paramKinds : Array Value := #[]
  for param in params do
    let kindExpr ← match param.kind with
      | some k => Soma.Dependent.inferTypeExpr k
      | none => pure (.sort Level.zero)
    let kindVal ← TCM.evalExpr kindExpr
    paramKindExprs := paramKindExprs.push kindExpr
    paramKinds := paramKinds.push kindVal

  let mut bindings : Array (Soma.Unique × String) := #[]
  for param in params do
    let uid ← TCM.freshLocalId param.name.name
    bindings := bindings.push (uid, param.name.name)

  let buildInner : TCM Soma.Core.Expr := do
    let mut fields : List (String × Value) := []
    for (methodName, methodTypeSyntax) in methods do
      let expr ← Soma.Dependent.inferTypeExpr methodTypeSyntax
      let methodType ← TCM.evalExpr expr
      fields := (methodName.display, methodType) :: fields
    let mut row := Value.vRowEmpty
    for (name, ty) in fields.reverse do
      row := Value.vRowExtend (Value.vLabelLit name) ty row
    pure (Soma.Core.quoteExpr ⟨N⟩ (Value.vRecord row))

  let wrapped ← bindings.zip paramKinds |>.foldrM (init := buildInner)
    (fun ((uid, name), kindVal) acc =>
      pure (TCM.withBinding name uid kindVal .omega .implicit Span.uninhabited acc))
  let innerBody ← wrapped

  let mut piExpr : Soma.Core.Expr := innerBody
  for i in [:N] do
    let idx := N - 1 - i
    let name := params[idx]!.name.name
    let kindExpr := paramKindExprs[idx]!
    piExpr := .pi .omega .implicit name kindExpr piExpr
  TCM.evalExprInEnv Soma.Core.Env.empty piExpr

/-- Elaborate superclass constraints.

For a trait like:
  trait Ord a with (Eq a) where ...

The superclass constraint (Eq a) means:
- Ord's parameter 0 (a) maps to Eq's parameter 0

Returns an array of (superclass Unique, parameter index mapping).
-/
def elaborateSuperclasses (params : Array TypeVarBinder)
    (constraints : Array Syntax.Constraint)
    : TCM (Array (Unique × Array Nat)) := do
  let paramNames := params.map (·.name.name)
  let mut result : Array (Unique × Array Nat) := #[]

  for constraint in constraints do
    match ← resolveClassName constraint.className with
    | none =>
      -- `resolveClassName` has already emitted a targeted diagnostic.
      pure ()
    | some (_, classInfo) =>
      -- Map constraint args to parameter indices
      let mut indices : Array Nat := #[]
      for arg in constraint.args do
        match arg with
        | .var name =>
          match paramNames.findIdx? (· == name.name) with
          | some idx => indices := indices.push idx
          | none => pure ()
        | _ => pure ()
      result := result.push (classInfo.classId, indices)

  return result

def elaborateClass (typeClass : Soma.Core.TypeClassMeta) : TCM ClassInfo := do
  let classUnique := typeClass.name.id

  -- Elaborate the record type from method signatures
  let recordType ← elaborateClassRecordType typeClass.params typeClass.methodSignatures

  -- Elaborate superclass constraints
  let superclasses ← elaborateSuperclasses typeClass.params typeClass.superclasses

  return {
    classId := classUnique
    numParams := typeClass.params.size
    paramQuantities := typeClass.params.map (fun _ => Quantity.omega)
    recordType := recordType
    superclasses := superclasses
    span := Span.uninhabited
  }

/-- Elaborate a constraint into (class Unique, arg Values). -/
def elaborateConstraint (constraint : Syntax.Constraint) (env : ElabEnv)
    : TCM (Option (Unique × Array Value)) := do
  match ← resolveClassName constraint.className with
  | none => return none
  | some (_, classInfo) =>
    let args ← constraint.args.mapM (elaborateType env)
    return some (classInfo.classId, args)

/-- Substitute instance type arguments into a method signature.

For `instance Display Int where def display | x => ...`:
- The class method signature is `a -> String`
- We substitute `a := Int` to get `Int -> String`
-/
def substituteMethodType (methodTypeSyntax : Soma.Syntax.Expr) (params : Array TypeVarBinder)
    (typeArgs : Array Value) : TCM Value := do
  -- Elaborate the method type with type parameters bound as TCM implicits
  let paramNames := params.map (·.name.name)
  let mut bindings : Array (Soma.Unique × String × Value) := #[]
  for param in params do
    let kindVal ← match param.kind with
      | some k => do
        let expr ← Soma.Dependent.inferTypeExpr k
        TCM.evalExpr expr
      | none => pure (Value.vType Level.zero)
    let uid ← TCM.freshLocalId param.name.name
    bindings := bindings.push (uid, param.name.name, kindVal)

  let go : TCM Value := do
    let expr ← Soma.Dependent.inferTypeExpr methodTypeSyntax
    TCM.evalExpr expr

  let methodType ← bindings.foldrM (init := go)
    (fun (uid, name, kind) acc =>
      pure (TCM.withBinding name uid kind .omega .implicit Span.uninhabited acc))
  let resolved ← methodType

  substituteTypeArgsInValue resolved paramNames typeArgs 0

/-- Build a lambda value from parameter names and types wrapping a body value. -/
partial def buildLambdaValue (paramNames : Array String) (paramTypes : Array Value)
    (bodyVal : Value) : TCM Value := do
  -- Wrap in lambdas for each parameter (right to left)
  let mut result := bodyVal
  for i in [:paramNames.size] do
    let idx := paramNames.size - 1 - i
    if h₁ : idx < paramNames.size then
      let name := paramNames[idx]
      let _paramTy := if h₂ : idx < paramTypes.size then paramTypes[idx] else Value.vType .zero
      result := Value.vLam name (Closure.const name result)

  return result

/-- Result of elaborating a single instance method -/
structure MethodElabResult where
  /-- The method value for the instance record -/
  value : Value
  /-- The Core Expr body (before NbE evaluation) -/
  coreBody : Expr
  /-- The full lambda-wrapped Expr (params abstracted, before evaluation) -/
  lambdaExpr : Expr
  /-- The full function type (after instance type argument substitution) -/
  fnType : Value
  /-- Parameter bindings: (Unique, name) pairs -/
  params : Array (Unique × String)

/-- Extract explicit parameter types from a function type, skipping implicit binders -/
private partial def extractParamTypes (ty : Value) (count : Nat) : TCM (Array Value × Value) := do
  if count == 0 then
    return (#[], ty)
  else
    let ty' ← force ty
    match ty' with
    | .vPi _ binder _ dom cod =>
      let dummyArg ← TCM.freshMetaVal dom
      let codTy ← applyClosure cod dummyArg
      if binder.isImplicit then
        extractParamTypes codTy count
      else
        let (restParams, resultTy) ← extractParamTypes codTy (count - 1)
        return (#[dom] ++ restParams, resultTy)
    | _ =>
      return (#[], ty')

/-- Elaborate a method implementation.

Type-checks the method body against the expected (substituted) signature
and returns the elaborated value -/
def elaborateMethodImpl (methodFn : Soma.Core.UntypedFunction) (expectedType : Value)
    : TCM MethodElabResult := do
  let paramNames := methodFn.params

  -- Decompose the expected type to get explicit parameter types
  let (paramTypes, _resultType) ← extractParamTypes expectedType paramNames.size

  -- Extend context with params, then elaborate the method body
  let rec bindParams (idx : Nat) (accParams : Array (Unique × String))
      : TCM (Value × Expr × Array (Unique × String)) := do
    if idx >= paramNames.size then
      let (_bodyTy, coreBody) ← Soma.Dependent.inferSyntax methodFn.body
      let bodyVal ← TCM.evalExpr coreBody
      return (bodyVal, coreBody, accParams)
    else
      let name := paramNames[idx]!
      let paramTy := if h : idx < paramTypes.size then paramTypes[idx] else Value.vType .zero
      let bindingId ← TCM.freshLocalId name
      TCM.withBinding name bindingId paramTy .omega
        (Soma.Core.BinderInfo.explicit) methodFn.span do
        let paramUnique : Unique := ⟨bindingId.id, bindingId.module, name⟩
        bindParams (idx + 1) (accParams.push (paramUnique, name))

  let (_bodyVal, coreBody, generatedParams) ← bindParams 0 #[]

  let _ ← Soma.Dependent.solvePendingInstances
  let coreBody' ← zonkExpr coreBody
  let expectedType' ← zonkValue expectedType

  -- Build the method value by abstracting fvars into proper lambda binders
  let mut lambdaExpr := coreBody'
  for i in [:generatedParams.size] do
    let idx := generatedParams.size - 1 - i
    let (paramId, paramName) := generatedParams[idx]!
    lambdaExpr := lambdaExpr.abstractFVar paramId
    let domTy := if idx < paramTypes.size then
      Soma.Core.quoteExpr0 paramTypes[idx]!
    else
      Expr.sort Level.zero
    lambdaExpr := .lam .explicit paramName domTy lambdaExpr
  let methodVal ← TCM.evalExpr lambdaExpr

  return {
    value := methodVal
    coreBody := coreBody'
    lambdaExpr := lambdaExpr
    fnType := expectedType'
    params := generatedParams
  }

/-- Extract field names and types from a record type value -/
private partial def extractRecordFields (v : Value) : TCM (Array (String × Value)) := do
  match ← force v with
  | .vRecord row => extractRowFields row
  | _ => pure #[]
where
  extractRowFields (row : Value) : TCM (Array (String × Value)) := do
    match ← force row with
    | .vRowExtend (.vLabelLit name) ty rest =>
      let restFields ← extractRowFields rest
      return #[(name, ty)] ++ restFields
    | .vRowEmpty => return #[]
    | _ => return #[]

/-- Recursively check whether a Value contains an unsolved metavariable -/
private partial def valueContainsMeta : Value → Bool
  | .vNeutral ty neu => valueContainsMeta ty || neutralContainsMeta neu
  | .vDataType _ params => params.any valueContainsMeta
  | .vPi _ _ _ dom cod => valueContainsMeta dom || match cod with
    | .const _ v => valueContainsMeta v
    | .term _ _ _ => false -- can't inspect closure bodies
  | .vSigma _ _ fst snd => valueContainsMeta fst || match snd with
    | .const _ v => valueContainsMeta v
    | .term _ _ _ => false
  | .vPair a b => valueContainsMeta a || valueContainsMeta b
  | .vRowExtend l ft t => valueContainsMeta l || valueContainsMeta ft || valueContainsMeta t
  | .vRecord row => valueContainsMeta row
  | .vVariant row => valueContainsMeta row
  | .vConstructor _ _ args rty => args.any valueContainsMeta || valueContainsMeta rty
  | .vEq _ ty l r => valueContainsMeta ty || valueContainsMeta l || valueContainsMeta r
  | _ => false
where
  neutralContainsMeta (n : Neutral) : Bool :=
    headContainsMeta n.head || n.spine.any elimContainsMeta
  headContainsMeta : Head → Bool
    | .hMeta _ => true
    | .hVar _ => false
    | .hErrored => false
    | .hConst _ ty => valueContainsMeta ty
    | .hCase scrutinees _ rty =>
      scrutinees.any valueContainsMeta || valueContainsMeta rty
  elimContainsMeta : Elim → Bool
    | .eApp arg => valueContainsMeta arg
    | .eFst | .eSnd | .eField _ => false

/-- Build the record type for a constraint dict (class record type applied to args) -/
private partial def buildConstraintDictType (constraintClassId : Unique)
    (constraintArgs : Array Value) : TCM Value := do
  let classInfo? ← TCM.lookupClass constraintClassId
  match classInfo? with
  | some ci =>
    let mut rty := ci.recordType
    for arg in constraintArgs do
      match ← force rty with
      | .vPi _ _ _ _ cod => rty ← applyClosure cod arg
      | _ => pure ()
    pure rty
  | none => pure (Value.vType .zero)

/-- Constraint dict info for Expr-level substitution -/
structure ConstraintDictEntry where
  classId : Unique
  dictUnique : Unique
  dictTyExpr : Expr

/-- Resolve constraint dict metas in method bodies via Expr-level substitution -/
private def buildConstraintDictSubst
    (constraintDicts : Array ConstraintDictEntry)
    (pendingBefore : Nat)
    : TCM (Std.HashMap MetaId Expr) := do
  let pending ← TCM.getPendingInstances
  let mut subst : Std.HashMap MetaId Expr := {}
  for i in [pendingBefore:pending.size] do
    let p := pending[i]!
    if ← TCM.isMetaSolved p.metaId then continue
    -- Match this pending instance against our constraint dicts by class ID
    for entry in constraintDicts do
      if p.classId == entry.classId then
        let fvarExpr := Expr.fvar entry.dictUnique entry.dictTyExpr
        subst := subst.insert p.metaId fvarExpr
        -- Mark meta as solved to prevent error reporting
        let dictTy ← buildConstraintDictType entry.classId p.args
        let placeholderVal := Value.vNeutral dictTy
          (.nConst ⟨entry.dictUnique.id, entry.dictUnique.module, entry.dictUnique.original⟩
                   dictTy)
        TCM.solveMeta p.metaId placeholderVal (callerTag := "TraitElaborate.placeholder")
        break
  return subst

/-- Result of elaborating all instance methods -/
structure InstanceElabResult where
  /-- The instance record value -/
  value : Value
  /-- Typed functions for codegen -/
  typedFns : Array Soma.Core.TypedFunction
  /-- Method names paired with their lambda-wrapped Exprs (for rebuilding) -/
  methodExprs : Array (String × Expr)

/-- A single method body elaboration job -/
structure InstanceMethodJob where
  method : Soma.Core.UntypedFunction
  expectedType : Value

/-- The indirect-form result of instance skeleton elaboration -/
structure InstanceSkeleton where
  /-- Instance value in indirect form -/
  value : Value
  /-- Work remaining -/
  methodJobs : Array InstanceMethodJob
  /-- Method self-references for recursive calls within instance bodies -/
  selfRefs : Array (String × QualifiedName × Value)

/-- Build an indirect-form instance value -/
private def buildIndirectInstanceValue
    (jobs : Array InstanceMethodJob) : Value :=
  let fields := jobs.toList.map fun j =>
    let ty := j.expectedType
    (j.method.name.display, Value.vNeutral ty (.nConst j.method.name ty))
  Value.vRecordVal fields

/-- Shared body-elaboration core: given the already-matched jobs + selfRefs -/
partial def elaborateInstanceBodiesCore
    (jobs : Array InstanceMethodJob)
    (selfRefs : Array (String × QualifiedName × Value))
    (constraintDicts : Array ConstraintDictEntry := #[])
    : TCM InstanceElabResult := do
  let mut fields : List (String × Value) := []
  let mut typedFns : Array Soma.Core.TypedFunction := #[]
  let mut methodExprs : Array (String × Expr) := #[]
  for job in jobs do
    let method := job.method
    let expectedType := job.expectedType
    let methodName := method.name.display
    let pendingBefore := (← TCM.getPendingInstances).size
    let result ← TCM.withMethodSelfRefs selfRefs do
      elaborateMethodImpl method expectedType

    let (lambdaExpr, coreBody) ←
      if constraintDicts.isEmpty then
        pure (result.lambdaExpr, result.coreBody)
      else
        let subst ← buildConstraintDictSubst constraintDicts pendingBefore
        if subst.isEmpty then
          pure (result.lambdaExpr, result.coreBody)
        else
          pure (applyMvarSubst result.lambdaExpr subst,
                applyMvarSubst result.coreBody subst)

    fields := (methodName, result.value) :: fields
    methodExprs := methodExprs.push (methodName, lambdaExpr)
    typedFns := typedFns.push {
      name := method.name
      params := result.params
      body := coreBody
      fnType := result.fnType
      closureInfo := method.closureInfo
      attrs := method.attrs
    }

  return {
    value := Value.vRecordVal fields.reverse
    typedFns := typedFns
    methodExprs := methodExprs
  }

/-- Collect `InstanceMethodJob`s from a concrete class record type and the user-written methods -/
partial def collectInstanceMethodJobsFromClassInfo
    (classInfo : ClassInfo) (typeArgs : Array Value)
    (methods : Array Soma.Core.UntypedFunction)
    : TCM (Array InstanceMethodJob × Array (String × QualifiedName × Value)) := do
  let mut recordTy := classInfo.recordType
  for arg in typeArgs do
    match ← force recordTy with
    | .vPi _ _ _ _ cod => recordTy ← applyClosure cod arg
    | _ => pure ()
  let methodTypes ← extractRecordFields recordTy
  let mut jobs : Array InstanceMethodJob := #[]
  let mut selfRefs : Array (String × QualifiedName × Value) := #[]
  for method in methods do
    let methodName := method.name.display
    match methodTypes.find? (fun (name, _) => name == methodName) with
    | some (_, expectedType) =>
      jobs := jobs.push { method := method, expectedType := expectedType }
      selfRefs := selfRefs.push (methodName, method.name, expectedType)
    | none => pure ()
  pure (jobs, selfRefs)

/-- Build a stub instance value without elaborating method bodies -/
partial def elaborateInstanceSkeletonFromClassInfo
    (classInfo : ClassInfo) (typeArgs : Array Value)
    (methods : Array Soma.Core.UntypedFunction)
    : TCM InstanceSkeleton := do
  let (jobs, selfRefs) ← collectInstanceMethodJobsFromClassInfo classInfo typeArgs methods
  pure { value := buildIndirectInstanceValue jobs,
         methodJobs := jobs, selfRefs := selfRefs }

/-- Elaborate a full instance value (setup + body elab) -/
partial def elaborateInstanceValueFromClassInfo (classInfo : ClassInfo)
    (typeArgs : Array Value) (methods : Array Soma.Core.UntypedFunction)
    (constraintDicts : Array ConstraintDictEntry := #[])
    : TCM InstanceElabResult := do
  let (jobs, selfRefs) ← collectInstanceMethodJobsFromClassInfo classInfo typeArgs methods
  elaborateInstanceBodiesCore jobs selfRefs constraintDicts

/-- Result of eager constraint resolution -/
private inductive EagerResolutionResult where
  | resolved (dicts : Array (Unique × Value))
  | unresolvable

/-- Try to eagerly resolve all constraints -/
private def tryEagerResolution
    (constraints : Array (Unique × Array Value))
    : TCM EagerResolutionResult := do
  let mut resolvedDicts : Array (Unique × Value) := #[]
  for (constraintClassId, constraintArgs) in constraints do
    if constraintArgs.any valueContainsMeta then
      return .unresolvable
    let result ← Soma.Dependent.resolveInstance constraintClassId constraintArgs
    match result with
    | .found value _ =>
      resolvedDicts := resolvedDicts.push (constraintClassId, value)
    | _ =>
      return .unresolvable
  return .resolved resolvedDicts

/-- Elaborate an instance with eagerly-resolved constraints -/
private def elaborateWithEagerDicts
    (constraints : Array (Unique × Array Value))
    (resolvedDicts : Array (Unique × Value))
    (span : Span)
    (elabMethods : TCM InstanceElabResult)
    : TCM InstanceElabResult := do
  let mut resolvedInstEnv ← TCM.getInstanceEnv
  for (constraintClassId, constraintArgs) in constraints do
    let dictVal := resolvedDicts.find? (·.1 == constraintClassId) |>.map (·.2)
      |>.getD (Value.vType .zero)
    let tempInst : InstanceInfo := {
      instanceId := ← TCM.freshUnique s!"$resolved_{constraintClassId.original}"
      classId := constraintClassId
      args := constraintArgs
      constraints := #[]
      value := dictVal
      span := span
    }
    resolvedInstEnv ← resolvedInstEnv.addInstanceWithIdForced tempInst
  TCM.withInstanceEnv resolvedInstEnv elabMethods

/-- A constraint with an optional user-chosen dict name from instance binders. -/
private structure NamedConstraint where
  classId : Unique
  args : Array Value
  dictName? : Option String

/-- Full dictionary-passing elaboration for constrained instances -/
private def elaborateDictPassingInstance
    (constraints : Array NamedConstraint)
    (span : Span)
    (elabMethods : Array ConstraintDictEntry → TCM InstanceElabResult)
    : TCM (Value × Array Soma.Core.TypedFunction × Nat) := do
  -- 1. Create constraint dict bindings.
  let mut constraintDictBindings : Array (Unique × String × Value) := #[]
  let mut constraintDictEntries : Array ConstraintDictEntry := #[]
  let mut tempInstEnv ← TCM.getInstanceEnv
  for nc in constraints do
    let constraintClassId := nc.classId
    let constraintArgs := nc.args
    -- Use user-chosen name if available, otherwise generate one
    let dictName := match nc.dictName? with
      | some name => name
      | none => s!"$dict_{constraintClassId.original}"
    let dictUnique ← TCM.freshUnique dictName
    let dictTy ← buildConstraintDictType constraintClassId constraintArgs
    let dictTyExpr := Soma.Core.quoteExpr0 dictTy
    let dictVal := Value.vNeutral dictTy
      (.nConst ⟨dictUnique.id, dictUnique.module, dictName⟩ dictTy)
    constraintDictBindings := constraintDictBindings.push (dictUnique, dictName, dictTy)
    constraintDictEntries := constraintDictEntries.push {
      classId := constraintClassId
      dictUnique := dictUnique
      dictTyExpr := dictTyExpr
    }
    let tempInst : InstanceInfo := {
      instanceId := dictUnique
      classId := constraintClassId
      args := constraintArgs
      constraints := #[]
      value := dictVal
      span := span
    }
    tempInstEnv ← tempInstEnv.addInstanceWithIdForced tempInst

  -- 2. Elaborate methods within the modified instance env and bindings.
  let result ← TCM.withInstanceEnv tempInstEnv do
    let rec withConstraintBindings (idx : Nat) : TCM InstanceElabResult := do
      if idx >= constraintDictBindings.size then
        elabMethods constraintDictEntries
      else
        let (dictUnique, dictName, dictTy) := constraintDictBindings[idx]!
        TCM.withBinding dictName dictUnique dictTy .omega .instance_ span do
          withConstraintBindings (idx + 1)
    withConstraintBindings 0

  -- 3. Build the instance value: a lambda wrapping the method record.
  let recordExpr := Expr.record (result.methodExprs.map fun (name, expr) => (name, expr))
  let zonkedRecordExpr ← zonkExpr recordExpr

  let mut wrappedExpr := zonkedRecordExpr
  for i in [:constraintDictBindings.size] do
    let idx := constraintDictBindings.size - 1 - i
    let (dictUnique, dictName, dictTy) := constraintDictBindings[idx]!
    wrappedExpr := wrappedExpr.abstractFVar dictUnique
    let domTyExpr := Soma.Core.quoteExpr0 dictTy
    wrappedExpr := .lam .instance_ dictName domTyExpr wrappedExpr

  let instValue ← TCM.evalExpr wrappedExpr

  -- 4. Build TypedFunctions with dict params.
  let mut dictPassedFns := #[]
  for fn in result.typedFns do
    let mut body := fn.body
    let mut fnType := fn.fnType
    let mut extraParams : Array (Unique × String) := #[]
    for i in [:constraintDictBindings.size] do
      let idx := constraintDictBindings.size - 1 - i
      let (dictUnique, dictName, dictTy) := constraintDictBindings[idx]!
      body := body.abstractFVar dictUnique
      let domTyExpr := Soma.Core.quoteExpr0 dictTy
      body := .lam .instance_ dictName domTyExpr body
      fnType := .vPi .omega .instance_ dictName dictTy
        (.const dictName fnType)
      extraParams := #[(dictUnique, dictName)] ++ extraParams
    dictPassedFns := dictPassedFns.push {
      fn with
      body := body
      fnType := fnType
      params := extraParams ++ fn.params
    }

  return (instValue, dictPassedFns, constraints.size)

/-- Build an InstanceInfo from the common fields. -/
private def mkInstanceInfo (instUnique classId : Unique) (typeArgs : Array Value)
    (constraints : Array (Unique × Array Value)) (value : Value)
    (span : Span) (constraintDictCount : Nat := 0) : InstanceInfo := {
  instanceId := instUnique
  classId := classId
  args := typeArgs
  argQuantities := typeArgs.map (fun _ => .omega)
  constraints := constraints
  value := value
  constraintDictCount := constraintDictCount
  span := span
}

/-- Three-tier constrained instance elaboration strategy:
    1. No constraints → direct elaboration
    2. All constraints eagerly resolvable → inline resolved dicts
    3. Unresolvable constraints → full dictionary-passing -/
private def elaborateConstrainedInstance
    (classId instUnique : Unique) (typeArgs : Array Value)
    (namedConstraints : Array NamedConstraint) (span : Span)
    (elabSimple : TCM InstanceElabResult)
    (elabConstrained : Array ConstraintDictEntry → TCM InstanceElabResult)
    : TCM (InstanceInfo × Array Soma.Core.TypedFunction) := do
  let constraints := namedConstraints.map fun nc => (nc.classId, nc.args)
  if namedConstraints.isEmpty then
    let result ← elabSimple
    return (mkInstanceInfo instUnique classId typeArgs constraints result.value span,
            result.typedFns)
  else
    match ← tryEagerResolution constraints with
    | .resolved resolvedDicts =>
      let result ← elaborateWithEagerDicts constraints resolvedDicts span elabSimple
      return (mkInstanceInfo instUnique classId typeArgs constraints result.value span,
              result.typedFns)
    | .unresolvable =>
      let (instValue, dictPassedFns, dictCount) ←
        elaborateDictPassingInstance namedConstraints span elabConstrained
      return (mkInstanceInfo instUnique classId typeArgs constraints instValue span dictCount,
              dictPassedFns)

/-- Process instance binders into an elaboration environment and constraint list.

Explicit type variable binders `{a : Type}` create fresh metas in the elabEnv.
Instance dict binders `{{d : Display a}}` produce constraint entries for dict-passing,
preserving the user-chosen name for use in method bodies.
-/
private def processInstanceBinders (binders : Array Syntax.InstanceBinder)
    (baseEnv : ElabEnv := ElabEnv.empty)
    : TCM (ElabEnv × Array NamedConstraint) := do
  let mut elabEnv := baseEnv
  let mut constraints : Array NamedConstraint := #[]
  for binder in binders do
    match binder with
    | .typeVar name kind _ =>
      -- {a : Type} — create a fresh meta for this type variable
      let kindVal ← elaborateType elabEnv kind
      let metaVal ← TCM.freshMetaVal kindVal
      elabEnv := elabEnv.addOverride name.name metaVal
    | .dictParam name? constraint _ =>
      -- {{d : Display a}} or {{Display a}} — elaborate the constraint
      match ← elaborateConstraint constraint elabEnv with
      | some (cid, cargs) =>
        constraints := constraints.push {
          classId := cid, args := cargs, dictName? := name?.map (·.name)
        }
      | none => pure ()
  return (elabEnv, constraints)

partial def elaborateInstanceFromClassInfo (inst : Soma.Core.InstanceDecl)
    (classInfo : ClassInfo)
    : TCM (Option (InstanceInfo × Array Soma.Core.TypedFunction)) := do
  let (elabEnv, constraints) ← processInstanceBinders inst.binders
  let typeArgs ← inst.typeArgsSyntax.mapM (elaborateType elabEnv)

  let instUnique ← TCM.freshUnique s!"$inst_{inst.className.name}_{typeArgs.size}"

  let (instanceInfo, typedFns) ← elaborateConstrainedInstance
    classInfo.classId instUnique typeArgs constraints inst.span
    (elaborateInstanceValueFromClassInfo classInfo typeArgs inst.methods)
    (elaborateInstanceValueFromClassInfo classInfo typeArgs inst.methods ·)

  return some (instanceInfo, typedFns)

/-- Collect method elaboration jobs from method signatures + type args -/
def collectInstanceMethodJobs
    (typeArgs : Array Value) (methods : Array Soma.Core.UntypedFunction)
    (methodSignatures : Array (QualifiedName × Soma.Syntax.Expr))
    (params : Array TypeVarBinder)
    : TCM (Array InstanceMethodJob × Array (String × QualifiedName × Value)) := do
  let mut jobs : Array InstanceMethodJob := #[]
  let mut selfRefs : Array (String × QualifiedName × Value) := #[]
  for method in methods do
    match methodSignatures.find? (fun (name, _) => name.display == method.name.display) with
    | some (_, sigSyntax) =>
      let expectedType ← substituteMethodType sigSyntax params typeArgs
      jobs := jobs.push { method := method, expectedType := expectedType }
      selfRefs := selfRefs.push (method.name.display, method.name, expectedType)
    | none => pure ()
  pure (jobs, selfRefs)

/-- Skeleton variant of `elaborateInstanceValue` -/
def elaborateInstanceSkeleton
    (typeArgs : Array Value) (methods : Array Soma.Core.UntypedFunction)
    (methodSignatures : Array (QualifiedName × Soma.Syntax.Expr))
    (params : Array TypeVarBinder) : TCM InstanceSkeleton := do
  let (jobs, selfRefs) ← collectInstanceMethodJobs typeArgs methods methodSignatures params
  pure { value := buildIndirectInstanceValue jobs,
         methodJobs := jobs, selfRefs := selfRefs }

/-- Build the instance value (a record of method implementations -/
def elaborateInstanceValue (typeArgs : Array Value)
  (methods : Array Soma.Core.UntypedFunction)
    (methodSignatures : Array (QualifiedName × Soma.Syntax.Expr))
    (params : Array TypeVarBinder)
    (constraintDicts : Array ConstraintDictEntry := #[])
    : TCM InstanceElabResult := do
  let (jobs, selfRefs) ← collectInstanceMethodJobs typeArgs methods methodSignatures params
  elaborateInstanceBodiesCore jobs selfRefs constraintDicts

/-- Elaborate a single instance declaration into an InstanceInfo.
    Processes explicit binders for type variables and dictionary parameters,
    then delegates to the constrained instance elaboration pipeline. -/
def elaborateInstance (inst : Soma.Core.InstanceDecl)
  (typeClass : Soma.Core.TypeClassMeta) : TCM (Option (InstanceInfo × Array Soma.Core.TypedFunction)) := do
  match ← resolveClassName inst.className with
  | none => return none
  | some (_, _) =>
    let (elabEnv, constraints) ← processInstanceBinders inst.binders

    let typeArgs ← inst.typeArgsSyntax.mapM (elaborateType elabEnv)

    let instUnique ← TCM.freshUnique s!"$inst_{inst.className.name}_{typeArgs.size}"

    let elabSimple := elaborateInstanceValue typeArgs inst.methods
      typeClass.methodSignatures typeClass.params
    let (instanceInfo, typedFns) ← elaborateConstrainedInstance
      typeClass.name.id instUnique typeArgs constraints inst.span
      elabSimple
      (fun entries => elaborateInstanceValue typeArgs inst.methods
        typeClass.methodSignatures typeClass.params entries)

    return some (instanceInfo, typedFns)

/-- Build a method dispatch wrapper for a type class method -/
private def buildMethodWrapper (info : GlobalInfo) (methodNameStr : String)
    (fieldIdx : Nat) : TCM (Option TypedFunction) := do
  let mut wrapperParams : Array (Soma.Unique × String) := #[]
  let mut paramTyExprs : Array Soma.Core.Expr := #[]
  let mut paramIsExplicit : Array Bool := #[]
  let mut walkTy := info.type
  let mut dictUnique : Soma.Unique := ⟨0, "", "$dict"⟩
  let mut foundInstance := false
  let mut walking := true
  while walking do
    match walkTy with
    | .vPi _qty binder name dom cod =>
      let paramUnique ← TCM.freshUnique name
      let domExpr := Soma.Core.quoteExpr0 dom
      wrapperParams := wrapperParams.push (paramUnique, name)
      paramTyExprs := paramTyExprs.push domExpr
      if binder == .instance_ then
        dictUnique := paramUnique
        foundInstance := true
        paramIsExplicit := paramIsExplicit.push false
      else if binder.isImplicit then
        paramIsExplicit := paramIsExplicit.push false
      else
        paramIsExplicit := paramIsExplicit.push true
      walkTy := cod.applyPure (.vNeutral dom (.nVar ⟨name, ⟨0⟩⟩))
    | _ => walking := false
  if !foundInstance then return none

  -- Index of the dict parameter (first instance binder)
  let dictIdx := wrapperParams.findIdx? (fun (u, _) => u == dictUnique) |>.getD 0
  let dictTyExpr := paramTyExprs[dictIdx]?.getD (Soma.Core.Expr.sort .zero)

  let mut body : Soma.Core.Expr :=
    Soma.Core.Expr.fieldAccess
      (Soma.Core.Expr.fvar dictUnique dictTyExpr)
      methodNameStr
      fieldIdx
  for i in [dictIdx + 1 : wrapperParams.size] do
    if paramIsExplicit[i]? == some true then
      let (u, _) := wrapperParams[i]!
      let tyExpr := paramTyExprs[i]?.getD (Soma.Core.Expr.sort .zero)
      body := Soma.Core.Expr.app body (Soma.Core.Expr.fvar u tyExpr)

  return some {
    name := info.name
    params := wrapperParams
    body := body
    fnType := info.type
    closureInfo := none
    attrs := {}
  }

/-- Deferred body-elaboration work for a simple (no-constraint) instance -/
structure PendingInstanceBodies where
  /-- Unique identifier for the already-registered instance -/
  instanceId : Unique
  /-- The class this instance implements -/
  classId : Unique
  /-- Method bodies to elaborate -/
  jobs : Array InstanceMethodJob
  /-- Method self-references for mutual recursion within the instance -/
  selfRefs : Array (String × QualifiedName × Value)
  /-- Source span for error reporting -/
  span : Span
  /-- The instance env in scope at skeleton time -/
  instanceEnvSnapshot : InstanceEnv
  deriving Inhabited

/-- Skeleton path for an instance with no explicit constraints -/
partial def elaborateSimpleInstanceSkeleton
    (inst : Soma.Core.InstanceDecl) (classId instUnique : Unique)
    (typeArgs : Array Value)
    (methods : Array Soma.Core.UntypedFunction)
    (classInfo? : Option ClassInfo)
    (typeClass? : Option Soma.Core.TypeClassMeta)
    : TCM (InstanceInfo × PendingInstanceBodies) := do
  let (jobs, selfRefs) ← do
    match classInfo?, typeClass? with
    | some classInfo, _ =>
      collectInstanceMethodJobsFromClassInfo classInfo typeArgs methods
    | none, some typeClass =>
      collectInstanceMethodJobs typeArgs methods
        typeClass.methodSignatures typeClass.params
    | none, none =>
      pure (#[], #[])
  let indirectValue := buildIndirectInstanceValue jobs
  let instanceInfo := mkInstanceInfo instUnique classId typeArgs #[] indirectValue inst.span
  let envSnapshot ← TCM.getInstanceEnv
  let pending : PendingInstanceBodies := {
    instanceId := instUnique,
    classId := classId,
    jobs := jobs,
    selfRefs := selfRefs,
    span := inst.span,
    instanceEnvSnapshot := envSnapshot
  }
  return (instanceInfo, pending)

/-- Run body elaboration for a previously-registered simple instance -/
partial def runInstanceBodies
    (pending : PendingInstanceBodies)
    : TCM (Array Soma.Core.TypedFunction) := do
  TCM.withInstanceEnv pending.instanceEnvSnapshot do
    let result ← elaborateInstanceBodiesCore pending.jobs pending.selfRefs #[]
    return result.typedFns

private def mergeInstanceEnvs (local_ seed : InstanceEnv) : InstanceEnv := Id.run do
  let mergedClasses := local_.classes.fold (init := seed.classes)
    fun acc uid info => acc.insert uid info
  let mut mergedInstances := seed.instances
  let mut mergedIndices := seed.indices
  for (uid, insts) in local_.instances.toList do
    let existingInsts := mergedInstances.getD uid #[]
    let mut dedupedAdds : Array InstanceInfo := #[]
    for inst in insts do
      if !existingInsts.any (·.instanceId == inst.instanceId) then
        dedupedAdds := dedupedAdds.push inst
    mergedInstances := mergedInstances.insert uid (existingInsts ++ dedupedAdds)
    let existingIdx := mergedIndices.getD uid DiscrTree.empty
    let addedIdx := dedupedAdds.foldl (init := DiscrTree.empty) DiscrTree.insert
    mergedIndices := mergedIndices.insert uid (DiscrTree.merge existingIdx addedIdx)
  return {
    classes := mergedClasses
    instances := mergedInstances
    indices := mergedIndices
    moduleName := local_.moduleName
  }

/-- Try the skeleton path for an instance -/
private def trySimpleInstanceSkeleton
    (inst : Soma.Core.InstanceDecl) (classId : Unique)
    (classInfo? : Option ClassInfo)
    (typeClass? : Option Soma.Core.TypeClassMeta)
    : TCM (Option (InstanceInfo × PendingInstanceBodies)) := do
  let (elabEnv, constraints) ← processInstanceBinders inst.binders
  if !constraints.isEmpty then
    return none
  let typeArgs ← inst.typeArgsSyntax.mapM (elaborateType elabEnv)
  let instUnique ← TCM.freshUnique s!"$inst_{inst.className.name}_{typeArgs.size}"
  let (info, deferred) ← elaborateSimpleInstanceSkeleton
    inst classId instUnique typeArgs inst.methods classInfo? typeClass?
  return some (info, deferred)

def buildInstanceEnvFromModule (module : Soma.Core.UntypedModule)
    : TCM (InstanceEnv × InstanceMap × Array Soma.Core.TypedFunction
          × Array PendingInstanceBodies) := do
  let mut env := defaultInstanceEnv
  env := { env with moduleName := module.name }
  let mut instanceMap : InstanceMap := {}
  let mut allTypedFns : Array Soma.Core.TypedFunction := #[]

  let seedEnv ← TCM.getInstanceEnv
  for typeClass in module.typeClasses do
    let visible := mergeInstanceEnvs env seedEnv
    let classInfo ← TCM.withInstanceEnv visible (elaborateClass typeClass)
    env := env.addClass classInfo

  let mut pending : Array PendingInstanceBodies := #[]
  for inst in module.instances do
    let visible := mergeInstanceEnvs env seedEnv
    match ← TCM.withInstanceEnv visible (resolveClassName inst.className) with
    | none => pure ()
    | some (classQN, classInfo) =>
      let typeClass? := module.typeClasses.find? fun tc => tc.name.id == classQN.id
      let attemptSkeleton :=
        trySimpleInstanceSkeleton inst classInfo.classId
          (if typeClass?.isSome then none else some classInfo)
          typeClass?
      match ← TCM.withInstanceEnv visible attemptSkeleton with
      | some (instInfo, p) =>
        env ← env.addInstanceWithIdForced instInfo
        instanceMap := instanceMap.insert inst.span instInfo
        pending := pending.push p
      | none =>
        let attemptFull : TCM (Option (InstanceInfo × Array Soma.Core.TypedFunction)) :=
          match typeClass? with
          | some typeClass => elaborateInstance inst typeClass
          | none           => elaborateInstanceFromClassInfo inst classInfo
        match ← TCM.withInstanceEnv visible attemptFull with
        | some (instInfo, methodFns) =>
          env ← env.addInstanceWithIdForced instInfo
          instanceMap := instanceMap.insert inst.span instInfo
          allTypedFns := allTypedFns ++ methodFns
        | none => pure ()

  for typeClass in module.typeClasses do
    let mut idx := 0
    for (methodName, _) in typeClass.methodSignatures do
      match ← TCM.lookupGlobalByQN methodName with
      | some info =>
        if let some wrapper ← buildMethodWrapper info methodName.display idx then
          allTypedFns := allTypedFns.push wrapper
      | none => pure ()
      idx := idx + 1

  return (env, instanceMap, allTypedFns, pending)

/-- Run body elaboration for every pending instance from `buildInstanceEnvFromModule` -/
def runAllPendingInstanceBodies
    (pending : Array PendingInstanceBodies)
    : TCM (Array Soma.Core.TypedFunction) := do
  let mut allFns : Array Soma.Core.TypedFunction := #[]
  for p in pending do
    let fns ← runInstanceBodies p
    allFns := allFns ++ fns
  return allFns

/-- Build an InstanceEnv incrementally, reusing cached class/instance info for unchanged definitions -/
def buildInstanceEnvFromModuleIncremental
  (module : Soma.Core.UntypedModule)
    (prevEnv : InstanceEnv)
    (prevInstanceMap : InstanceMap)
    (dirtyNames : Std.HashSet String)
    : TCM (InstanceEnv × InstanceMap × Array Soma.Core.TypedFunction
          × Array PendingInstanceBodies) := do
  -- Start with the default built-in instances
  let mut env := defaultInstanceEnv
  env := { env with moduleName := module.name }
  let mut instanceMap : InstanceMap := {}
  let mut allTypedFns : Array Soma.Core.TypedFunction := #[]

  let seedEnv ← TCM.getInstanceEnv
  for typeClass in module.typeClasses do
    let className := typeClass.name.display

    if dirtyNames.contains className then
      let visible := mergeInstanceEnvs env seedEnv
      let classInfo ← TCM.withInstanceEnv visible (elaborateClass typeClass)
      env := env.addClass classInfo
    else
      -- Not dirty: try to reuse from previous env
      match prevEnv.classes.toList.find? (fun (_, info) => info.classId.original == className) with
      | some (_, classInfo) =>
        env := env.addClass classInfo
      | none =>
        let visible := mergeInstanceEnvs env seedEnv
        let classInfo ← TCM.withInstanceEnv visible (elaborateClass typeClass)
        env := env.addClass classInfo

  let elaborateOne (inst : Soma.Core.InstanceDecl) (visible : InstanceEnv)
      : TCM (Option (InstanceInfo × Array Soma.Core.TypedFunction)) :=
    TCM.withInstanceEnv visible do
      match ← resolveClassName inst.className with
      | none => return none
      | some (classQN, classInfo) =>
        let typeClass? := module.typeClasses.find? fun tc => tc.name.id == classQN.id
        match typeClass? with
        | some typeClass => elaborateInstance inst typeClass
        | none           => elaborateInstanceFromClassInfo inst classInfo

  for inst in module.instances do
    let instClassName := inst.className.name
    let isDirty := dirtyNames.contains instClassName
    if isDirty then
      let visible := mergeInstanceEnvs env seedEnv
      match ← elaborateOne inst visible with
      | some (instInfo, methodFns) =>
        env ← env.addInstanceWithIdForced instInfo
        instanceMap := instanceMap.insert inst.span instInfo
        allTypedFns := allTypedFns ++ methodFns
      | none => pure ()
    else
      match prevInstanceMap.get? inst.span with
      | some prevInst =>
        env ← env.addInstanceWithIdForced prevInst
        instanceMap := instanceMap.insert inst.span prevInst
      | none =>
        let visible := mergeInstanceEnvs env seedEnv
        match ← elaborateOne inst visible with
        | some (instInfo, methodFns) =>
          env ← env.addInstanceWithIdForced instInfo
          instanceMap := instanceMap.insert inst.span instInfo
          allTypedFns := allTypedFns ++ methodFns
        | none => pure ()

  -- Third pass: create wrapper TypedFunctions for class methods
  for typeClass in module.typeClasses do
    let mut idx := 0
    for (methodName, _) in typeClass.methodSignatures do
      match ← TCM.lookupGlobalByQN methodName with
      | some info =>
        if let some wrapper ← buildMethodWrapper info methodName.display idx then
          allTypedFns := allTypedFns.push wrapper
      | none => pure ()
      idx := idx + 1

  return (env, instanceMap, allTypedFns, #[])

end Soma.Dependent.TraitElaborate
