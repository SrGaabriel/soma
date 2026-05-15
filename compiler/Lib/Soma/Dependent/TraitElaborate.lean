import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Core.Quote
import Soma.Dependent.Monad
import Soma.Dependent.Elaborate
import Soma.Dependent.Infer
import Soma.Dependent.Instance
import Soma.Dependent.Telescope
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
  | .hCase scrutinees motive arms =>
    let scrutinees' ← scrutinees.mapM (substituteTypeArgsInValue · paramNames typeArgs depth)
    let motive' ← substituteTypeArgsInValue motive paramNames typeArgs depth
    return .hCase scrutinees' motive' arms

partial def substituteElim (e : Elim) (paramNames : Array String)
    (typeArgs : Array Value) (depth : Nat) : TCM Elim := do
  match e with
  | .eApp arg =>
    let arg' ← substituteTypeArgsInValue arg paramNames typeArgs depth
    return .eApp arg'
  | .eField n => return .eField n

end

Elaborate a type class (trait) declaration into a ClassInfo structure.
The record type for the class is built from the method signatures.
-/

/-- Build the dictionary record type for a class -/
def elaborateClassRecordType (typeClass : Soma.Core.TypeClassMeta)
  (methods : Array (QualifiedName × Soma.Syntax.Expr)) : TCM Value := do
  let params := typeClass.params
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
    let oldPostponed := (← TCM.getState).postponed
    let oldSet := oldPostponed.foldl
      (init := (∅ : Std.HashSet Soma.Core.ConstraintId))
      (fun acc tc => acc.insert tc.constraintId)
    let mut fields : List (String × Value) := []
    for (methodName, methodTypeSyntax) in methods do
      let expr ← Soma.Dependent.inferTypeExpr methodTypeSyntax
      let methodType ← TCM.evalExpr expr
      fields := (methodName.display, methodType) :: fields
    TCM.modifyState fun s =>
      let kept := s.postponed.filter (fun tc => oldSet.contains tc.constraintId)
      { s with postponed := kept }
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

  -- Build the dictionary record type
  let recordType ← elaborateClassRecordType typeClass typeClass.methodSignatures

  let typeParams := typeClass.params
  let supersOnly := typeClass.superclasses.map (·.2)
  let superclasses ← elaborateSuperclasses typeParams supersOnly

  return {
    classId := classUnique
    numParams := typeParams.size
    paramQuantities := typeParams.map (fun _ => Quantity.omega)
    recordType := recordType
    superclasses := superclasses
    span := Span.uninhabited
  }

/-- A constraint paired with the optional user-chosen dictionary name from an instance binder -/
structure NamedConstraint where
  classId : Unique
  args : Array Value
  dictName? : Option String

/-- Elaborate a constraint into (class Unique, arg Values). -/
def elaborateConstraint (constraint : Syntax.Constraint) (env : ElabEnv)
    : TCM (Option (Unique × Array Value)) := do
  match ← resolveClassName constraint.className with
  | none => return none
  | some (_, classInfo) =>
    let args ← constraint.args.mapM (elaborateType env)
    return some (classInfo.classId, args)

/-- Compute the super-class constraints implied by an instance -/
def superclassConstraintsForInstance
    (typeClass : Soma.Core.TypeClassMeta)
    (typeArgs : Array Value)
    (env : ElabEnv)
    : TCM (Array NamedConstraint) := do
  let typeParams := typeClass.params
  let mut env' := env
  for (param, arg) in typeParams.zip typeArgs do
    env' := env'.addOverride param.name.name arg
  let mut result : Array NamedConstraint := #[]
  for (name?, cstr) in typeClass.superclasses do
    match ← elaborateConstraint cstr env' with
    | some (cid, cargs) =>
      result := result.push {
        classId := cid, args := cargs, dictName? := name?.map (·.name)
      }
    | none => pure ()
  return result

/-- Validate that an instance body provides exactly the methods declared on the class -/
def validateInstanceMethodSet
    (className : String) (instSpan : Syntax.Span)
    (methodSignatures : Array (QualifiedName × Soma.Syntax.Expr))
    (methods : Array Soma.Core.UntypedFunction)
    : TCM Unit := do
  let knownNames := methodSignatures.map (·.1.display)
  let providedNames := methods.map (·.name.display)
  for method in methods do
    let nm := method.name.display
    unless knownNames.contains nm do
      TCM.addError (.unknownInstanceMethod className nm knownNames method.span)
  let missing := knownNames.filter fun n => !providedNames.contains n
  unless missing.isEmpty do
    TCM.addError (.missingInstanceMethods className missing instSpan)

/-- Recursively check whether a Value contains an unsolved metavariable -/
private partial def valueContainsMeta : Value → Bool
  | .vNeutral ty neu => valueContainsMeta ty || neutralContainsMeta neu
  | .vDataType _ params => params.any valueContainsMeta
  | .vPi _ _ _ dom cod => valueContainsMeta dom || match cod with
    | .const _ v => valueContainsMeta v
    | .term _ _ _ => false -- can't inspect closure bodies
  | .vRowExtend l ft t => valueContainsMeta l || valueContainsMeta ft || valueContainsMeta t
  | .vRecord row => valueContainsMeta row
  | .vVariant row => valueContainsMeta row
  | .vConstructor _ _ args rty => args.any valueContainsMeta || valueContainsMeta rty
  | _ => false
where
  neutralContainsMeta (n : Neutral) : Bool :=
    headContainsMeta n.head || n.spine.any elimContainsMeta
  headContainsMeta : Head → Bool
    | .hMeta _ => true
    | .hVar _ => false
    | .hErrored => false
    | .hConst _ ty => valueContainsMeta ty
    | .hCase scrutinees motive _ =>
      scrutinees.any valueContainsMeta || valueContainsMeta motive
  elimContainsMeta : Elim → Bool
    | .eApp arg => valueContainsMeta arg
    | .eField _ => false

/-- Substitute instance type arguments into a method signature -/
def substituteMethodType (methodTypeSyntax : Soma.Syntax.Expr)
    (typeClass : Soma.Core.TypeClassMeta) (typeArgs : Array Value) : TCM Value := do
  let params := typeClass.params
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
    let superclasses := typeClass.superclasses
    let mut scBindings : Array (Soma.Unique × String × Value × Unique × Array Value × Option Value) := #[]
    for (nameOpt, cstr) in superclasses do
      let head : Soma.Syntax.Expr := .con cstr.className
      let appExpr := cstr.args.foldl
        (fun acc a => Soma.Syntax.Expr.app acc a cstr.span) head
      let cstrTyExpr ← Soma.Dependent.inferTypeExpr appExpr
      let cstrTy ← TCM.evalExpr cstrTyExpr
      let dictName := match nameOpt with
        | some n => n.name
        | none => s!"$super_{cstr.className.name}"
      let dictUnique ← TCM.freshLocalId dictName
      let forcedTy ← Soma.Dependent.force cstrTy
      match Soma.Dependent.extractClassInfo forcedTy with
      | some (classId, classArgs) =>
        let resolvedValue? : Option Value ← do
          if classArgs.any valueContainsMeta then
            pure none
          else
            match ← Soma.Dependent.resolveInstance classId classArgs with
            | .found v _ => pure (some v)
            | _ => pure none
        scBindings := scBindings.push
          (dictUnique, dictName, cstrTy, classId, classArgs, resolvedValue?)
      | none => pure ()

    let classNameStr := typeClass.name.display
    let ns ← TCM.getCurrentNamespace
    let ctx ← TCM.getCtx
    let selfBindingOpt :
        Option (Soma.Unique × String × Value × Unique × Array Value × Option Value) := ←
      match ctx.globals.resolve ns #[] classNameStr with
      | none => pure none
      | some classQN => do
        let selfArgs := typeArgs
        let selfTy : Value := Value.vDataType classQN.id selfArgs.toList
        let selfDictName := "$self"
        let selfDictUnique ← TCM.freshLocalId selfDictName
        pure (some (selfDictUnique, selfDictName, selfTy, classQN.id, selfArgs, none))

    let allBindings := match selfBindingOpt with
      | some sb => scBindings.push sb
      | none => scBindings

    let rec withSCs (idx : Nat) : TCM Value := do
      if idx >= allBindings.size then
        -- Snapshot the older constraints so we can isolate the constraints we introduce here
        let oldPostponed := (← TCM.getState).postponed
        let oldSet := oldPostponed.foldl
          (init := (∅ : Std.HashSet Soma.Core.ConstraintId))
          (fun acc tc => acc.insert tc.constraintId)
        let expr ← Soma.Dependent.inferTypeExpr methodTypeSyntax
        TCM.modifyState fun s =>
          let kept := s.postponed.filter (fun tc => !oldSet.contains tc.constraintId)
          { s with postponed := kept }
        let report ← Soma.Dependent.solveConstraintsSoft
        report.allowPostponed
        TCM.modifyState fun s =>
          { s with postponed := oldPostponed ++ s.postponed }
        TCM.evalExpr expr
      else
        let (dictUnique, dictName, dictTy, _, _, resolvedValue?) := allBindings[idx]!
        match resolvedValue? with
        | some resolvedValue =>
          Soma.Dependent.withResolvedInstanceBinding dictName dictUnique dictTy
            resolvedValue .omega Span.uninhabited (withSCs (idx + 1))
        | none =>
          Soma.Dependent.withLocalInstanceBinding dictName dictUnique dictTy
            .omega Span.uninhabited (withSCs (idx + 1))
    termination_by allBindings.size - idx

    withSCs 0

  let methodType : TCM Value := do
    let rec wrap (i : Nat) : TCM Value := do
      if i >= bindings.size then go
      else
        let (uid, name, kind) := bindings[i]!
        let valueArg :=
          if h : i < typeArgs.size then typeArgs[i]
          else Value.vNeutral kind (.nVar ⟨name, ⟨0⟩⟩)
        TCM.withBindingValue name uid kind .omega .implicit Span.uninhabited
          valueArg (wrap (i + 1))
    termination_by bindings.size - i
    wrap 0
  let resolved ← methodType

  let zonked ← zonkValue resolved

  substituteTypeArgsInValue zonked paramNames typeArgs 0

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
  /-- Full NbE value telescope, including erased implicit and instance binders -/
  valueParams : Array (Unique × String × BinderInfo) := #[]

/-- Extract the part of a method signature needed to check the source body -/
private partial def extractMethodSignaturePrefix (ty : Value) (explicitCount : Nat)
    : TCM (Array (String × Value × BinderInfo × Quantity) × Value) := do
  let startLvl ← TCM.currentLevel
  go ty explicitCount startLvl.lvl
where
  go (ty : Value) (remainingExplicit : Nat) (lvl : Nat)
      : TCM (Array (String × Value × BinderInfo × Quantity) × Value) := do
    let ty' ← force ty
    match ty' with
    | .vPi qty binder name dom cod =>
      if remainingExplicit == 0 && !binder.isImplicit then
        return (#[], ty')
      let neutral := Value.vNeutral dom (.nVar ⟨name, ⟨lvl⟩⟩)
      let codTy ← applyClosure cod neutral
      let remainingExplicit' :=
        if binder.isImplicit then remainingExplicit else remainingExplicit - 1
      let (rest, resultTy) ← go codTy remainingExplicit' (lvl + 1)
      return (#[(name, dom, binder, qty)] ++ rest, resultTy)
    | _ =>
      return (#[], ty')

/-- Bind a method-signature prefix for body checking -/
private def withMethodSignaturePrefix
    (sigPrefix : Array (String × Value × BinderInfo × Quantity))
    (explicitNames : Array String)
    (span : Span)
    (action : TCM α)
    : TCM (Array (Unique × String) × Array (Unique × String × BinderInfo) × α) := do
  let mut runtimeParams : Array (Unique × String) := #[]
  let mut valueParams : Array (Unique × String × BinderInfo) := #[]
  let mut binders : Array (Unique × String × Value × BinderInfo × Quantity) := #[]
  let mut explicitIdx : Nat := 0
  for (sigName, ty, binder, qty) in sigPrefix do
    let mut name := sigName
    if !binder.isImplicit then
      name := explicitNames[explicitIdx]?.getD sigName
      explicitIdx := explicitIdx + 1
    let uid ← TCM.freshLocalId name
    binders := binders.push (uid, name, ty, binder, qty)
    valueParams := valueParams.push (uid, name, binder)
    if !binder.isImplicit then
      runtimeParams := runtimeParams.push (uid, name)

  let rec bindAll (idx : Nat) : TCM α := do
    if idx >= binders.size then
      action
    else
      let (uid, name, ty, binder, qty) := binders[idx]!
      Soma.Dependent.withCheckedBinding name uid ty qty binder span do
        if binder == .instance_ then
          Soma.Dependent.withLocalInstanceForBoundDict name uid ty span (bindAll (idx + 1))
        else
          bindAll (idx + 1)
  termination_by binders.size - idx

  let result ← bindAll 0
  return (runtimeParams, valueParams, result)

/-- Elaborate a method implementation.

Type-checks the method body against the expected (substituted) signature
and returns the elaborated value -/
def elaborateMethodImpl (methodFn : Soma.Core.UntypedFunction) (expectedType : Value)
    : TCM MethodElabResult := do
  let (sigPrefix, resultType) ← extractMethodSignaturePrefix expectedType methodFn.params.size

  let (generatedParams, valueParams, coreBody) ←
    withMethodSignaturePrefix sigPrefix (methodFn.params.map (·.name)) methodFn.span do
      let bodyIsProof ← Soma.Dependent.valueInPropUniverse resultType
      let checked ←
        if bodyIsProof then
          TCM.inErasedContext (Soma.Dependent.checkSyntax methodFn.body resultType)
        else
          Soma.Dependent.checkSyntax methodFn.body resultType
      Soma.Dependent.drainConstraints
      pure checked

  let coreBody' ← zonkExpr coreBody
  let expectedType' ← zonkValue expectedType

  -- Build the unfoldable method value over the full semantic telescope
  let mut lambdaExpr := coreBody'
  for i in [:valueParams.size] do
    let idx := valueParams.size - 1 - i
    let (paramId, paramName, binderInfo) := valueParams[idx]!
    lambdaExpr := lambdaExpr.abstractFVar paramId
    lambdaExpr := .lam binderInfo paramName (Expr.sort Level.zero) lambdaExpr
  let methodVal ← TCM.evalExpr lambdaExpr

  return {
    value := methodVal
    coreBody := coreBody'
    lambdaExpr := lambdaExpr
    fnType := expectedType'
    params := generatedParams
    valueParams := valueParams
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
      valueParams := result.valueParams
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
    (typeClass : Soma.Core.TypeClassMeta)
    : TCM (Array InstanceMethodJob × Array (String × QualifiedName × Value)) := do
  let mut jobs : Array InstanceMethodJob := #[]
  let mut selfRefs : Array (String × QualifiedName × Value) := #[]
  for method in methods do
    match methodSignatures.find? (fun (name, _) => name.display == method.name.display) with
    | some (_, sigSyntax) =>
      let expectedType ← substituteMethodType sigSyntax typeClass typeArgs
      jobs := jobs.push { method := method, expectedType := expectedType }
      selfRefs := selfRefs.push (method.name.display, method.name, expectedType)
    | none => pure ()
  pure (jobs, selfRefs)

/-- Build the instance value (a record of method implementations -/
def elaborateInstanceValue (typeArgs : Array Value)
  (methods : Array Soma.Core.UntypedFunction)
    (methodSignatures : Array (QualifiedName × Soma.Syntax.Expr))
    (typeClass : Soma.Core.TypeClassMeta)
    (constraintDicts : Array ConstraintDictEntry := #[])
    : TCM InstanceElabResult := do
  let (jobs, selfRefs) ← collectInstanceMethodJobs typeArgs methods methodSignatures typeClass
  elaborateInstanceBodiesCore jobs selfRefs constraintDicts

/-- Elaborate a single instance declaration into an InstanceInfo.
    Processes explicit binders for type variables and dictionary parameters,
    then delegates to the constrained instance elaboration pipeline. -/
def elaborateInstance (inst : Soma.Core.InstanceDecl)
  (typeClass : Soma.Core.TypeClassMeta) : TCM (Option (InstanceInfo × Array Soma.Core.TypedFunction)) := do
  match ← resolveClassName inst.className with
  | none => return none
  | some (_, _) =>
    let (elabEnv, userConstraints) ← processInstanceBinders inst.binders

    let typeArgs ← inst.typeArgsSyntax.mapM (elaborateType elabEnv)

    let superConstraints ← superclassConstraintsForInstance typeClass typeArgs elabEnv
    for nc in superConstraints do
      if !(nc.args.any valueContainsMeta) then
        match ← Soma.Dependent.resolveInstance nc.classId nc.args with
        | .found _ _ => pure ()
        | _ =>
          TCM.addError (.noInstance nc.classId nc.args inst.span #[] #[])

    let constraints := userConstraints ++ superConstraints

    let instUnique ← TCM.freshUnique s!"$inst_{inst.className.name}_{typeArgs.size}"

    let elabSimple := elaborateInstanceValue typeArgs inst.methods
      typeClass.methodSignatures typeClass
    let (instanceInfo, typedFns) ← elaborateConstrainedInstance
      typeClass.name.id instUnique typeArgs constraints inst.span
      elabSimple
      (fun entries => elaborateInstanceValue typeArgs inst.methods
        typeClass.methodSignatures typeClass entries)

    return some (instanceInfo, typedFns)

/-- Build a method dispatch wrapper for a type class method -/
private def buildMethodWrapper (info : GlobalInfo) (methodNameStr : String)
    (fieldIdx : Nat) : TCM (Option TypedFunction) := do
  let mut runtimeParams : Array (Soma.Unique × String) := #[]
  let mut allValueParams : Array (Soma.Unique × String × Soma.Core.BinderInfo) := #[]
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
      paramTyExprs := paramTyExprs.push domExpr
      allValueParams := allValueParams.push (paramUnique, name, binder)
      let isErasedImplicitTyParam : Bool :=
        match binder with
        | .implicit | .strictImplicit =>
          match dom with
          | .vType _ | .vRowSort | .vLabelSort => true
          | _ => false
        | _ => false
      paramIsExplicit := paramIsExplicit.push (binder == .explicit)
      if binder == .instance_ then
        dictUnique := paramUnique
        foundInstance := true
      if !isErasedImplicitTyParam then
        runtimeParams := runtimeParams.push (paramUnique, name)
      walkTy := cod.applyPure (.vNeutral dom (.nVar ⟨name, ⟨0⟩⟩))
    | _ => walking := false
  if !foundInstance then return none

  -- Locate the `$dict` parameter inside the all-binders array
  let allDictIdx := allValueParams.findIdx? (fun (u, _, _) => u == dictUnique) |>.getD 0
  let dictTyExpr := paramTyExprs[allDictIdx]?.getD (Soma.Core.Expr.sort .zero)

  let mut body : Soma.Core.Expr :=
    Soma.Core.Expr.fieldAccess
      (Soma.Core.Expr.fvar dictUnique dictTyExpr)
      methodNameStr
      fieldIdx
  for i in [allDictIdx + 1 : allValueParams.size] do
    if paramIsExplicit[i]? == some true then
      let (u, _, _) := allValueParams[i]!
      let tyExpr := paramTyExprs[i]?.getD (Soma.Core.Expr.sort .zero)
      body := Soma.Core.Expr.app body (Soma.Core.Expr.fvar u tyExpr)

  return some {
    name := info.name
    params := runtimeParams
    valueParams := allValueParams
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
        typeClass.methodSignatures typeClass
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
  let hasSupers := match typeClass? with
    | some tc => !tc.superclasses.isEmpty
    | none =>
      match classInfo? with
      | some ci => !ci.superclasses.isEmpty
      | none    => false
  if hasSupers then
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
      if let some typeClass := typeClass? then
        TCM.withInstanceEnv visible <|
          validateInstanceMethodSet inst.className.name inst.span
            typeClass.methodSignatures inst.methods
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
        for prior in pending do
          let bodyResult ← TCM.withInstanceEnv prior.instanceEnvSnapshot do
            elaborateInstanceBodiesCore prior.jobs prior.selfRefs #[]
          match instanceMap.get? prior.span with
          | some priorSkel =>
            let realInfo := { priorSkel with value := bodyResult.value }
            env := env.replaceInstanceWithId realInfo
            instanceMap := instanceMap.insert prior.span realInfo
          | none => pure ()
          allTypedFns := allTypedFns ++ bodyResult.typedFns
        pending := #[]
        let visible' := mergeInstanceEnvs env seedEnv
        let attemptFull : TCM (Option (InstanceInfo × Array Soma.Core.TypedFunction)) :=
          match typeClass? with
          | some typeClass => elaborateInstance inst typeClass
          | none           => elaborateInstanceFromClassInfo inst classInfo
        match ← TCM.withInstanceEnv visible' attemptFull with
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
