import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Quote
import Soma.Core.Eval
import Soma.Core.Primitive
import Soma.Core.Expr
import Soma.Dependent.Prelude
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Unify
import Soma.Dependent.Error
import Soma.Dependent.Usage
import Soma.Dependent.Elaborate
import Soma.Syntax.Ast

namespace Soma.Dependent

open Soma (Unique)
open Soma.Core
open Soma.Syntax (Span)

/-- Try to unify two values, returning true if successful, false if unification fails -/
def tryUnify (v1 v2 : Value) : TCM Bool := do
  -- Save the current state
  let state ← get
  try
    unify v1 v2
    return true
  catch _ =>
    -- Restore state on failure
    set state
    return false

/-- Get the universe level of a type, creating a fresh level var if needed -/
def inferUniverse (ty : Value) : TCM Level := do
  match ty with
  | .vType l => return l
  | _ =>
    -- If it's not obviously a Type, create a fresh level variable
    TCM.freshLevel "u"

/-- Ensure a value is a type (has type Type) -/
def ensureType (v : Value) (span : Span) (context : Option String := none) : TCM Level := do
  let v' ← force v
  match v' with
  | .vType l => return l
  | .vNeutral (.vType l) _ => return l
  | _ =>
    TCM.throw (.expectedType v' span context)

/-- Ensure a value is a Pi type -/
def ensurePi (v : Value) (span : Span) (origin : Option ConstraintOrigin := none)
    : TCM (Quantity × BinderInfo × String × Value × Closure) := do
  let v' ← force v
  match v' with
  | .vPi qty binder name dom cod => return (qty, binder, name, dom, cod)
  | _ =>
    TCM.throw (.expectedFunction v' span origin)

/-- Ensure a value is a Sigma type -/
def ensureSigma (v : Value) (span : Span) (origin : Option ConstraintOrigin := none)
    : TCM (Quantity × String × Value × Closure) := do
  let v' ← force v
  match v' with
  | .vSigma qty name fst snd => return (qty, name, fst, snd)
  | _ => TCM.throw (.expectedSigma v' span origin)

/-- Apply a motive value to an argument.
    Used for transport where we have P : A -> Type and want P x. -/
def vAppMotive (motive : Value) (arg : Value) : TCM Value := do
  match motive with
  | .vLam _ body =>
    applyClosure body arg
  | .vPi _ _ _ _ cod =>
    -- If motive is a Pi type, apply the codomain closure
    applyClosure cod arg
  | .vNeutral ty neu =>
    -- Stuck application
    return .vNeutral ty (.nApp neu arg)
  | _ =>
    -- For other values, create a stuck application
    return .vNeutral .type0 (.nApp (.nVar ⟨"_motive", ⟨0⟩⟩) arg)

/-- Extract class information from a type that represents a type class constraint.
    Returns the class unique ID and type arguments if the type is a class application. -/
def extractClassInfo (ty : Value) : Option (Unique × Array Value) := do
  match ty with
  | .vDataType unique args =>
    return (unique, args.toArray)
  | _ => none

/-- Insert implicit arguments for a function type, tracking created metavariables.
    Returns (resultType, wrappedCoreExpr, createdMetas). -/
partial def insertImplicitsCore (fnTy : Value) (fnExpr : Soma.Core.Expr) (span : Span)
    : TCM (Value × Soma.Core.Expr × Array (MetaId × Value × String)) := do
  let fnTy' ← force fnTy
  match fnTy' with
  | .vPi _qty binder name dom cod =>
    if binder.isImplicit then
      -- Create metavariable for this implicit parameter
      let metaId ← TCM.freshMeta dom
      let argMeta := Value.vNeutral dom (.nMeta metaId)

      -- Handle instance parameters specially
      if binder == .instance_ then
        let forcedDom ← force dom
        match extractClassInfo forcedDom with
        | some (classId, args) =>
          TCM.addPendingInstance classId args metaId span
        | none =>
          TCM.addDeferredInstanceMeta metaId dom span

      -- Apply the function to the metavariable
      let resultTy ← applyClosure cod argMeta
      let argExpr := Soma.Core.Expr.mvar metaId
      let appExpr := Soma.Core.Expr.app fnExpr argExpr

      -- Recursively insert more implicits, accumulating metas
      let (finalTy, finalExpr, restMetas) ← insertImplicitsCore resultTy appExpr span
      return (finalTy, finalExpr, #[(metaId, dom, name)] ++ restMetas)
    else
      -- Explicit argument: stop inserting implicits
      return (fnTy', fnExpr, #[])
  | _ => return (fnTy', fnExpr, #[])

/-- Insert implicit arguments, discarding created meta tracking info -/
partial def insertImplicits (fnTy : Value) (fnExpr : Soma.Core.Expr) (span : Span)
    : TCM (Value × Soma.Core.Expr) := do
  let (ty, expr, _) ← insertImplicitsCore fnTy fnExpr span
  return (ty, expr)

/-- Project the result type after consuming n explicit arguments, reusing existing metas.
    This ensures that when we unify the projected result type with an expected type,
    the constraints properly connect to the metas that will be used in the actual application -/
partial def projectResultTypeWithMetas (ty : Value) (numExplicitArgs : Nat)
    (existingMetas : Array (MetaId × Value × String)) : TCM (Option Value) := do
  if numExplicitArgs == 0 then
    return some ty

  let ty' ← force ty
  match ty' with
  | .vPi _qty binder name dom cod =>
    if binder.isImplicit then
      -- Find the corresponding meta from existingMetas if available
      let metaVal ← match existingMetas.find? (fun (_, _, n) => n == name) with
        | some (mid, _, _) => pure (Value.vNeutral dom (.nMeta mid))
        | none => TCM.freshMetaVal dom  -- Fallback to fresh meta
      let resultTy ← applyClosure cod metaVal
      projectResultTypeWithMetas resultTy numExplicitArgs existingMetas
    else
      -- Consume one explicit argument with a placeholder
      let lvl ← TCM.currentLevel
      let argVal := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
      let resultTy ← applyClosure cod argVal
      projectResultTypeWithMetas resultTy (numExplicitArgs - 1) existingMetas
  | _ => return none

/-- Single pass of greedy constraint solving -/
def solveImplicitsGreedyPass : TCM Bool := do
  let constraints ← TCM.getPostponedTracked
  if constraints.isEmpty then return false

  -- Sort constraints by complexity (fewer unsolved metas first)
  let sortedConstraints ← constraints.mapM fun tc => do
    let mut unsolvedCount := 0
    for mid in tc.metas do
      let solved ← TCM.isMetaSolved mid
      if !solved then unsolvedCount := unsolvedCount + 1
    return (tc, unsolvedCount)

  let prioritized := sortedConstraints.qsort (fun (_, c1) (_, c2) => c1 < c2)

  -- Track which metas we solve
  let mut solvedMetas : Array MetaId := #[]
  let mut madeProgress := false

  TCM.clearPostponed

  for (tc, _) in prioritized do
    match tc.constraint with
    | .unify v1 v2 constraintSpan =>
      let v1' ← force v1
      let v2' ← force v2
      let success ← tryUnify v1' v2'
      if success then
        madeProgress := true
        for mid in tc.metas do
          let solved ← TCM.isMetaSolved mid
          if solved && !solvedMetas.contains mid then
            solvedMetas := solvedMetas.push mid
      else
        let _ ← TCM.postponeTracked (.unify v1' v2' constraintSpan) tc.metas
    | other =>
      TCM.postpone other

  -- Wake constraints that depend on solved metas
  for mid in solvedMetas do
    TCM.wakeConstraintsFor mid

  return madeProgress

/-- Solve implicit arguments greedily using dependency-aware constraint solving.
    Uses fuel to avoid infinite recursion -/
def solveImplicitsGreedy : TCM Unit := do
  -- Use fuel-based iteration instead of direct recursion
  let mut fuel := maxGreedySolveIterations
  let mut progress := true
  while progress && fuel > 0 do
    fuel := fuel - 1
    progress ← solveImplicitsGreedyPass

/-- Propagate type information from an argument back to solve implicits in the function -/
def propagateFromArgument (argTy : Value) (expectedDom : Value) : TCM Unit := do
  let _ ← tryUnify argTy expectedDom
  solveImplicitsGreedy

/-- Insert implicit arguments with expected type guidance and full bidirectional propagation -/
partial def insertImplicitsWithExpected (fnTy : Value) (fnExpr : Soma.Core.Expr)
    (expected : Option Value) (numExplicitArgs : Nat) (span : Span)
    : TCM (Value × Soma.Core.Expr) := do
  -- Insert implicits and track the metas created
  let (fnTy', fnExpr', implicitMetas) ← insertImplicitsCore fnTy fnExpr span

  -- If we have an expected type, use it to solve implicits early
  match expected with
  | none =>
    solveImplicitsGreedy
    let finalTy ← force fnTy'
    return (finalTy, fnExpr')
  | some expectedTy =>
    -- Project result type using the SAME metas we just created
    match ← projectResultTypeWithMetas fnTy' numExplicitArgs implicitMetas with
    | some resultTy =>
      -- Unify projected result with expected type
      let _ ← tryUnify resultTy expectedTy
      solveImplicitsGreedy
      let finalTy ← force fnTy'
      return (finalTy, fnExpr')
    | none =>
      solveImplicitsGreedy
      let finalTy ← force fnTy'
      return (finalTy, fnExpr')

/-- Check if we can solve a meta from the expected type -/
def trySolveMetaFromExpected (metaId : MetaId) (expected : Value) : TCM Bool := do
  match ← TCM.lookupMeta metaId with
  | some info =>
    match info.solution with
    | some _ => return false
    | none =>
      let metaVal := Value.vNeutral info.type (.nMeta metaId)
      let success ← tryUnify metaVal expected
      if success then solveImplicitsGreedy
      return success
  | none => return false

/-- Aggressively propagate type information during inference -/
def propagateTypeInfo (inferredTy : Value) (targetTy : Value) : TCM Unit := do
  unify inferredTy targetTy
  solveImplicitsGreedy


/-- Build nested Core lambdas from `(fvar, name, domainExpr)` bindings. -/
partial def buildLambdas (bindings : List (Unique × String × Soma.Core.Expr))
    (body : Soma.Core.Expr) : Soma.Core.Expr :=
  match bindings with
  | [] => body
  | (fvar, name, domExpr) :: rest =>
    let innerBody := buildLambdas rest body
    let closedBody := Soma.Core.Expr.abstractFVar innerBody fvar
    .lam .explicit name domExpr closedBody

/-- Quote a `Value` to a Core `Expr`. -/
partial def quoteValueToExpr (v : Value) : TCM Soma.Core.Expr := do
  let depth ← TCM.currentLevel
  return Soma.Core.quoteExpr depth v

/-- Elaborate an explicit type application argument (`@T` or `@label`). -/
partial def elaborateTypeArg (typeArg : Soma.Syntax.TypeAppArg) : TCM Value := do
  match typeArg with
  | .label labelName =>
    match ← TCM.lookupLocal labelName.value with
    | some entry =>
      pure (Value.vNeutral entry.type (Neutral.nVar ⟨labelName.value, entry.level⟩))
    | none =>
      pure (Value.vLabelLit labelName.value)
  | .type tyExpr =>
    Elaborate.elaborateType Elaborate.ElabEnv.empty tyExpr

/-- Infer explicit type application to an implicit parameter (`f @T`). -/
partial def inferExplicitTypeApp
    (fnExpr : Soma.Core.Expr) (cod : Closure)
    (typeArg : Soma.Syntax.TypeAppArg) (_argSpan : Span) (_callSpan : Span)
    : TCM (Value × Soma.Core.Expr) := do
  let argVal ← elaborateTypeArg typeArg
  let resultTy ← applyClosure cod argVal
  let argExpr ← quoteValueToExpr argVal
  let appExpr := Soma.Core.Expr.app fnExpr argExpr
  return (resultTy, appExpr)

/-- Instantiate all leading implicit binders in a type with fresh metas. -/
partial def instantiateImplicits (ty : Value) (_span : Span) : TCM Value := do
  let ty' ← force ty
  match ty' with
  | .vPi _qty binder _name dom cod =>
    if binder.isImplicit then
      let metaVal ← TCM.freshMetaVal dom
      let resultTy ← applyClosure cod metaVal
      instantiateImplicits resultTy Span.uninhabited
    else
      return ty'
  | _ =>
    return ty'

/-- Check if two forced values are structurally incompatible (distinct head constructors) -/
partial def structurallyIncompatible (v1 v2 : Value) : TCM Bool := do
  let v1' ← force v1
  let v2' ← force v2
  match v1', v2' with
  | .vConstructor n1 _ _ _, .vConstructor n2 _ _ _ => return n1 != n2
  | .vIntLit n1, .vIntLit n2 => return n1 != n2
  | .vStringLit s1, .vStringLit s2 => return s1 != s2
  | .vPrimTy p1, .vPrimTy p2 => return p1 != p2
  | .vDataType id1 ps1, .vDataType id2 ps2 =>
    if id1 != id2 then return true
    let rec checkParams (l1 l2 : List Value) : TCM Bool := do
      match l1, l2 with
      | p1 :: rest1, p2 :: rest2 =>
        if ← structurallyIncompatible p1 p2 then return true
        checkParams rest1 rest2
      | _, _ => return false
    checkParams ps1 ps2
  | _, _ => return false

/-- Extract constructor field types, constraining result type against scrutinee type.

    For a constructor type like `forall {a}. a -> Vec n a -> Vec (n+1) a` and
    scrutinee type `Vec 5 Int`:
    1. Instantiate implicits with fresh metas: `?a -> Vec ?n ?a -> Vec (?n+1) ?a`
    2. Collect explicit argument types: [?a, Vec ?n ?a]
    3. Unify result type `Vec (?n+1) ?a` with scrutinee `Vec 5 Int`
    4. This generates constraints: `?n+1 = 5`, `?a = Int`
    5. Return field types with metas that will be solved: [Int, Vec 4 Int]

    This enables proper index inference in pattern matching. -/
partial def extractConstructorFieldTypes (ctorTy : Value) (scrutTy : Value)
    (ctorName : Option String := none) (span : Span := default)
    : TCM (Array Value) := do
  -- Walk the constructor type, instantiating implicits and collecting explicit field types
  let rec go (ty : Value) (acc : Array Value) : TCM (Array Value × Value) := do
    let ty' ← force ty
    match ty' with
    | .vPi _qty binder _name dom cod =>
      if binder.isImplicit then
        -- Implicit parameter: instantiate with fresh meta
        let metaVal ← TCM.freshMetaVal dom
        let resultTy ← applyClosure cod metaVal
        go resultTy acc
      else
        -- Explicit parameter: this is a field type
        -- Create a dummy value to apply the closure (for dependent fields)
        let lvl ← TCM.currentLevel
        let dummyVal := Value.vNeutral dom (.nVar ⟨"_field", lvl⟩)
        let resultTy ← applyClosure cod dummyVal
        go resultTy (acc.push dom)
    | _ =>
      -- Not a Pi type: this is the result type
      return (acc, ty')

  let (fieldTypes, resultTy) ← go ctorTy #[]

  -- Check for structurally impossible patterns before unification
  if ← structurallyIncompatible resultTy scrutTy then
    match ctorName with
    | some name => TCM.throw (.impossiblePattern name resultTy scrutTy span)
    | none => pure ()

  -- Unify the constructor's result type with the scrutinee type
  -- This generates constraints on the indices
  unify resultTy scrutTy

  return fieldTypes

/-- Collect available field names from a row -/
partial def collectRowFields (row : Value) : TCM (Array String) := do
  match row with
  | .vRowEmpty => return #[]
  | .vRowExtend (.vLabelLit name) _ tail =>
    let tailFields ← collectRowFields tail
    return #[name] ++ tailFields
  | .vRowExtend _ _ tail => collectRowFields tail
  | _ => return #[]

/-- Find the positional index of a field in a row type -/
partial def findFieldIndex (row : Value) (fieldName : String) (idx : Nat := 0) : TCM (Option Nat) := do
  match ← force row with
  | .vRowEmpty => return none
  | .vRowExtend (.vLabelLit name) _ tail =>
    if name == fieldName then return some idx
    else findFieldIndex tail fieldName (idx + 1)
  | .vRowExtend _ _ tail => findFieldIndex tail fieldName (idx + 1)
  | _ => return none

/-- Find a field in a row type -/
partial def findFieldInRow (row : Value) (fieldName : String) (span : Span) : TCM Value := do
  match row with
  | .vRowEmpty =>
    TCM.throw (.fieldNotFound fieldName row span #[] none)
  | .vRowExtend (.vLabelLit name) ty tail =>
    if name == fieldName then
      return ty
    else
      findFieldInRow tail fieldName span
  | .vNeutral _ _ =>
    -- Can't search in neutral row
    let available ← collectRowFields row
    TCM.throw (.fieldNotFound fieldName row span available none)
  | _ =>
    TCM.throw (.fieldNotFound fieldName row span #[] none)

/-- If a type is a type-class application, instantiate its class record type -/
private def normalizeRecordLikeType (ty : Value) (span : Span := Span.uninhabited) : TCM Value := do
  let ty' ← force ty
  match ty' with
  | .vDataType classId args =>
    match ← TCM.lookupClass classId with
    | none =>
      return ty'
    | some classInfo =>
      if args.length > classInfo.numParams then
        TCM.throw (.cannotInfer
          s!"type class expects {classInfo.numParams} argument(s) but was applied to {args.length}"
          span none)
      let mut instTy := classInfo.recordType
      for arg in args do
        let instTy' ← force instTy
        match instTy' with
        | .vPi _ _ _ _ cod =>
          instTy ← applyClosure cod arg
        | _ =>
          TCM.throw (.cannotInfer
            s!"type class record type is not a function; cannot apply remaining argument"
            span none)
      return instTy
  | _ =>
    return ty'

/-- Look up field type in a record type -/
partial def lookupFieldType (recTy : Value) (fieldName : String) (span : Span) : TCM Value := do
  let recTy' ← normalizeRecordLikeType recTy span
  match recTy' with
  | .vRecord row =>
    findFieldInRow row fieldName span
  | .vRecordVal fields =>
    match fields.find? (·.1 == fieldName) with
    | some (_, ty) => return ty
    | none =>
      let available := fields.map (·.1) |>.toArray
      TCM.throw (.fieldNotFound fieldName recTy' span available none)
  | _ =>
    TCM.throw (.expectedRecord recTy' span #[])

/-- Find a field in a row type by label value, supporting label polymorphism.
    This handles the case where both the row label and the lookup label can be
    either literal labels or label variables. Used for polymorphic field access: rec @l -/
partial def findFieldInRowByLabelVal (row : Value) (lookupLabel : Value) (span : Span) : TCM Value := do
  let row' ← force row
  let lookupLabel' ← force lookupLabel
  match row' with
  | .vRowEmpty =>
    let labelStr := match lookupLabel' with
      | .vLabelLit name => name
      | .vNeutral _ (.nVar v) => v.name
      | _ => "<label>"
    TCM.throw (.fieldNotFound labelStr row' span #[] none)
  | .vRowExtend rowLabel ty tail =>
    -- Try to unify the row label with the lookup label
    -- If they unify, we found our field; otherwise, search the tail
    let canUnify ← tryUnify rowLabel lookupLabel'
    if canUnify then
      return ty
    else
      findFieldInRowByLabelVal tail lookupLabel' span
  | .vNeutral _ (.nMeta _) =>
    -- Row ends in a metavariable - we can extend it with the field we need
    let fieldTy ← TCM.freshMetaVal (.vType .zero)
    let tailMeta ← TCM.freshMetaVal .vRowSort
    let newRow := Value.vRowExtend lookupLabel' fieldTy tailMeta
    unify row' newRow
    return fieldTy
  | .vNeutral _ _ =>
    -- Can't search in other neutral rows
    let labelStr := match lookupLabel' with
      | .vLabelLit name => name
      | .vNeutral _ (.nVar v) => v.name
      | _ => "<label>"
    let available ← collectRowFields row'
    TCM.throw (.fieldNotFound labelStr row' span available none)
  | _ =>
    let labelStr := match lookupLabel' with
      | .vLabelLit name => name
      | .vNeutral _ (.nVar v) => v.name
      | _ => "<label>"
    TCM.throw (.fieldNotFound labelStr row' span #[] none)

/-- Infer polymorphic field access (`rec @l`). -/
partial def inferPolymorphicFieldAccess
    (recExpr : Soma.Core.Expr) (row : Value)
    (labelName : String) (argSpan : Span) (_callSpan : Span)
    : TCM (Value × Soma.Core.Expr) := do
  let labelVal ← match ← TCM.lookupLocal labelName with
    | some entry =>
      pure (Value.vNeutral entry.type (Neutral.nVar ⟨labelName, entry.level⟩))
    | none =>
      pure (Value.vLabelLit labelName)
  let fieldTy ← findFieldInRowByLabelVal row labelVal argSpan
  let fieldExpr := Soma.Core.Expr.fieldAccess recExpr labelName 0
  return (fieldTy, fieldExpr)

/-! ## Syntax.Expr-based inference (Phase 5b) -/

/-- Short debug description of a Syntax.Expr -/
def syntaxExprKind : Soma.Syntax.Expr → String
  | .var name => s!"var({name.value})"
  | .lit _ => "lit"
  | .app _ _ _ => "app"
  | .infix op _ _ _ => s!"infix({op.value})"
  | .lambda params _ _ => s!"λ({params.size} params)"
  | .if_ _ _ _ _ => "if"
  | .case _ _ _ => "case"
  | .tuple elems _ => s!"tuple({elems.size})"
  | .list _ _ => "list"
  | .record _ _ => "record"
  | .recordUpdate _ _ _ => "recordUpdate"
  | .fieldAccess _ field _ => s!".{field.value}"
  | .projection tn fn _ => s!"proj({tn.value}.{fn.value})"
  | .parens _ _ => "parens"
  | .typeAnnot _ _ _ => "ann"
  | .typeApp _ _ => "typeApp"
  | .composeBlock stmts _ _ => s!"composeBlock({stmts.size} stmts)"
  | .variant label _ _ => s!"variant(.{label.value})"

private def requireUniqueWiredRole (role : WiredRole) (span : Span) : TCM GlobalInfo := do
  let infos ← TCM.lookupWiredInAll role
  match infos.toList with
  | [info] => pure info
  | [] =>
    TCM.throw (.unboundGlobal s!"{role.canonical} (missing @[wired_in \"{role.canonical}\"] declaration)" span #[])
  | _ =>
    let names := infos.map (fun i => i.name.display)
    let details := String.intercalate ", " names.toList
    TCM.throw (.cannotInfer s!"wired role '{role.canonical}' is ambiguous: {details}" span none)

/-- Build a nested Pair pattern from a list of core patterns: (a, b, c) → Pair(a, Pair(b, c))
    Requires @[wired_in "pair"] to be defined on a binary constructor. -/
partial def buildNestedPairPattern (elems : List Soma.Core.Pattern) (span : Span)
    : TCM Soma.Core.Pattern := do
  match elems with
  | [] => pure .wildcard
  | [single] => pure single
  | [a, b] =>
    match ← TCM.lookupWiredIn .pair with
    | some info => pure (.ctor info.name info.ctorTag #[a, b])
    | none => TCM.throw (.unboundGlobal "pair (no @[wired_in \"pair\"] constructor in scope)" span #[])
  | a :: rest => do
    let nested ← buildNestedPairPattern rest span
    match ← TCM.lookupWiredIn .pair with
    | some info => pure (.ctor info.name info.ctorTag #[a, nested])
    | none => TCM.throw (.unboundGlobal "pair (no @[wired_in \"pair\"] constructor in scope)" span #[])

/-- Build a list pattern from elements: [a, b] → Cons(a, Cons(b, Nil))
    Requires @[wired_in "cons"] and @[wired_in "nil"] to be defined. -/
partial def buildListPattern (elems : List Soma.Core.Pattern) (span : Span)
    : TCM Soma.Core.Pattern := do
  match elems with
  | [] =>
    match ← TCM.lookupWiredIn .nil with
    | some info => pure (.ctor info.name info.ctorTag #[])
    | none => TCM.throw (.unboundGlobal "nil (no @[wired_in \"nil\"] constructor in scope)" span #[])
  | head :: tail => do
    let tailPat ← buildListPattern tail span
    match ← TCM.lookupWiredIn .cons with
    | some info => pure (.ctor info.name info.ctorTag #[head, tailPat])
    | none => TCM.throw (.unboundGlobal "cons (no @[wired_in \"cons\"] constructor in scope)" span #[])

/-- Convert a Syntax.Pattern to a Core.Pattern and simultaneously extract binding types -/
partial def convertPatternWithBindings (pat : Soma.Syntax.Pattern) (scrutTy : Value)
    : TCM (Soma.Core.Pattern × List (Unique × String × Value)) := do
  match pat with
  | .var name =>
    let u ← TCM.freshUnique name.value
    pure (.var (some u), [(u, name.value, scrutTy)])
  | .wildcard _ => pure (.wildcard, [])
  | .lit l =>
    pure (.lit (match l with
      | .int n _ => .int n
      | .string s _ => .string s
      | .bool b _ => .bool b), [])
  | .con name args span =>
    match ← TCM.resolveConstructor name.value with
    | some ctorInfo =>
      let fieldTypes ← extractConstructorFieldTypes ctorInfo.type scrutTy (some name.value) span
      let mut coreArgs : Array Soma.Core.Pattern := #[]
      let mut bindings : List (Unique × String × Value) := []
      for h : i in [:args.size] do
        let arg := args[i]
        let fieldTy ← if h' : i < fieldTypes.size then
          pure fieldTypes[i]
        else
          TCM.freshMetaVal (.vType .zero)
        let (corePat, argBindings) ← convertPatternWithBindings arg fieldTy
        coreArgs := coreArgs.push corePat
        bindings := bindings ++ argBindings
      pure (.ctor ctorInfo.name ctorInfo.ctorTag coreArgs, bindings)
    | none =>
      TCM.throw (.unboundVariable name.value span #[])
  | .tuple elems span => do
    let (coreElems, bindings) ← convertTuplePatternWithBindings elems.toList scrutTy
    let nested ← buildNestedPairPattern coreElems span
    pure (nested, bindings)
  | .list elems span => do
    let elemTy ← TCM.freshMetaVal (.vType .zero)
    let scrutTy' ← force scrutTy
    match scrutTy' with
    | .vDataType _ (actualElemTy :: _) => unify elemTy actualElemTy
    | _ =>
      let listInfo ← requireUniqueWiredRole .typeList span
      let listId := listInfo.name.id
      let expectedListTy := Value.vDataType listId [elemTy]
      unify scrutTy expectedListTy
    let mut coreElems : List Soma.Core.Pattern := []
    let mut bindings : List (Unique × String × Value) := []
    for elem in elems do
      let (corePat, elemBindings) ← convertPatternWithBindings elem elemTy
      coreElems := coreElems ++ [corePat]
      bindings := bindings ++ elemBindings
    let listPat ← buildListPattern coreElems span
    pure (listPat, bindings)
  | .cons head tail span => do
    let elemTy ← TCM.freshMetaVal (.vType .zero)
    let scrutTy' ← force scrutTy
    match scrutTy' with
    | .vDataType _ (actualElemTy :: _) => unify elemTy actualElemTy
    | _ =>
      let listInfo ← requireUniqueWiredRole .typeList span
      let listId := listInfo.name.id
      let expectedListTy := Value.vDataType listId [elemTy]
      unify scrutTy expectedListTy
    let (coreHead, headBindings) ← convertPatternWithBindings head elemTy
    let (coreTail, tailBindings) ← convertPatternWithBindings tail scrutTy
    match ← TCM.lookupWiredIn .cons with
    | some info => pure (.ctor info.name info.ctorTag #[coreHead, coreTail], headBindings ++ tailBindings)
    | none => TCM.throw (.unboundGlobal "cons (no @[wired_in \"cons\"] constructor in scope)" span #[])
  | .parens inner _ => convertPatternWithBindings inner scrutTy
  | .typed pat _ _ => convertPatternWithBindings pat scrutTy
  | .variant label arg _ => do
    match arg with
    | some p =>
      let argTy ← TCM.freshMetaVal (.vType .zero)
      let (coreArg, bindings) ← convertPatternWithBindings p argTy
      pure (.inject label.value (some coreArg), bindings)
    | none => pure (.inject label.value none, [])
where
  convertTuplePatternWithBindings (elems : List Soma.Syntax.Pattern) (ty : Value)
      : TCM (List Soma.Core.Pattern × List (Unique × String × Value)) := do
    match elems with
    | [] => return ([], [])
    | [lastElem] =>
      let (pat, bindings) ← convertPatternWithBindings lastElem ty
      pure ([pat], bindings)
    | elem :: rest =>
      let ty' ← force ty
      match ty' with
      | .vSigma _ _ fstTy sndClos =>
        let (elemPat, elemBindings) ← convertPatternWithBindings elem fstTy
        let lvl ← TCM.currentLevel
        let dummyVal := Value.vNeutral fstTy (.nVar ⟨"_", lvl⟩)
        let sndTy ← applyClosure sndClos dummyVal
        let (restPats, restBindings) ← convertTuplePatternWithBindings rest sndTy
        return (elemPat :: restPats, elemBindings ++ restBindings)
      | _ =>
        let mut pats : List Soma.Core.Pattern := []
        let mut bindings : List (Unique × String × Value) := []
        for e in (elem :: rest) do
          let eTy ← TCM.freshMetaVal (.vType .zero)
          let (p, bs) ← convertPatternWithBindings e eTy
          pats := pats ++ [p]
          bindings := bindings ++ bs
        return (pats, bindings)

/-- Convert a list of Syntax.Patterns with corresponding scrutinee types -/
partial def convertPatternListWithBindings (pats : List Soma.Syntax.Pattern) (scrutTys : List Value)
    : TCM (Array Soma.Core.Pattern × List (Unique × String × Value)) := do
  match pats, scrutTys with
  | [], _ => return (#[], [])
  | pat :: rest, ty :: tys =>
    let (corePat, patBindings) ← convertPatternWithBindings pat ty
    let (restPats, restBindings) ← convertPatternListWithBindings rest tys
    return (#[corePat] ++ restPats, patBindings ++ restBindings)
  | pat :: rest, [] =>
    let freshTy ← TCM.freshMetaVal (.vType .zero)
    let (corePat, patBindings) ← convertPatternWithBindings pat freshTy
    let (restPats, restBindings) ← convertPatternListWithBindings rest []
    return (#[corePat] ++ restPats, patBindings ++ restBindings)

/-- Intermediate result from elaborating a compose block statement -/
private inductive ComposeElabStmt where
  /-- Expression statement: (>>= action) with lambda-wrapped continuation -/
  | seqStmt (partialTy : Value) (partialExpr : Soma.Core.Expr)
      (codomain : Closure) (stmtSpan : Span)
  /-- Let binding: let x = value -/
  | letBind (name : String) (valTy : Value) (valTyExpr : Soma.Core.Expr)
      (valExpr : Soma.Core.Expr) (fvarId : Unique)
  /-- Monadic bind: bind x <- action -/
  | monadBind (name : String) (bindTy : Value) (bindTyExpr : Soma.Core.Expr)
      (partialTy : Value) (partialExpr : Soma.Core.Expr)
      (codomain : Closure) (fvarId : Unique) (stmtSpan : Span)
  deriving Inhabited

mutual

/-- Infer the type of a Syntax.Expr, returning (type, Core.Expr) -/
partial def inferSyntax (e : Soma.Syntax.Expr) : TCM (Value × Soma.Core.Expr) := do
  let kind := syntaxExprKind e
  TCM.debugEnter "inferS" kind
  let result ← TCM.withDebugIndent do
    TCM.withSpan e.span do
      inferSyntaxCore e
  TCM.debugLeave "inferS" (toString result.1)
  return result
where
  inferSyntaxCore (e : Soma.Syntax.Expr) : TCM (Value × Soma.Core.Expr) := do
    match e with
    -- Variables: resolve name (local, global, or builtin)
    | .var name => do
      -- First check local context
      match ← TCM.lookupLocal name.value with
      | some entry =>
        useVarChecked entry.bindingId name.span
        let tyExpr ← quoteValueToExpr entry.type
        return (entry.type, .fvar entry.fvarId tyExpr)
      | none =>
        -- Check globals (functions, constructors, data types)
        match ← TCM.lookupGlobal name.value with
        | some info =>
          let qn := info.name
          if info.isConstructor then
            let instantiatedTy ← instantiateImplicits info.type name.span
            let tyExpr ← quoteValueToExpr instantiatedTy
            return (instantiatedTy, .const qn tyExpr)
          else
            let tyExpr ← quoteValueToExpr info.type
            return (info.type, .const qn tyExpr)
        | none =>
          match name.value with
          | "Type" | "Type0" => return (.vType .one, .sort .zero)
          | "Type1" => return (.vType .one, .sort .one)
          | "Row" => return (.vType .zero, .rowSort)
          | "Label" => return (.vType .zero, .labelSort)
          | _ => TCM.throw (.unboundVariable name.value name.span #[])

    -- Literals
    | .lit (.int n _) => return (.vPrimTy .int, .lit (.int n))
    | .lit (.string s _) => return (.vPrimTy .string, .lit (.string s))
    | .lit (.bool b _) => return (.vPrimTy .bool, .lit (.bool b))

    -- Application: infer fn, then apply arg
    | .app fn arg span => do
      let (fnTy, fnExpr) ← inferSyntax fn
      inferSyntaxApp fnTy fnExpr arg span

    -- Infix operators: resolve op, apply to both args
    | .infix op left right span => do
      -- Resolve the operator name
      let (opTy, opExpr) ← inferSyntax (.var ⟨op.value, op.span⟩)
      -- Apply to left
      let (ty1, expr1) ← inferSyntaxApp opTy opExpr left span
      -- Apply to right
      let (ty2, expr2) ← inferSyntaxApp ty1 expr1 right span
      return (ty2, expr2)

    -- Lambda: generate bindings, infer body
    | .lambda params body span => do
      inferSyntaxLamBody params.toList body span []

    -- If-then-else
    | .if_ cond then_ else_ span => do
      let condExpr ← checkSyntax cond (.vPrimTy .bool)
      let ((thenTy, thenExpr), thenUsages) ← captureUsages (inferSyntax then_)
      let (elseExpr, elseUsages) ← captureUsages (checkSyntax else_ thenTy)
      let joined ← checkBranchUsages thenUsages elseUsages span
      applyUsages joined
      return (thenTy, .if_ condExpr thenExpr elseExpr)

    -- Case expressions
    | .case scruts arms _ => do
      let (scrutTys, scrutsExpr) ← inferSyntaxList scruts.toList
      let resultTy ← TCM.freshMetaVal (.vType .zero)
      let armsExpr ← inferSyntaxArms arms.toList scrutTys resultTy
      let resultTyExpr ← quoteValueToExpr resultTy
      return (resultTy, .«case» scrutsExpr armsExpr resultTyExpr)

    -- Tuple: desugar to nested pairs
    | .tuple elems span => do
      let elemList := elems.toList
      match elemList with
      | [] =>
        -- Empty tuple = unit
        return (.vPrimTy .unit, .tuple #[])
      | [e] =>
        -- Single element, unwrap
        inferSyntax e
      | _ =>
        -- Multiple: desugar to nested pairs
        inferSyntaxTuple elemList span

    -- List literal
    | .list elems span => do
      let elemTy ← TCM.freshMetaVal (.vType .zero)
      let elemsChecked ← checkSyntaxList elems.toList elemTy
      let listInfo ← requireUniqueWiredRole .typeList span
      let listId := listInfo.name.id
      let listTy := Value.vDataType listId [elemTy]
      let listTyExpr ← quoteValueToExpr listTy
      return (listTy, .array elemsChecked.toArray listTyExpr)

    -- Record literal
    | .record fields _ => do
      let (rowTy, fieldsExpr) ← inferSyntaxRecordFields fields.toList
      let recTy := Value.vRecord rowTy
      return (recTy, .record fieldsExpr)

    -- Record update
    | .recordUpdate base updates _ => do
      let (baseTy, baseExpr) ← inferSyntax base
      let (_, updatesExpr) ← inferSyntaxRecordFields updates.toList
      return (baseTy, .recordUpdate baseExpr updatesExpr)

    -- Field access
    | .fieldAccess expr field span => do
      let (exprTy, exprE) ← inferSyntax expr
      let normalizedTy ← normalizeRecordLikeType exprTy span
      let fieldTy ← match normalizedTy with
        | .vRecord row => findFieldInRow row field.value span
        | .vRecordVal fields =>
          match fields.find? (·.1 == field.value) with
          | some (_, ty) => pure ty
          | none =>
            let available := fields.map (·.1) |>.toArray
            TCM.throw (.fieldNotFound field.value normalizedTy span available none)
        | _ => TCM.throw (.expectedRecord normalizedTy span #[])
      let idx ← match normalizedTy with
        | .vRecord row =>
          match ← findFieldIndex row field.value with
          | some i => pure i
          | none => pure 0
        | _ => pure 0
      return (fieldTy, .fieldAccess exprE field.value idx)

    -- Projection function: Type.field
    | .projection typeName fieldName span => do
      let accessorName := s!"{typeName.value}::{fieldName.value}"
      match ← TCM.lookupGlobal accessorName with
      | some accessorInfo =>
        let ctx ← TCM.getCtx
        let idx := ctx.globals.lookupFieldIndex typeName.value fieldName.value |>.getD 0
        return (accessorInfo.type, .proj accessorInfo.name fieldName.value idx)
      | none =>
        TCM.throw (.unboundGlobal accessorName span #[])

    -- Parenthesized: recurse
    | .parens inner _ => inferSyntax inner

    -- Type annotation: elaborate type, check expr against it
    | .typeAnnot expr ty _ => do
      let tyVal ← TCM.inErasedContext do
        Elaborate.elaborateType Elaborate.ElabEnv.empty ty
      let tyExpr ← quoteValueToExpr tyVal
      let checkedExpr ← checkSyntax expr tyVal
      return (tyVal, .ann checkedExpr tyExpr)

    -- Explicit type application
    | .typeApp _arg _span => do
      let resultTy ← TCM.freshMetaVal (.vType .zero)
      -- Standalone typeApp: produce placeholder (normally handled in app context)
      return (resultTy, .panic "typeApp not supported standalone")

    -- Compose block: elaborate iteratively (avoids deep recursion)
    | .composeBlock stmts final_ span => do
      inferComposeBlock stmts final_ span

    -- Variant injection
    | .variant label arg _ => do
      let (argTy, argsExpr) ← match arg with
        | some argExpr =>
          let (ty, e) ← inferSyntax argExpr
          pure (ty, #[e])
        | none =>
          pure (Value.vRecordVal [], #[])
      let rowTail ← TCM.freshMetaVal .vRowSort
      let row := Value.vRowExtend (.vLabelLit label.value) argTy rowTail
      let variantTy := Value.vVariant row
      let variantTyExpr ← quoteValueToExpr variantTy
      return (variantTy, .inject label.value argsExpr variantTyExpr)

/-- Elaborate a flat compose block in three iterative phases -/
partial def inferComposeBlock (stmts : Array Soma.Syntax.ComposeStmt)
    (final_ : Soma.Syntax.Expr) (_span : Span) : TCM (Value × Soma.Core.Expr) := do
  if stmts.isEmpty then
    return ← inferSyntax final_

  let mut elabStmts : Array ComposeElabStmt := #[]
  let mut extCtx ← read

  for stmt in stmts do
    match stmt with
    | .expr action stmtSpan =>
      -- Elaborate >>= operator and apply to action (in current extended context)
      let (partialTy, partialExpr) ← withReader (fun _ => extCtx) do
        let (opTy, opExpr) ← inferSyntax (.var ⟨">>=", stmtSpan⟩)
        inferSyntaxApp opTy opExpr action stmtSpan
      let partialTy' ← withReader (fun _ => extCtx) (force partialTy)
      let (_, _, _, _dom, cod) ← withReader (fun _ => extCtx) (ensurePi partialTy' stmtSpan)
      elabStmts := elabStmts.push (.seqStmt partialTy partialExpr cod stmtSpan)

    | .let_ name value stmtSpan =>
      -- Elaborate the value in the current extended context
      let (valTy, valExpr) ← withReader (fun _ => extCtx) (inferSyntax value)
      let valTyExpr ← withReader (fun _ => extCtx) (quoteValueToExpr valTy)
      let bindingId ← TCM.freshLocalId name.value
      extCtx := extCtx.extend name.value bindingId valTy .omega .explicit stmtSpan
      elabStmts := elabStmts.push (.letBind name.value valTy valTyExpr valExpr bindingId)

    | .bind_ name action stmtSpan =>
      -- Elaborate >>= operator and apply to action (in current extended context)
      let (partialTy, partialExpr) ← withReader (fun _ => extCtx) do
        let (opTy, opExpr) ← inferSyntax (.var ⟨">>=", stmtSpan⟩)
        inferSyntaxApp opTy opExpr action stmtSpan
      let partialTy' ← withReader (fun _ => extCtx) (force partialTy)
      let (_, _, _, dom, cod) ← withReader (fun _ => extCtx) (ensurePi partialTy' stmtSpan)
      let dom' ← withReader (fun _ => extCtx) (force dom)
      let bindTy ← match dom' with
        | .vPi _ _ _ innerDom _ => pure innerDom
        | _ => withReader (fun _ => extCtx) (TCM.freshMetaVal (.vType .zero))
      let bindTyExpr ← withReader (fun _ => extCtx) (quoteValueToExpr bindTy)
      -- Create binding and extend context for subsequent statements
      let bindingId ← TCM.freshLocalId name.value
      extCtx := extCtx.extend name.value bindingId bindTy .omega .explicit stmtSpan
      elabStmts := elabStmts.push (.monadBind name.value bindTy bindTyExpr partialTy partialExpr cod bindingId stmtSpan)

  let finalResult ← withReader (fun _ => extCtx) (inferSyntax final_)
  let mut resultTy := finalResult.1
  let mut resultExpr := finalResult.2

  for i in List.reverse (List.range elabStmts.size) do
    match elabStmts[i]! with
    | .seqStmt _partialTy partialExpr codomain _stmtSpan =>
      let unitTyExpr := Soma.Core.Expr.primTy .unit
      let lamExpr := Soma.Core.Expr.lam .explicit "_" unitTyExpr resultExpr
      let newTy ← applyClosure codomain (.vType .zero)
      resultExpr := .app partialExpr lamExpr
      resultTy := newTy

    | .letBind name _valTy valTyExpr valExpr fvarId =>
      let abstractedBody := resultExpr.abstractFVar fvarId
      resultExpr := .let_ name valTyExpr valExpr abstractedBody

    | .monadBind name _bindTy bindTyExpr _partialTy partialExpr codomain fvarId _stmtSpan =>
      let abstractedBody := resultExpr.abstractFVar fvarId
      let lamExpr := Soma.Core.Expr.lam .explicit name bindTyExpr abstractedBody
      -- The argument value is irrelevant so we pass a placeholder to extract the result type
      let newTy ← applyClosure codomain (.vType .zero)
      resultExpr := .app partialExpr lamExpr
      resultTy := newTy

  return (resultTy, resultExpr)

/-- Apply a function to a single Syntax.Expr argument -/
partial def inferSyntaxApp (fnTy : Value) (fnExpr : Soma.Core.Expr)
    (arg : Soma.Syntax.Expr) (span : Span) : TCM (Value × Soma.Core.Expr) := do
  let fnTy' ← force fnTy

  -- Check if the argument is a type application (@T or @label)
  match arg with
  | .typeApp typeArg argSpan =>
    -- Handle explicit type application
    match fnTy' with
    | .vPi _qty binder _name _dom cod =>
      if binder.isImplicit then
        let argVal ← elaborateTypeArg typeArg
        let resultTy ← applyClosure cod argVal
        let argExpr ← quoteValueToExpr argVal
        let appExpr := Soma.Core.Expr.app fnExpr argExpr
        solveImplicitsGreedy
        return (resultTy, appExpr)
      else
        -- Explicit param with typeApp — insert implicits first, then apply
        let (fnTy'', fnExpr') ← insertImplicits fnTy fnExpr span
        let (_, _, _, _dom, cod) ← ensurePi fnTy'' span
        let argVal ← elaborateTypeArg typeArg
        let argExpr ← quoteValueToExpr argVal
        let resultTy ← applyClosure cod argVal
        let appExpr := Soma.Core.Expr.app fnExpr' argExpr
        solveImplicitsGreedy
        return (resultTy, appExpr)
    | .vRecord row =>
      -- Polymorphic field access: rec @l
      match typeArg with
      | .label name =>
        let (fieldTy, fieldExpr) ← inferPolymorphicFieldAccess fnExpr row name.value argSpan span
        solveImplicitsGreedy
        return (fieldTy, fieldExpr)
      | _ =>
        -- Not a label — insert implicits and apply
        let (fnTy'', fnExpr') ← insertImplicits fnTy fnExpr span
        let (_, _, _, _dom, cod) ← ensurePi fnTy'' span
        let argVal ← elaborateTypeArg typeArg
        let argExpr ← quoteValueToExpr argVal
        let resultTy ← applyClosure cod argVal
        let appExpr := Soma.Core.Expr.app fnExpr' argExpr
        solveImplicitsGreedy
        return (resultTy, appExpr)
    | _ =>
      let (fnTy'', fnExpr') ← insertImplicits fnTy fnExpr span
      let (_, _, _, _dom, cod) ← ensurePi fnTy'' span
      let argVal ← elaborateTypeArg typeArg
      let argExpr ← quoteValueToExpr argVal
      let resultTy ← applyClosure cod argVal
      let appExpr := Soma.Core.Expr.app fnExpr' argExpr
      solveImplicitsGreedy
      return (resultTy, appExpr)
  | _ =>
    -- Regular value application: insert implicits, then check arg against domain
    let (fnTy'', fnExpr') ← insertImplicits fnTy fnExpr span
    let (_, _, _, dom, cod) ← ensurePi fnTy'' span
    let argExpr ← checkSyntax arg dom
    let argVal ← TCM.evalExpr argExpr
    let resultTy ← applyClosure cod argVal
    let appExpr := Soma.Core.Expr.app fnExpr' argExpr
    solveImplicitsGreedy
    return (resultTy, appExpr)

/-- Infer lambda body from Syntax params, building nested Core.Expr lambdas -/
partial def inferSyntaxLamBody
    (params : List (Soma.Syntax.Name × Option Soma.Syntax.TypeExpr))
    (body : Soma.Syntax.Expr) (span : Span)
    (acc : List (Unique × String × Soma.Core.Expr))
    : TCM (Value × Soma.Core.Expr) := do
  match params with
  | [] =>
    let (bodyTy, bodyExpr) ← inferSyntax body
    let lamExpr := buildLambdas acc.reverse bodyExpr
    return (bodyTy, lamExpr)
  | (name, _tyAnnot) :: rest =>
    let paramTy ← TCM.freshMetaVal (.vType .zero)
    let bindingId ← TCM.freshLocalId name.value
    TCM.withBinding name.value bindingId paramTy .omega .explicit span do
      match ← TCM.lookupLocal name.value with
      | some entry =>
        let domExpr ← quoteValueToExpr paramTy
        let (innerTy, lamExpr) ← inferSyntaxLamBody rest body span (acc ++ [(entry.fvarId, name.value, domExpr)])
        -- Build Pi type: paramTy -> innerTy
        let codClosure := Closure.const name.value innerTy
        let piTy := Value.vPi .omega .explicit name.value paramTy codClosure
        return (piTy, lamExpr)
      | none =>
        inferSyntaxLamBody rest body span acc

/-- Check lambda body against expected Pi type from Syntax params -/
partial def checkSyntaxLamBody
    (params : List (Soma.Syntax.Name × Option Soma.Syntax.TypeExpr))
    (body : Soma.Syntax.Expr) (expectedTy : Value) (span : Span)
    (acc : List (Unique × String × Soma.Core.Expr))
    : TCM Soma.Core.Expr := do
  match params with
  | [] =>
    let bodyExpr ← checkSyntax body expectedTy
    return buildLambdas acc.reverse bodyExpr
  | (name, _tyAnnot) :: rest =>
    let expectedTy' ← force expectedTy
    match expectedTy' with
    | .vPi qty binder _ dom cod =>
      let codTy ← do
        let lvl ← TCM.currentLevel
        let x := Value.vNeutral dom (.nVar ⟨name.value, lvl⟩)
        applyClosure cod x
      let bindingId ← TCM.freshLocalId name.value
      withCheckedBinding name.value bindingId dom qty binder span do
        match ← TCM.lookupLocal name.value with
        | some entry =>
          let domExpr ← quoteValueToExpr dom
          checkSyntaxLamBody rest body codTy span (acc ++ [(entry.fvarId, name.value, domExpr)])
        | none =>
          checkSyntaxLamBody rest body codTy span acc
    | _ =>
      let paramTy ← TCM.freshMetaVal (.vType .zero)
      let bindingId ← TCM.freshLocalId name.value
      TCM.withBinding name.value bindingId paramTy .omega .explicit span do
        match ← TCM.lookupLocal name.value with
        | some entry =>
          let domExpr ← quoteValueToExpr paramTy
          checkSyntaxLamBody rest body expectedTy' span (acc ++ [(entry.fvarId, name.value, domExpr)])
        | none =>
          checkSyntaxLamBody rest body expectedTy' span acc

/-- Infer a list of Syntax.Exprs, returning (types, Core.Expr array) -/
partial def inferSyntaxList (es : List Soma.Syntax.Expr)
    : TCM (List Value × Array Soma.Core.Expr) := do
  match es with
  | [] => return ([], #[])
  | e :: rest => do
    let (ty, expr) ← inferSyntax e
    let (restTys, restExprs) ← inferSyntaxList rest
    return (ty :: restTys, #[expr] ++ restExprs)

/-- Check a list of Syntax.Exprs against an expected type -/
partial def checkSyntaxList (exprs : List Soma.Syntax.Expr) (elemTy : Value)
    : TCM (List Soma.Core.Expr) := do
  match exprs with
  | [] => return []
  | e :: es =>
    let e' ← checkSyntax e elemTy
    let es' ← checkSyntaxList es elemTy
    return e' :: es'

/-- Infer record fields from Syntax -/
partial def inferSyntaxRecordFields (fields : List (Soma.Syntax.Name × Soma.Syntax.Expr))
    : TCM (Value × Array (String × Soma.Core.Expr)) := do
  match fields with
  | [] => return (.vRowEmpty, #[])
  | (name, expr) :: rest => do
    let (ty, exprE) ← inferSyntax expr
    let (restRow, restFields) ← inferSyntaxRecordFields rest
    let row := Value.vRowExtend (.vLabelLit name.value) ty restRow
    return (row, #[(name.value, exprE)] ++ restFields)

/-- Infer arms of a case expression from Syntax.MatchArm -/
partial def inferSyntaxArms (arms : List Soma.Syntax.MatchArm)
    (scrutTys : List Value) (expectedTy : Value)
    : TCM (Array Soma.Core.Arm) := do
  let mut results : Array Soma.Core.Arm := #[]
  let mut armUsagesList : Array UsageSnapshot := #[]
  for arm in arms do
    let pats := arm.patterns.toList
    -- Single unified pass: convert patterns and extract bindings with shared unique IDs
    let (corePatterns, bindingsWithTypes) ← convertPatternListWithBindings pats scrutTys
    let (bodyExpr, armUsages) ← captureUsages
      (inferSyntaxArmBodyWithBindings bindingsWithTypes arm.body expectedTy arm.span)
    results := results.push (Soma.Core.Arm.mk corePatterns bodyExpr)
    armUsagesList := armUsagesList.push armUsages
  let span := match arms.head? with
    | some arm => arm.span
    | none => default
  let joined ← checkMultiBranchUsages armUsagesList span
  applyUsages joined
  return results

/-- Helper: extend context with bindings and check body -/
partial def inferSyntaxArmBodyWithBindings
  (bindings : List (Unique × String × Value))
    (body : Soma.Syntax.Expr) (expectedTy : Value) (span : Span)
    : TCM Soma.Core.Expr := do
  match bindings with
  | [] => checkSyntax body expectedTy
  | (bindingId, name, bindingTy) :: rest =>
    TCM.withBinding name bindingId bindingTy .omega .explicit span do
      inferSyntaxArmBodyWithBindings rest body expectedTy span

/-- Infer nested tuple as nested pairs -/
partial def inferSyntaxTuple (elems : List Soma.Syntax.Expr) (span : Span)
    : TCM (Value × Soma.Core.Expr) := do
  match elems with
  | [] => return (.vPrimTy .unit, .tuple #[])
  | [e] => inferSyntax e
  | e :: rest => do
    let (fstTy, fstExpr) ← inferSyntax e
    let (sndTy, sndExpr) ← inferSyntaxTuple rest span
    let sigmaTy := Value.vSigma .omega "_" fstTy (Closure.const "_" sndTy)
    return (sigmaTy, .pair fstExpr sndExpr)

/-- Infer constructor application from Syntax -/
partial def inferSyntaxConstructorApp
    (ctorTy : Value) (args : List Soma.Syntax.Expr) (span : Span)
    : TCM (Value × Array Soma.Core.Expr) := do
  let rec go (ty : Value) (remainingArgs : List Soma.Syntax.Expr)
      (checkedArgs : Array Soma.Core.Expr)
      : TCM (Value × Array Soma.Core.Expr) := do
    let ty' ← force ty
    match ty', remainingArgs with
    | _, [] => return (ty', checkedArgs)
    | .vPi _qty binder _name dom cod, _ =>
      if binder.isImplicit then
        let metaVal ← TCM.freshMetaVal dom
        let resultTy ← applyClosure cod metaVal
        go resultTy remainingArgs checkedArgs
      else
        match remainingArgs with
        | [] => return (ty', checkedArgs)
        | arg :: restArgs =>
          let argExpr ← checkSyntax arg dom
          let argVal ← TCM.evalExpr argExpr
          let resultTy ← applyClosure cod argVal
          go resultTy restArgs (checkedArgs.push argExpr)
    | _, _ :: _ => TCM.throw (.expectedFunction ty' span none)
  go ctorTy args #[]

/-- Check an expression against an expected type (Syntax.Expr version) -/
partial def checkSyntax (e : Soma.Syntax.Expr) (expected : Value)
    : TCM Soma.Core.Expr := do
  match e with
  | .parens inner _ => checkSyntax inner expected
  | _ =>
  let kind := syntaxExprKind e
  TCM.debugEnter "checkS" s!"{kind} ⇐ {expected}"
  let result ← TCM.withDebugIndent do
    TCM.withSpan e.span do
      checkSyntaxCore e expected
  TCM.debugLeave "checkS" "ok"
  return result
where
  checkSyntaxCore (e : Soma.Syntax.Expr) (expected : Value)
      : TCM Soma.Core.Expr := do
    let expected' ← force expected

    match e, expected' with
    -- Lambda against Pi type
    | .lambda params body span, .vPi _ _ _ _ _ =>
      match params.toList with
      | [] =>
        let (_, bodyExpr) ← inferSyntax body
        return bodyExpr
      | paramList =>
        checkSyntaxLamBody paramList body expected' span []

    -- If-then-else: check both branches
    | .if_ cond then_ else_ span, _ => do
      let condExpr ← checkSyntax cond (.vPrimTy .bool)
      let (thenExpr, thenUsages) ← captureUsages (checkSyntax then_ expected')
      let (elseExpr, elseUsages) ← captureUsages (checkSyntax else_ expected')
      let joined ← checkBranchUsages thenUsages elseUsages span
      applyUsages joined
      return .if_ condExpr thenExpr elseExpr

    -- Tuple against Sigma: desugar to nested pair checks
    | .tuple elems _, .vSigma _ _ _ _ =>
      checkSyntaxTupleAgainstSigma elems.toList expected'

    -- Application: use expected type to guide implicit solving
    | .app fn arg span, _ => do
      let (fnTy, fnExpr) ← inferSyntax fn
      let (fnTy', fnExpr') ← insertImplicitsWithExpected fnTy fnExpr (some expected') 1 span
      let (resultTy, appExpr) ← inferSyntaxApp fnTy' fnExpr' arg span
      solveImplicitsGreedy
      unify resultTy expected'
      return appExpr

    -- List literal against List type
    | .list elems span, .vDataType unique (elemTy :: _) => do
      let listInfo ← requireUniqueWiredRole .typeList span
      let listId := listInfo.name.id
      if unique == listId then
        let elemsChecked ← checkSyntaxList elems.toList elemTy
        let listTyExpr ← quoteValueToExpr (Value.vDataType unique [elemTy])
        return .array elemsChecked.toArray listTyExpr
      else
        let (inferred, expr) ← inferSyntax e
        let (inferred', expr') ← insertImplicits inferred expr e.span
        unify inferred' expected'
        solveImplicitsGreedy
        return expr'

    -- Default: infer and unify
    | _, _ => do
      let (inferred, expr) ← inferSyntax e
      let (inferred', expr') ← insertImplicits inferred expr e.span
      unify inferred' expected'
      solveImplicitsGreedy
      return expr'

/-- Check tuple elements against a Sigma type -/
partial def checkSyntaxTupleAgainstSigma (elems : List Soma.Syntax.Expr) (sigmaTy : Value)
    : TCM Soma.Core.Expr := do
  match elems with
  | [] => do
    let (_, expr) ← inferSyntax (.tuple #[] Span.uninhabited)
    return expr
  | [e] => checkSyntax e sigmaTy
  | e :: rest => do
    let sigmaTy' ← force sigmaTy
    match sigmaTy' with
    | .vSigma _qty _name fstTy sndClos =>
      let fstExpr ← checkSyntax e fstTy
      let fstVal ← TCM.evalExpr fstExpr
      let sndTy ← applyClosure sndClos fstVal
      let sndExpr ← checkSyntaxTupleAgainstSigma rest sndTy
      return .pair fstExpr sndExpr
    | _ =>
      -- Not a sigma, fall back to inference
      let (_, expr) ← inferSyntaxTuple elems Span.uninhabited
      return expr

end -- mutual

/-! ## Top-Level Interface -/

/-- Type check an expression, inferring its type -/
def typeInfer (e : Soma.Syntax.Expr) (ctx : TCContext := TCContext.empty)
    : Except TCError (Value × Soma.Core.Expr × TCState) := do
  let ((ty, expr), state) ← (inferSyntax e).run ctx
  return (ty, expr, state)

/-- Type check an expression against an expected type -/
def typeCheck (e : Soma.Syntax.Expr) (expected : Value)
    (ctx : TCContext := TCContext.empty) : Except TCError (Soma.Core.Expr × TCState) := do
  let (expr, state) ← (checkSyntax e expected).run ctx
  return (expr, state)

/-- Type check a Syntax expression, inferring its type -/
def typeInferSyntax (e : Soma.Syntax.Expr) (ctx : TCContext := TCContext.empty)
    : Except TCError (Value × Soma.Core.Expr × TCState) := do
  let ((ty, expr), state) ← (inferSyntax e).run ctx
  return (ty, expr, state)

/-- Type check a Syntax expression against an expected type -/
def typeCheckSyntax (e : Soma.Syntax.Expr) (expected : Value)
    (ctx : TCContext := TCContext.empty) : Except TCError (Soma.Core.Expr × TCState) := do
  let (expr, state) ← (checkSyntax e expected).run ctx
  return (expr, state)

end Soma.Dependent
