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
import Soma.Dependent.Coverage
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
  | .vNeutral _ (.nMeta mid) =>
    -- Fake it for error recovery
    let domMeta ← TCM.freshMetaVal (.vType .zero)
    let codMeta ← TCM.freshMetaVal (.vType .zero)
    let codClosure := Closure.const "?cod" codMeta
    let piTy := Value.vPi .omega .explicit "?dom" domMeta codClosure
    TCM.solveMeta mid piTy "ensurePi-meta"
    return (.omega, .explicit, "?dom", domMeta, codClosure)
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
      let piLvl := cod.level?.map (·.lvl)
      let metaId ← TCM.freshMeta dom (piLevel := piLvl)
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
    match ← TCM.lookupLocal labelName.name with
    | some entry =>
      pure (Value.vNeutral entry.type (Neutral.nVar ⟨labelName.name, entry.level⟩))
    | none =>
      pure (Value.vLabelLit labelName.name)
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

/-- Extract constructor field types and their declared QTT quantities,
    constraining the constructor's result type against the scrutinee type.

    For a constructor `forall {a}. (1 x : a) -> Vec n a -> Vec (n+1) a` and
    scrutinee type `Vec 5 Int`:
    1. Instantiate implicits with fresh metas: `(1 x : ?a) -> Vec ?n ?a -> Vec (?n+1) ?a`
    2. Collect explicit field (type, qty) pairs: `[(?a, .one), (Vec ?n ?a, .omega)]`
    3. Unify result `Vec (?n+1) ?a` with scrutinee `Vec 5 Int` to solve indices
    4. Field types become [Int, Vec 4 Int] once metas are solved, each carrying
       its constructor-declared quantity.

    Returning the quantities lets callers propagate linearity / erasure through
    pattern bindings per the standard QTT rule `binding_qty = scrut_qty * field_qty` -/
partial def extractConstructorFieldTypes (ctorTy : Value) (scrutTy : Value)
    (ctorName : Option String := none) (span : Span := default)
    : TCM (Array (Value × Quantity)) := do
  let rec go (ty : Value) (acc : Array (Value × Quantity))
      : TCM (Array (Value × Quantity) × Value) := do
    let ty' ← force ty
    match ty' with
    | .vPi qty binder _name dom cod =>
      if binder.isImplicit then
        let metaVal ← TCM.freshMetaVal dom
        let resultTy ← applyClosure cod metaVal
        go resultTy acc
      else
        let lvl ← TCM.currentLevel
        let dummyVal := Value.vNeutral dom (.nVar ⟨"_field", lvl⟩)
        let resultTy ← applyClosure cod dummyVal
        go resultTy (acc.push (dom, qty))
    | _ =>
      return (acc, ty')

  let (fields, resultTy) ← go ctorTy #[]

  if ← structurallyIncompatible resultTy scrutTy then
    match ctorName with
    | some name => TCM.throw (.impossiblePattern name resultTy scrutTy span)
    | none => pure ()

  unify resultTy scrutTy

  return fields

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
    let available ← collectRowFields row
    TCM.throw (.fieldNotFound fieldName row span available none)

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
  | .vDataType typeId _ =>
    -- Check if this data type is a record with named fields
    let ctx ← TCM.getCtx
    match ctx.globals.lookupFieldIndex ⟨typeId⟩ fieldName with
    | some fieldIdx =>
      -- Look up the constructor's type to extract the field type
      match ctx.globals.lookupInductive ⟨typeId⟩ with
      | some indInfo =>
        if indInfo.ctors.size == 1 then
          let ctor := indInfo.ctors[0]!
          -- Walk the constructor type (Pi chain) to find the field at fieldIdx
          let mut ty := ctor.type
          for _ in [:fieldIdx] do
            match ty with
            | .vPi _ _ _ _ cod => ty ← applyClosure cod (Value.vNeutral (.vType .zero) (.nVar ⟨"_", ⟨0⟩⟩))
            | _ => break
          match ty with
          | .vPi _ _ _ dom _ => return dom
          | _ => TCM.throw (.expectedRecord recTy' span #[])
        else
          TCM.throw (.expectedRecord recTy' span #[])
      | none => TCM.throw (.expectedRecord recTy' span #[])
    | none =>
      let available := match ctx.globals.lookupInductive ⟨typeId⟩ with
        | some indInfo => indInfo.fieldNames
        | none => #[]
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
    let available ← collectRowFields row'
    TCM.throw (.fieldNotFound labelStr row' span available none)

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
  | .var name => s!"var({name.name})"
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
  | .fieldAccess _ field _ => s!".{field.name}"
  | .projection tn fn _ => s!"proj({tn.name}.{fn.name})"
  | .parens _ _ => "parens"
  | .typeAnnot _ _ _ => "ann"
  | .typeApp _ _ => "typeApp"
  | .composeBlock stmts _ _ => s!"composeBlock({stmts.size} stmts)"
  | .variant label _ _ => s!"variant(.{label.name})"

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

/-- A binding produced by pattern elaboration -/
structure PatternBinding where
  fvarId : Unique
  name : String
  type : Value
  qty : Quantity
  deriving Inhabited

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

/-- Convert a Syntax.Pattern to a Core.Pattern and the `PatternBinding`s it introduces -/
partial def convertPatternWithBindings
    (pat : Soma.Syntax.Pattern) (scrutTy : Value) (scrutQty : Quantity)
    : TCM (Soma.Core.Pattern × List PatternBinding) := do
  match pat with
  | .var name =>
    let u ← TCM.freshUnique name.name
    pure (.var (some u), [{ fvarId := u, name := name.name, type := scrutTy, qty := scrutQty }])
  | .wildcard _ => pure (.wildcard, [])
  | .lit l =>
    pure (.lit (match l with
      | .int n _ => .int n
      | .string s _ => .string s
      | .bool b _ => .bool b), [])
  | .con name args span => do
    let ctorInfo? ← do
      match ← TCM.lookupGlobal name.path name.name with
      | some info =>
        if info.isConstructor then pure (some info)
        else
          -- If the name is a record type, use its `New` constructor
          match ← TCM.lookupGlobal (name.path.push name.name) "New" with
          | some newInfo => if newInfo.isConstructor then pure (some newInfo) else pure none
          | none => pure none
      | none => pure none
    match ctorInfo? with
    | some ctorInfo =>
      let fields ← extractConstructorFieldTypes ctorInfo.type scrutTy (some name.name) span
      let mut coreArgs : Array Soma.Core.Pattern := #[]
      let mut bindings : List PatternBinding := []
      for h : i in [:args.size] do
        let arg := args[i]
        let (fieldTy, fieldQty) ← if h' : i < fields.size then
          pure fields[i]
        else
          let ty ← TCM.freshMetaVal (.vType .zero)
          pure (ty, .omega)
        let (corePat, argBindings) ← convertPatternWithBindings arg fieldTy (scrutQty * fieldQty)
        coreArgs := coreArgs.push corePat
        bindings := bindings ++ argBindings
      pure (.ctor ctorInfo.name ctorInfo.ctorTag coreArgs, bindings)
    | none =>
      TCM.throw (.unboundVariable name.name span #[])
  | .tuple elems span => do
    let (coreElems, bindings) ← convertTuplePatternWithBindings elems.toList scrutTy scrutQty
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
    let mut bindings : List PatternBinding := []
    for elem in elems do
      let (corePat, elemBindings) ← convertPatternWithBindings elem elemTy scrutQty
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
    let (coreHead, headBindings) ← convertPatternWithBindings head elemTy scrutQty
    let (coreTail, tailBindings) ← convertPatternWithBindings tail scrutTy scrutQty
    match ← TCM.lookupWiredIn .cons with
    | some info => pure (.ctor info.name info.ctorTag #[coreHead, coreTail], headBindings ++ tailBindings)
    | none => TCM.throw (.unboundGlobal "cons (no @[wired_in \"cons\"] constructor in scope)" span #[])
  | .parens inner _ => convertPatternWithBindings inner scrutTy scrutQty
  | .typed pat _ _ => convertPatternWithBindings pat scrutTy scrutQty
  | .variant label arg _ => do
    match arg with
    | some p =>
      let argTy ← TCM.freshMetaVal (.vType .zero)
      let (coreArg, bindings) ← convertPatternWithBindings p argTy scrutQty
      pure (.inject label.name (some coreArg), bindings)
    | none => pure (.inject label.name none, [])
where
  convertTuplePatternWithBindings
      (elems : List Soma.Syntax.Pattern) (ty : Value) (scrutQty : Quantity)
      : TCM (List Soma.Core.Pattern × List PatternBinding) := do
    match elems with
    | [] => return ([], [])
    | [lastElem] =>
      let (pat, bindings) ← convertPatternWithBindings lastElem ty scrutQty
      pure ([pat], bindings)
    | elem :: rest =>
      let ty' ← force ty
      match ty' with
      | .vSigma fstQty _ fstTy sndClos =>
        let (elemPat, elemBindings) ←
          convertPatternWithBindings elem fstTy (scrutQty * fstQty)
        let lvl ← TCM.currentLevel
        let dummyVal := Value.vNeutral fstTy (.nVar ⟨"_", lvl⟩)
        let sndTy ← applyClosure sndClos dummyVal
        let (restPats, restBindings) ←
          convertTuplePatternWithBindings rest sndTy scrutQty
        return (elemPat :: restPats, elemBindings ++ restBindings)
      | _ =>
        let mut pats : List Soma.Core.Pattern := []
        let mut bindings : List PatternBinding := []
        for e in (elem :: rest) do
          let eTy ← TCM.freshMetaVal (.vType .zero)
          let (p, bs) ← convertPatternWithBindings e eTy scrutQty
          pats := pats ++ [p]
          bindings := bindings ++ bs
        return (pats, bindings)

/-- Convert a list of Syntax.Patterns against parallel `(scrutineeType, scrutineeQty)` pairs -/
partial def convertPatternListWithBindings
    (pats : List Soma.Syntax.Pattern) (scruts : List (Value × Quantity))
    : TCM (Array Soma.Core.Pattern × List PatternBinding) := do
  match pats, scruts with
  | [], _ => return (#[], [])
  | pat :: rest, (ty, qty) :: tys =>
    let (corePat, patBindings) ← convertPatternWithBindings pat ty qty
    let (restPats, restBindings) ← convertPatternListWithBindings rest tys
    return (#[corePat] ++ restPats, patBindings ++ restBindings)
  | pat :: rest, [] =>
    let freshTy ← TCM.freshMetaVal (.vType .zero)
    let (corePat, patBindings) ← convertPatternWithBindings pat freshTy .omega
    let (restPats, restBindings) ← convertPatternListWithBindings rest []
    return (#[corePat] ++ restPats, patBindings ++ restBindings)


/-- Desugar a compose block into nested >>= applications -/
private def desugarCompose (stmts : Array Soma.Syntax.ComposeStmt)
    (final_ : Soma.Syntax.Expr) : Soma.Syntax.Expr :=
  stmts.foldr (init := final_) fun stmt result =>
    match stmt with
    | .bind_ name action stmtSpan =>
      let cont := Soma.Syntax.Expr.lambda #[(name, none)] result stmtSpan
      let bindOp := Soma.Syntax.Expr.var ⟨#[], ">>=", stmtSpan⟩
      .app (.app bindOp action stmtSpan) cont stmtSpan
    | .expr action stmtSpan =>
      let wildcard : Soma.Syntax.QualName := ⟨#[], "_", stmtSpan⟩
      let cont := Soma.Syntax.Expr.lambda #[(wildcard, none)] result stmtSpan
      let bindOp := Soma.Syntax.Expr.var ⟨#[], ">>=", stmtSpan⟩
      .app (.app bindOp action stmtSpan) cont stmtSpan
    | .let_ name value stmtSpan =>
      let cont := Soma.Syntax.Expr.lambda #[(name, none)] result stmtSpan
      .app cont value stmtSpan

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
      match ← TCM.lookupLocal name.name with
      | some entry =>
        useVarChecked entry.bindingId name.span
        let tyExpr ← quoteValueToExpr entry.type
        return (entry.type, .fvar entry.fvarId tyExpr)
      | none =>
        if name.path.isEmpty then
          if let some (qn, ty) ← TCM.lookupMethodSelfRef name.name then
            TCM.recordGlobalDep qn
            let tyExpr ← quoteValueToExpr ty
            return (ty, .const qn tyExpr)
        -- Check globals (functions, constructors, data types)
        match ← TCM.lookupGlobal name.path name.name with
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
          match name.name with
          | "Type" | "Type0" => return (.vType .one, .sort .zero)
          | "Type1" => return (.vType .one, .sort .one)
          | "Row" => return (.vType .zero, .rowSort)
          | "Label" => return (.vType .zero, .labelSort)
          | _ =>
            -- Recover: record the error and return a placeholder so the
            -- rest of the expression (and any other unbound references it
            -- contains) can still be elaborated and reported. The term is
            -- `panic` because the module has errors and won't reach codegen;
            -- the type is a fresh meta so `ensurePi`/unification can still
            -- make progress at use sites.
            let suggestions ← TCM.suggestSimilarNames name.name
            TCM.addError (.unboundVariable name.name name.span suggestions)
            let tyMeta ← TCM.freshMetaVal (.vType .zero)
            return (tyMeta, .panic s!"unbound variable `{name.name}`")

    -- Literals
    | .lit (.int n _) => return (.vPrimTy .int, .lit (.int n))
    | .lit (.string s _) =>
      -- Look up the String type from wired-in registry (real record, not primitive)
      let stringTy ← do
        match ← TCM.lookupWiredIn .typeString with
        | some info => pure (Value.vDataType info.name.id [])
        | none => pure (Value.vPrimTy .string)
      return (stringTy, .lit (.string s))
    | .lit (.bool b _) => return (.vPrimTy .bool, .lit (.bool b))

    -- Application: infer fn, then apply arg
    | .app fn arg span => do
      let (fnTy, fnExpr) ← inferSyntax fn
      inferSyntaxApp fnTy fnExpr arg span

    -- Infix operators: resolve op, apply to both args
    | .infix op left right span => do
      -- `a = b` desugars to the propositional equality type `Eq {A} a b`
      if op.value == "=" then
        let (lhsTy, lhsExpr) ← inferSyntax left
        let rhsExpr ← checkSyntax right lhsTy
        let tyLevel ← inferUniverse lhsTy
        let tyExpr ← quoteValueToExpr lhsTy
        return (.vType tyLevel, .eqTy tyLevel tyExpr lhsExpr rhsExpr)
      else
        -- Resolve the operator name
        let (opTy, opExpr) ← inferSyntax (.var ⟨#[], op.value, op.span⟩)
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
      let armsExpr ← inferSyntaxArms arms.toList scrutTys scrutsExpr resultTy
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
      let (fieldTy, idx) ← match normalizedTy with
        | .vRecord row =>
          let ty ← findFieldInRow row field.name span
          let idx ← match ← findFieldIndex row field.name with
            | some i => pure i
            | none => pure 0
          pure (ty, idx)
        | .vRecordVal fields =>
          match fields.find? (·.1 == field.name) with
          | some (_, ty) => pure (ty, 0)
          | none =>
            let available := fields.map (·.1) |>.toArray
            TCM.throw (.fieldNotFound field.name normalizedTy span available none)
        | .vDataType typeId _ =>
          let fieldTy ← lookupFieldType normalizedTy field.name span
          let ctx ← TCM.getCtx
          let idx := ctx.globals.lookupFieldIndex ⟨typeId⟩ field.name |>.getD 0
          pure (fieldTy, idx)
        | _ => TCM.throw (.expectedRecord normalizedTy span #[])
      return (fieldTy, .fieldAccess exprE field.name idx)

    -- Projection function: Type.field
    | .projection typeName fieldName span => do
      match ← TCM.lookupGlobal (typeName.path.push typeName.name) fieldName.name with
      | some accessorInfo =>
        let ctx ← TCM.getCtx
        let typeQN := ctx.globals.resolve ctx.currentNamespace typeName.path typeName.name
        let idx := typeQN.bind (ctx.globals.lookupFieldIndex · fieldName.name) |>.getD 0
        return (accessorInfo.type, .proj accessorInfo.name fieldName.name idx)
      | none =>
        TCM.throw (.unboundGlobal s!"{typeName}::{fieldName}" span #[])

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
      let row := Value.vRowExtend (.vLabelLit label.name) argTy rowTail
      let variantTy := Value.vVariant row
      let variantTyExpr ← quoteValueToExpr variantTy
      return (variantTy, .inject label.name argsExpr variantTyExpr)

/-- Elaborate a compose block by desugaring to >>= and elaborating the result -/
partial def inferComposeBlock (stmts : Array Soma.Syntax.ComposeStmt)
    (final_ : Soma.Syntax.Expr) (_span : Span) : TCM (Value × Soma.Core.Expr) := do
  if stmts.isEmpty then
    return ← inferSyntax final_
  inferSyntax (desugarCompose stmts final_)

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
        let (fieldTy, fieldExpr) ← inferPolymorphicFieldAccess fnExpr row name.name argSpan span
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
    (params : List (Soma.Syntax.QualName × Option Soma.Syntax.TypeExpr))
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
    let bindingId ← TCM.freshLocalId name.name
    TCM.recordLocalBindingType name.span paramTy
    -- Inference mode has no expected Pi to read quantities from, so every
    -- parameter binds at `.omega`
    withCheckedBinding name.name bindingId paramTy .omega .explicit span do
      match ← TCM.lookupLocal name.name with
      | some entry =>
        let domExpr ← quoteValueToExpr paramTy
        let (innerTy, lamExpr) ← inferSyntaxLamBody rest body span (acc ++ [(entry.fvarId, name.name, domExpr)])
        -- Build Pi type: paramTy -> innerTy
        let codClosure := Closure.const name.name innerTy
        let piTy := Value.vPi .omega .explicit name.name paramTy codClosure
        return (piTy, lamExpr)
      | none =>
        inferSyntaxLamBody rest body span acc

/-- Check lambda body against expected Pi type from Syntax params -/
partial def checkSyntaxLamBody
    (params : List (Soma.Syntax.QualName × Option Soma.Syntax.TypeExpr))
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
        let x := Value.vNeutral dom (.nVar ⟨name.name, lvl⟩)
        applyClosure cod x
      let bindingId ← TCM.freshLocalId name.name
      TCM.recordLocalBindingType name.span dom
      withCheckedBinding name.name bindingId dom qty binder span do
        match ← TCM.lookupLocal name.name with
        | some entry =>
          let domExpr ← quoteValueToExpr dom
          checkSyntaxLamBody rest body codTy span (acc ++ [(entry.fvarId, name.name, domExpr)])
        | none =>
          checkSyntaxLamBody rest body codTy span acc
    | _ =>
      let paramTy ← TCM.freshMetaVal (.vType .zero)
      let bindingId ← TCM.freshLocalId name.name
      TCM.recordLocalBindingType name.span paramTy
      TCM.withBinding name.name bindingId paramTy .omega .explicit span do
        match ← TCM.lookupLocal name.name with
        | some entry =>
          let domExpr ← quoteValueToExpr paramTy
          checkSyntaxLamBody rest body expectedTy' span (acc ++ [(entry.fvarId, name.name, domExpr)])
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
partial def inferSyntaxRecordFields (fields : List (Soma.Syntax.QualName × Soma.Syntax.Expr))
    : TCM (Value × Array (String × Soma.Core.Expr)) := do
  match fields with
  | [] => return (.vRowEmpty, #[])
  | (name, expr) :: rest => do
    let (ty, exprE) ← inferSyntax expr
    let (restRow, restFields) ← inferSyntaxRecordFields rest
    let row := Value.vRowExtend (.vLabelLit name.name) ty restRow
    return (row, #[(name.name, exprE)] ++ restFields)

/-- Infer arms of a case expression from Syntax.MatchArm -/
partial def inferSyntaxArms (arms : List Soma.Syntax.MatchArm)
    (scrutTys : List Value) (scrutExprs : Array Soma.Core.Expr) (expectedTy : Value)
    : TCM (Array Soma.Core.Arm) := do
  let ctx ← TCM.getCtx
  let mut scruts : List (Value × Quantity) := []
  let mut i : Nat := 0
  for ty in scrutTys do
    let baseQty : Quantity :=
      if h : i < scrutExprs.size then
        match scrutExprs[i] with
        | .fvar u _ =>
          match ctx.locals.find? (·.fvarId == u) with
          | some entry => entry.qty
          | none => .omega
        | _ => .omega
      else .omega
    scruts := scruts ++ [(ty, baseQty)]
    i := i + 1
  let mut results : Array Soma.Core.Arm := #[]
  let mut armUsagesList : Array UsageSnapshot := #[]
  for arm in arms do
    let pats := arm.patterns.toList
    let (corePatterns, bindings) ← convertPatternListWithBindings pats scruts
    let (bodyExpr, armUsages) ← captureUsages
      (inferSyntaxArmBodyWithBindings bindings arm.body expectedTy arm.span)
    let abstractedBody := bindings.foldl
      (fun body b => body.abstractFVar b.fvarId) bodyExpr
    results := results.push (Soma.Core.Arm.mk corePatterns abstractedBody)
    armUsagesList := armUsagesList.push armUsages
  let span := match arms.head? with
    | some arm => arm.span
    | none => default
  let joined ← checkMultiBranchUsages armUsagesList span
  applyUsages joined
  Coverage.checkExhaustiveness results scrutTys span
  return results

/-- Extend the context with pattern bindings (each carrying its computed QTT
    quantity) and check the arm body against the expected arm type -/
partial def inferSyntaxArmBodyWithBindings
    (bindings : List PatternBinding)
    (body : Soma.Syntax.Expr) (expectedTy : Value) (span : Span)
    : TCM Soma.Core.Expr := do
  match bindings with
  | [] => checkSyntax body expectedTy
  | b :: rest =>
    withCheckedBinding b.name b.fvarId b.type b.qty .explicit span do
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

    | .lit (.int n _), .vPrimTy pt => do
      if pt.isIntegral then
        return .lit (.int n)
      else if pt.isFloating then
        return .lit (.float (Float.ofInt n))
      else
        let (inferred, expr) ← inferSyntax e
        let (inferred', expr') ← insertImplicits inferred expr e.span
        unify inferred' expected'
        solveImplicitsGreedy
        return expr'

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
