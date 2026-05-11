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
import Soma.Dependent.Solver
import Soma.Dependent.Telescope
import Soma.Dependent.Error
import Soma.Dependent.Usage
import Soma.Dependent.Zonk
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
    let domMeta ← TCM.freshMetaVal (.vType .zero)
    let codMeta ← TCM.freshMetaVal (.vType .zero)
    let codClosure := Closure.const "?cod" codMeta
    let piTy := Value.vPi .omega .explicit "?dom" domMeta codClosure
    TCM.solveMeta mid piTy "ensurePi-meta"
    return (.omega, .explicit, "?dom", domMeta, codClosure)
  | .vNeutral _ neu =>
    match neu.head with
    | .hMeta _ =>
      let domMeta ← TCM.freshMetaVal (.vType .zero)
      let codMeta ← TCM.freshMetaVal (.vType .zero)
      let codClosure := Closure.const "?cod" codMeta
      let piTy := Value.vPi .omega .explicit "?dom" domMeta codClosure
      try
        Soma.Dependent.unify v' piTy
        return (.omega, .explicit, "?dom", domMeta, codClosure)
      catch _ =>
        TCM.throw (.expectedFunction v' span origin)
    | _ => TCM.throw (.expectedFunction v' span origin)
  | _ =>
    TCM.throw (.expectedFunction v' span origin)

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

private partial def isSortDomain : Value → Bool
  | .vType _ | .vRowSort | .vLabelSort => true
  | .vPi _ _ name dom cod =>
    isSortDomain dom &&
      let neutral := Value.vNeutral dom (.nVar ⟨name, cod.level?.getD ⟨0⟩⟩)
      isSortDomain (cod.applyPure neutral)
  | _ => false

/-- Insert implicit arguments for a function type, tracking created metavariables -/
partial def insertImplicitsCore (fnTy : Value) (fnExpr : Soma.Core.Expr) (span : Span)
    : TCM (Value × Soma.Core.Expr × Array (MetaId × Value × String)) := do
  let fnTy' ← force fnTy
  match fnTy' with
  | .vPi _qty binder name dom cod =>
    if binder.isImplicit then
      let piLvl := cod.level?.map (·.lvl)

      let fresh ←
        if binder == .instance_ then
          Soma.Dependent.freshMetaWithPolicy dom {
            kind := .instanceArg
            abstractLocals := false
            piLevel := piLvl
          }
        else
          let dom' ← force dom
          let nextIsInstance ← do
            let lvl ← TCM.currentLevel
            let neutral := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
            let nextTy ← applyClosure cod neutral
            match ← force nextTy with
            | .vPi _ .instance_ _ _ _ => pure true
            | _ => pure false
          Soma.Dependent.freshMetaWithPolicy dom {
            kind := .autoImplicit
            abstractLocals := true
            includeInstanceLocals := false
            includeTermLocals := !(isSortDomain dom' && nextIsInstance)
            piLevel := piLvl
          }
      let metaId := fresh.id
      let argMeta := fresh.value
      let argExpr := fresh.expr

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

private def valueMentionsTrackedMeta
    (v : Value) (metas : Array (MetaId × Value × String)) : Bool :=
  let tracked := metas.map (fun (m, _, _) => m)
  (Value.collectMetas v).any fun m => tracked.contains m

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
      if valueMentionsTrackedMeta dom existingMetas then
        return none
      let lvl ← TCM.currentLevel
      let argVal := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
      let resultTy ← applyClosure cod argVal
      projectResultTypeWithMetas resultTy (numExplicitArgs - 1) existingMetas
  | _ => return none

/-- Insert implicit arguments with expected type guidance and full bidirectional propagation -/
partial def insertImplicitsWithExpected (fnTy : Value) (fnExpr : Soma.Core.Expr)
    (expected : Option Value) (numExplicitArgs : Nat) (span : Span)
    : TCM (Value × Soma.Core.Expr) := do
  -- Insert implicits and track the metas created
  let (fnTy', fnExpr', implicitMetas) ← insertImplicitsCore fnTy fnExpr span

  -- If we have an expected type, use it to solve implicits early
  match expected with
  | none =>
    let _ ← solveConstraints
    let finalTy ← force fnTy'
    return (finalTy, fnExpr')
  | some expectedTy =>
    if implicitMetas.isEmpty || numExplicitArgs > 0 then
      let _ ← solveConstraints
      let finalTy ← force fnTy'
      return (finalTy, fnExpr')
    else
      match ← projectResultTypeWithMetas fnTy' numExplicitArgs implicitMetas with
      | some resultTy =>
        -- Unify projected result with expected type
        let _ ← tryUnify resultTy expectedTy
        let _ ← solveConstraints
        let finalTy ← force fnTy'
        return (finalTy, fnExpr')
      | none =>
        let _ ← solveConstraints
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
      if success then
        let _ ← solveConstraints
      return success
  | none => return false

/-- Aggressively propagate type information during inference -/
def propagateTypeInfo (inferredTy : Value) (targetTy : Value) : TCM Unit := do
  unify inferredTy targetTy
  let _ ← solveConstraints


/-- Build nested Core lambdas from `(fvar, name, domainExpr)` bindings. -/
partial def buildLambdas (bindings : List (Unique × String × Soma.Core.Expr))
    (body : Soma.Core.Expr) : Soma.Core.Expr :=
  match bindings with
  | [] => body
  | (fvar, name, domExpr) :: rest =>
    let innerBody := buildLambdas rest body
    let closedBody := Soma.Core.Expr.abstractFVar innerBody fvar
    .lam .explicit name domExpr closedBody

/-- Quote a `Value` to a Core `Expr` at the current elaboration depth -/
partial def quoteValueToExpr (v : Value) : TCM Soma.Core.Expr := do
  let depth ← TCM.currentLevel
  return Soma.Core.quoteExpr depth v

/-- Quote a `Value` as a type annotation -/
partial def quoteTypeAnn (v : Value) : TCM Soma.Core.Expr := do
  return Soma.Core.quoteExpr0 v

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

/-- Like `instantiateImplicits` but also returns the list of meta values inserted -/
partial def instantiateImplicitsTracked (ty : Value)
    : TCM (Value × Array (Value × Value)) := do
  let ty' ← force ty
  match ty' with
  | .vPi _qty binder _name dom cod =>
    if binder.isImplicit then
      let metaVal ← TCM.freshMetaVal dom
      let resultTy ← applyClosure cod metaVal
      let (finalTy, metas) ← instantiateImplicitsTracked resultTy
      return (finalTy, #[(metaVal, dom)] ++ metas)
    else
      return (ty', #[])
  | _ =>
    return (ty', #[])

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

  let resForced ← force resultTy
  let scrutForced ← force scrutTy
  match resForced, scrutForced with
  | .vDataType id1 ps1, .vDataType id2 ps2 =>
    if id1 == id2 ∧ ps1.length == ps2.length then
      for (p1, p2) in ps1.zip ps2 do
        let p1f ← force p1
        match p1f with
        | .vNeutral _ neu =>
          if neu.spine.isEmpty then
            match neu.head with
            | .hMeta mid =>
              if !(← TCM.isMetaSolved mid) then
                -- Skip self-reference to avoid creating a meta cycle
                let p2f ← force p2
                let p2HasMeta := match p2f with
                  | .vNeutral _ neu2 =>
                    match neu2.head with
                    | .hMeta mid2 => mid == mid2
                    | _ => false
                  | _ => false
                if !p2HasMeta then
                  TCM.solveMeta mid p2f
            | _ => pure ()
        | _ => pure ()
  | _, _ => pure ()

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

/-- Walk a record constructor's Pi chain to find the type of the field at `fieldIdx` -/
partial def fieldTypeFromCtor (ctorTy : Value) (typeArgs : List Value) (fieldIdx : Nat)
    : TCM (Option Value) := do
  let ty ← force ctorTy
  match ty with
  | .vPi _ binder _ dom cod =>
    if binder.isImplicit && !typeArgs.isEmpty then
      let (arg, restArgs) ← match typeArgs with
        | a :: rest => pure (a, rest)
        | [] => pure (← TCM.freshMetaVal dom, [])
      let next ← applyClosure cod arg
      fieldTypeFromCtor next restArgs fieldIdx
    else
      if fieldIdx == 0 then
        return some dom
      else
        let lvl ← TCM.currentLevel
        let placeholder := Value.vNeutral dom (.nVar ⟨"_field", lvl⟩)
        let next ← applyClosure cod placeholder
        fieldTypeFromCtor next typeArgs (fieldIdx - 1)
  | _ => return none

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
  | .vDataType typeId args =>
    -- Check if this data type is a record with named fields
    let ctx ← TCM.getCtx
    match ctx.globals.lookupFieldIndex ⟨typeId⟩ fieldName with
    | some fieldIdx =>
      -- Look up the constructor's type to extract the field type
      match ctx.globals.lookupInductive ⟨typeId⟩ with
      | some indInfo =>
        if indInfo.ctors.size == 1 then
          let ctor := indInfo.ctors[0]!
          match ← fieldTypeFromCtor ctor.type args fieldIdx with
          | some fieldTy => return fieldTy
          | none => TCM.throw (.expectedRecord recTy' span #[])
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
  | .con name => s!"con({name.name})"
  | .arrow _ _ _ => "arrow"
  | .pi _ _ _ _ _ _ => "pi"
  | .sigma _ _ _ _ _ => "sigma"
  | .forall_ vars _ _ => s!"forall({vars.size})"
  | .recordTy _ _ _ => "recordTy"
  | .variantTy _ _ _ => "variantTy"
  | .listTy _ _ => "listTy"

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
  nbeValue? : Option Value := none
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

/-- Convert a Syntax.Pattern to a Core.Pattern, a pattern Value and the `PatternBinding`s it introduces -/
partial def convertPatternWithBindings
    (pat : Soma.Syntax.Pattern) (scrutTy : Value) (scrutQty : Quantity)
    (startLvl : Nat) (scrutVal? : Option Value := none)
    : TCM (Soma.Core.Pattern × Value × List PatternBinding × Nat) := do
  match pat with
  | .var name =>
    let u ← TCM.freshUnique name.name
    TCM.recordLocalBindingType name.span scrutTy
    match scrutVal? with
    | some scrutVal =>
      -- Top-level var pattern: alias the scrutinee
      let b : PatternBinding :=
        { fvarId := u, name := name.name, type := scrutTy, qty := scrutQty,
          nbeValue? := some scrutVal }
      pure (.var (some u), scrutVal, [b], startLvl + 1)
    | none =>
      -- Nested var pattern: allocate a fresh neutral at startLvl
      let patVal := Value.vNeutral scrutTy (.nVar ⟨name.name, ⟨startLvl⟩⟩)
      let b : PatternBinding :=
        { fvarId := u, name := name.name, type := scrutTy, qty := scrutQty }
      pure (.var (some u), patVal, [b], startLvl + 1)
  | .wildcard _ =>
    -- Wildcards: bind no name
    let patVal ← TCM.freshMetaVal scrutTy
    pure (.wildcard, patVal, [], startLvl)
  | .lit l =>
    let (corePat, patVal) := match l with
      | .int n _ => ((.lit (.int n) : Soma.Core.Pattern), Value.vIntLit n)
      | .string s _ => (.lit (.string s), Value.vStringLit s)
      | .bool b _ =>
        let ctor : Value :=
          if b
          then .vConstructor ⟨⟨0, "", "True"⟩⟩ 0 [] (.vPrimTy .bool)
          else .vConstructor ⟨⟨0, "", "False"⟩⟩ 1 [] (.vPrimTy .bool)
        (.lit (.bool b), ctor)
    pure (corePat, patVal, [], startLvl)
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
      let mut argVals : Array Value := #[]
      let mut bindings : List PatternBinding := []
      let mut curLvl := startLvl
      for h : i in [:args.size] do
        let arg := args[i]
        let (fieldTy, fieldQty) ← if h' : i < fields.size then
          pure fields[i]
        else
          let ty ← TCM.freshMetaVal (.vType .zero)
          pure (ty, .omega)
        let (corePat, argVal, argBindings, curLvl') ←
          convertPatternWithBindings arg fieldTy (scrutQty * fieldQty) curLvl
        coreArgs := coreArgs.push corePat
        argVals := argVals.push argVal
        bindings := bindings ++ argBindings
        curLvl := curLvl'
      let patVal := Value.vConstructor ctorInfo.name ctorInfo.ctorTag argVals.toList scrutTy
      pure (.ctor ctorInfo.name ctorInfo.ctorTag coreArgs, patVal, bindings, curLvl)
    | none =>
      TCM.throw (.unboundVariable name.name span #[])
  | .tuple elems span => do
    let (coreElems, elemVals, bindings, nextLvl) ←
      convertTuplePatternWithBindings elems.toList scrutTy scrutQty startLvl
    let nested ← buildNestedPairPattern coreElems span
    let patVal ← buildNestedPairValue elemVals span
    pure (nested, patVal, bindings, nextLvl)
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
    let mut elemVals : List Value := []
    let mut bindings : List PatternBinding := []
    let mut curLvl := startLvl
    for elem in elems do
      let (corePat, elemVal, elemBindings, curLvl') ←
        convertPatternWithBindings elem elemTy scrutQty curLvl
      coreElems := coreElems ++ [corePat]
      elemVals := elemVals ++ [elemVal]
      bindings := bindings ++ elemBindings
      curLvl := curLvl'
    let listPat ← buildListPattern coreElems span
    let listVal ← buildListValue elemVals elemTy scrutTy span
    pure (listPat, listVal, bindings, curLvl)
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
    let (coreHead, headVal, headBindings, midLvl) ←
      convertPatternWithBindings head elemTy scrutQty startLvl
    let (coreTail, tailVal, tailBindings, endLvl) ←
      convertPatternWithBindings tail scrutTy scrutQty midLvl
    match ← TCM.lookupWiredIn .cons with
    | some info =>
      let consVal := Value.vConstructor info.name info.ctorTag [headVal, tailVal] scrutTy
      pure (.ctor info.name info.ctorTag #[coreHead, coreTail], consVal,
            headBindings ++ tailBindings, endLvl)
    | none => TCM.throw (.unboundGlobal "cons (no @[wired_in \"cons\"] constructor in scope)" span #[])
  | .parens inner _ => convertPatternWithBindings inner scrutTy scrutQty startLvl scrutVal?
  | .typed pat _ _ => convertPatternWithBindings pat scrutTy scrutQty startLvl scrutVal?
  | .variant label arg _ => do
    -- Synthesize a QualifiedName uniquely identified by the label string
    let qn : Soma.Core.QualifiedName :=
      ⟨{ id := label.name.hash.toNat, module := "__variant", original := label.name }⟩
    match arg with
    | some p =>
      let argTy ← TCM.freshMetaVal (.vType .zero)
      let (coreArg, argVal, bindings, nextLvl) ←
        convertPatternWithBindings p argTy scrutQty startLvl
      let patVal := Value.vConstructor qn 0 [argVal] scrutTy
      pure (.inject label.name (some coreArg), patVal, bindings, nextLvl)
    | none =>
      let patVal := Value.vConstructor qn 0 [] scrutTy
      pure (.inject label.name none, patVal, [], startLvl)
where
  convertTuplePatternWithBindings
      (elems : List Soma.Syntax.Pattern) (ty : Value) (scrutQty : Quantity)
      (startLvl : Nat)
      : TCM (List Soma.Core.Pattern × List Value × List PatternBinding × Nat) := do
    match elems with
    | [] => return ([], [], [], startLvl)
    | [lastElem] =>
      let (pat, val, bindings, nextLvl) ←
        convertPatternWithBindings lastElem ty scrutQty startLvl
      pure ([pat], [val], bindings, nextLvl)
    | elem :: rest =>
      let ty' ← force ty
      match ty' with
      | .vDataType _ (fstTy :: sndTy :: _) =>
        let (elemPat, elemVal, elemBindings, midLvl) ←
          convertPatternWithBindings elem fstTy scrutQty startLvl
        let (restPats, restVals, restBindings, nextLvl) ←
          convertTuplePatternWithBindings rest sndTy scrutQty midLvl
        return (elemPat :: restPats, elemVal :: restVals,
                elemBindings ++ restBindings, nextLvl)
      | _ =>
        let mut pats : List Soma.Core.Pattern := []
        let mut vals : List Value := []
        let mut bindings : List PatternBinding := []
        let mut curLvl := startLvl
        for e in (elem :: rest) do
          let eTy ← TCM.freshMetaVal (.vType .zero)
          let (p, v, bs, curLvl') ←
            convertPatternWithBindings e eTy scrutQty curLvl
          pats := pats ++ [p]
          vals := vals ++ [v]
          bindings := bindings ++ bs
          curLvl := curLvl'
        return (pats, vals, bindings, curLvl)
  buildNestedPairValue (vs : List Value) (span : Span) : TCM Value := do
    match vs with
    | [] => pure (.vNeutral (.vPrimTy .unit) (.nVar ⟨"_unit", ⟨0⟩⟩))
    | [v] => pure v
    | v :: rest =>
      let restV ← buildNestedPairValue rest span
      match ← TCM.lookupWiredIn .pair with
      | some info =>
        let fstTy ← inferValueType v
        let sndTy ← inferValueType restV
        let pairTy ← match ← TCM.lookupWiredIn .typePair with
          | some tyInfo => pure (Value.vDataType tyInfo.name.id [fstTy, sndTy])
          | none =>
            TCM.throw (.unboundGlobal "Pair (no @[wired_in \"type.pair\"] type in scope)" span #[])
        pure (.vConstructor info.name info.ctorTag [v, restV] pairTy)
      | none =>
        TCM.throw (.unboundGlobal "pair (no @[wired_in \"pair\"] constructor in scope)" span #[])
  buildListValue (vs : List Value) (elemTy scrutTy : Value) (span : Span) : TCM Value := do
    match vs with
    | [] =>
      match ← TCM.lookupWiredIn .nil with
      | some info =>
        pure (.vConstructor info.name info.ctorTag [] scrutTy)
      | none => TCM.throw (.unboundGlobal "nil (no @[wired_in \"nil\"] constructor in scope)" span #[])
    | v :: rest =>
      let restV ← buildListValue rest elemTy scrutTy span
      match ← TCM.lookupWiredIn .cons with
      | some info =>
        pure (.vConstructor info.name info.ctorTag [v, restV] scrutTy)
      | none => TCM.throw (.unboundGlobal "cons (no @[wired_in \"cons\"] constructor in scope)" span #[])
  inferValueType (v : Value) : TCM Value := do
    match v with
    | .vNeutral ty _ => pure ty
    | .vConstructor _ _ _ ty => pure ty
    | .vIntLit _ => pure (.vPrimTy .int)
    | .vStringLit _ => pure (.vPrimTy .string)
    | .vFloatLit _ => pure (.vPrimTy .double)
    | _ => pure (.vType .zero)

/-- Convert a pattern row against parallel scrutinee -/
partial def convertPatternListWithBindings
    (pats : List Soma.Syntax.Pattern)
    (scruts : List (Value × Quantity × Value))
    (startLvl : Nat)
    : TCM (Array Soma.Core.Pattern × Array Value × List PatternBinding × Nat) := do
  goList pats scruts startLvl LevelSubst.empty #[] #[] []
where
  goList (pats : List Soma.Syntax.Pattern)
      (scruts : List (Value × Quantity × Value)) (curLvl : Nat)
      (σ : LevelSubst)
      (accPats : Array Soma.Core.Pattern) (accVals : Array Value)
      (accBindings : List PatternBinding)
      : TCM (Array Soma.Core.Pattern × Array Value × List PatternBinding × Nat) := do
    match pats, scruts with
    | [], _ =>
      let refinedBindings ← accBindings.mapM fun b => do
        let ty' ← substValue σ b.type
        pure { b with type := ty' }
      return (accPats, accVals, refinedBindings, curLvl)
    | pat :: rest, (ty, qty, scrutVal) :: restScruts =>
      let refinedTy ← substValue σ ty
      let refinedScrutVal ← substValue σ scrutVal
      let (corePat, patVal, patBindings, midLvl) ←
        convertPatternWithBindings pat refinedTy qty curLvl (some refinedScrutVal)
      let σ' ← do
        if patternConcretelyMatches corePat then
          match ← scrutLevel? refinedScrutVal with
          | some lvl => pure (σ.extend lvl patVal)
          | none => pure σ
        else pure σ
      goList rest restScruts midLvl σ'
        (accPats.push corePat) (accVals.push patVal)
        (accBindings ++ patBindings)
    | pat :: rest, [] =>
      let freshTy ← TCM.freshMetaVal (.vType .zero)
      let (corePat, patVal, patBindings, midLvl) ←
        convertPatternWithBindings pat freshTy .omega curLvl none
      goList rest [] midLvl σ
        (accPats.push corePat) (accVals.push patVal)
        (accBindings ++ patBindings)
  /-- True when the pattern pins the scrutinee to a specific structural shape -/
  patternConcretelyMatches : Soma.Core.Pattern → Bool
    | .ctor _ _ _ => true
    | .lit _ => true
    | .inject _ _ => true
    | .var _ | .wildcard => false
  /-- Extract the de Bruijn level of a value that is a bare bound variable -/
  scrutLevel? (v : Value) : TCM (Option DeBruijnLvl) := do
    match ← force v with
    | .vNeutral _ neu =>
      if neu.isBareHead then
        match neu.head with
        | .hVar bv => return some bv.level
        | _ => return none
      else return none
    | _ => return none


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

/-- Extract a scrutinee's stored type from the local context without running full inference -/
private def peekScrutineeType (scrut : Soma.Syntax.Expr) : TCM (Option Value) := do
  match scrut with
  | .var name =>
    match ← TCM.lookupLocal name.name with
    | some entry => return some entry.type
    | none => return none
  | .parens inner _ => peekScrutineeType inner
  | .typeAnnot e _ _ => peekScrutineeType e
  | _ => return none

/-- Does every scrutinee of a prospective case expression have a type that permits the small-elim rule? -/
private def allScrutineesSmallElimAble (scruts : List Soma.Syntax.Expr) : TCM Bool := do
  if scruts.isEmpty then return false
  scruts.allM fun scrut => do
    let some ty ← peekScrutineeType scrut | return false
    match ← force ty with
    | .vDataType uid _ =>
      let ctx ← TCM.getCtx
      match ctx.globals.lookupInductive ⟨uid⟩ with
      | some info => isInductiveSmall info
      | none => return false
    | _ => return false

/-- A pattern is trivial when it performs no observation on its scrutinee, only name-binding -/
private partial def patternIsTrivial : Soma.Syntax.Pattern → Bool
  | .var _ => true
  | .wildcard _ => true
  | .parens inner _ => patternIsTrivial inner
  | .typed inner _ _ => patternIsTrivial inner
  | _ => false

/-- Does the scrutinee at position `idx` receive only trivial patterns across every arm? -/
private def scrutineeTriviallyMatched
    (arms : List Soma.Syntax.MatchArm) (idx : Nat) : Bool :=
  arms.all fun arm =>
    match arm.patterns[idx]? with
    | some pat => patternIsTrivial pat
    | none => true

/-- Is it safe to elaborate this scrutinee in erased context? -/
private def scrutineeCanBeErased
    (scrut : Soma.Syntax.Expr) (idx : Nat)
    (arms : List Soma.Syntax.MatchArm) : TCM Bool := do
  if scrutineeTriviallyMatched arms idx then return true
  let some ty ← peekScrutineeType scrut | return false
  match ← force ty with
  | .vDataType uid _ =>
    let ctx ← TCM.getCtx
    match ctx.globals.lookupInductive ⟨uid⟩ with
    | some info => isInductiveSmall info
    | none => return false
  | _ => return false

/-- Detect attempted non-small Prop → Type elimination and raise a dedicated `propElimToType` diagnostic -/
private def checkPropElimSoundness
    (scruts : List Soma.Syntax.Expr)
    (arms : List Soma.Syntax.MatchArm)
    (motiveTy? : Option Value) : TCM Unit := do
  let motiveIsProp ← match motiveTy? with
    | some m => valueInPropUniverse m
    | none => pure false
  if motiveIsProp then return
  for h : i in [:scruts.length] do
    have : i < scruts.length := h.upper
    let scrut := scruts[i]
    if scrutineeTriviallyMatched arms i then continue
    let some ty ← peekScrutineeType scrut | continue
    let forced ← force ty
    match forced with
    | .vDataType uid _ =>
      let ctx ← TCM.getCtx
      match ctx.globals.lookupInductive ⟨uid⟩ with
      | some info =>
        if info.headSort.isProp then
          let small ← isInductiveSmall info
          if !small then
            let motiveDisplay ← match motiveTy? with
              | some m => pure m
              | none => pure (Value.vType Level.zero)
            TCM.throw (.propElimToType forced motiveDisplay scrut.span)
      | none => continue
    | _ => continue

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
        let tyExpr ← quoteTypeAnn entry.type
        return (entry.type, .fvar entry.fvarId tyExpr)
      | none =>
        if name.path.isEmpty then
          if let some (qn, ty) ← TCM.lookupMethodSelfRef name.name then
            TCM.recordGlobalDep qn
            let tyExpr ← quoteTypeAnn ty
            return (ty, .const qn tyExpr)
        -- Check globals (functions, constructors, data types)
        match ← TCM.lookupGlobal name.path name.name with
        | some info =>
          let qn := info.name
          if info.isConstructor then
            let (instantiatedTy, metas) ← instantiateImplicitsTracked info.type
            let tyExpr ← quoteTypeAnn info.type
            let mut expr : Soma.Core.Expr := .const qn tyExpr
            for (metaVal, _) in metas do
              let metaExpr ← quoteValueToExpr metaVal
              expr := .app expr metaExpr
            return (instantiatedTy, expr)
          else if info.origin == .typeDecl then
            match ← TCM.lookupWiredPrimitiveOfGlobal qn with
            | some primTy =>
              if primTy.isNullary then
                return (info.type, .primTy primTy)
              else
                return (info.type, .dataTy qn.id #[])
            | none =>
              return (info.type, .dataTy qn.id #[])
          else
            let tyExpr ← quoteTypeAnn info.type
            return (info.type, .const qn tyExpr)
        | none =>
          match name.name with
          | "Type" =>
            let u ← TCM.freshLevel "u"
            return (.vType (.succ u), .sort u)
          | "Type0" => return (.vType .one, .sort .zero)
          | "Type1" => return (.vType (.lit 2), .sort .one)
          | "Prop" => return (.vType .zero, .sort .prop)
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
      match fn with
      | .lambda #[(name, none)] body lamSpan =>
        inferLetStyle name body arg lamSpan
      | _ =>
        let (fnTy, fnExpr) ← inferSyntax fn
        inferSyntaxApp fnTy fnExpr arg span

    -- Infix operators: resolve op, apply to both args
    | .infix op left right span => do
      -- `a = b` desugars to the propositional equality type `Eq {A} a b`
      if op.value == "=" then
        let _eqInfo ← requireUniqueWiredRole .typeEq span
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
    | .case scruts arms caseSpan => do
      checkPropElimSoundness scruts.toList arms.toList none
      let erasedFlags ← scruts.toList.mapIdxM fun i scrut =>
        scrutineeCanBeErased scrut i arms.toList
      let (scrutTys, scrutsExpr) ←
        inferSyntaxListErased (scruts.toList.zip erasedFlags)
      let level ← TCM.freshLevel "caseU"
      let resultTy ← TCM.freshMetaVal (.vType level)
      let motive := buildConstantMotive scrutTys resultTy
      let armsExpr ← checkSyntaxArms arms.toList scrutTys scrutsExpr motive caseSpan
      let motiveExpr ← quoteValueToExpr motive
      return (resultTy, .«case» scrutsExpr motiveExpr armsExpr)

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

    | .typeAnnot expr ty _ => do
      let tyExpr ← TCM.inErasedContext do inferTypeExpr ty
      let tyVal ← TCM.evalExpr tyExpr
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

    -- Upper-case type-constructor identifier
    | .con name => do
      inferSyntaxCore (.var name)

    -- Non-dependent function type `A -> B`
    | .arrow from_ to _ => do
      let fromExpr ← inferTypeExpr from_
      let toExpr ← inferTypeExpr to
      let fromVal ← TCM.evalExpr fromExpr
      let qty : Soma.Core.Quantity :=
        if (← shouldAutoEraseBinder fromVal) then .zero else .omega
      let toVal ← TCM.evalExpr toExpr
      let piUniv : Soma.Core.Level :=
        if (← valueInPropUniverse toVal) then .prop else .zero
      return (.vType piUniv,
        .pi qty .explicit "_" fromExpr toExpr.shiftUp)

    -- Dependent function type `(x : A) -> B`, `{x : A} -> B`, `{{x : A}} -> B`
    | .pi qty binder name domain codomain _ => do
      let domExpr ← inferTypeExpr domain
      let domVal ← TCM.evalExpr domExpr
      -- Auto-erasure: a binder whose type is a universe or a proposition is always at quantity 0 (erased)
      let autoErase ← shouldAutoEraseBinder domVal
      let effectiveQty ←
        if qty == .omega ∧ autoErase then
          pure .zero
        else
          pure qty
      let bindingId ← TCM.freshLocalId name.name
      TCM.recordLocalBindingType name.span domVal
      let codExpr ← TCM.withBinding name.name bindingId domVal effectiveQty binder name.span do
        inferTypeExpr codomain
      -- Impredicativity: (x : A) -> B lives in Prop if B does, even when A : Type n with n > 0
      let codVal ← TCM.evalExpr codExpr
      let piUniv : Soma.Core.Level :=
        if (← valueInPropUniverse codVal) then .prop else .zero
      return (.vType piUniv,
        .pi effectiveQty binder name.name domExpr codExpr)

    -- Dependent pair type `(x : A) × B`
    | .sigma qty name fst snd _ => do
      let fstExpr ← inferTypeExpr fst
      let fstVal ← TCM.evalExpr fstExpr
      let bindingId ← TCM.freshLocalId name.name
      TCM.recordLocalBindingType name.span fstVal
      let sndExpr ← TCM.withBinding name.name bindingId fstVal qty .explicit name.span do
        inferTypeExpr snd
      let sigmaTypeInfo ← requireUniqueWiredRole .typeSigma name.span
      let bExpr := Soma.Core.Expr.lam .explicit name.name fstExpr sndExpr
      return (.vType Level.zero,
        Soma.Core.Expr.dataTy sigmaTypeInfo.name.id #[fstExpr, bExpr])

    -- Universal quantification `forall a b. T`
    | .forall_ vars body _ => do
      inferForallChain vars.toList body

    | .recordTy fields tail _ => do
      let rowExpr ← buildRowExpr fields tail
      return (.vType Level.zero, .recordTy rowExpr)

    | .variantTy cases tail _ => do
      let rowExpr ← buildRowExpr cases tail
      return (.vType Level.zero, .variantTy rowExpr)

    -- List type `[A]`
    | .listTy elem span => do
      let elemExpr ← inferTypeExpr elem
      let listInfo ← requireUniqueWiredRole .typeList span
      return (.vType Level.zero, .dataTy listInfo.name.id #[elemExpr])

/-- Elaborate `∀ b1 b2 .. bN. body` into a nested Pi Core.Expr -/
partial def inferForallChain
    (vars : List Soma.Syntax.TypeVarBinder) (body : Soma.Syntax.Expr)
    : TCM (Value × Soma.Core.Expr) := do
  match vars with
  | [] =>
    let bodyExpr ← inferTypeExpr body
    return (.vType Level.zero, bodyExpr)
  | v :: rest => do
    let (domExpr, domVal, name, span, info, userQty) ← match v with
      | .mk n kind? q _bi =>
          let kExpr ← match kind? with
            | some k => inferTypeExpr k
            | none   => pure (.sort Level.zero)
          let kVal ← TCM.evalExpr kExpr
          pure (kExpr, kVal, n.name, n.span, Soma.Core.BinderInfo.implicit, q)
      | .constraint n? cstr =>
          let head : Soma.Syntax.Expr := .con cstr.className
          let appExpr := cstr.args.foldl
            (fun acc a => Soma.Syntax.Expr.app acc a cstr.span) head
          let kExpr ← inferTypeExpr appExpr
          let kVal ← TCM.evalExpr kExpr
          let bname := match n? with | some n => n.name | none => "_"
          let bspan := match n? with | some n => n.span | none => cstr.span
          pure (kExpr, kVal, bname, bspan, Soma.Core.BinderInfo.instance_, .omega)
    let effectiveQty : Soma.Core.Quantity ← match userQty with
      | .zero => pure .zero
      | .one => pure .one
      | .omega =>
        let autoErase ← shouldAutoEraseBinder domVal
        pure (if autoErase then .zero else .omega)
    let bindingId ← TCM.freshLocalId name
    TCM.recordLocalBindingType span domVal
    let (_, restExpr) ← TCM.withBinding name bindingId domVal
        effectiveQty info span do
      inferForallChain rest body
    return (.vType Level.zero,
      .pi effectiveQty info name domExpr restExpr)

/-- Elaborate a sub-expression appearing in type position -/
partial def inferTypeExpr (e : Soma.Syntax.Expr) : TCM Soma.Core.Expr :=
  TCM.inErasedContext do
    match e with
    | .tuple _ _ =>
      checkSyntax e (.vType Level.zero)
    | .parens inner _ => inferTypeExpr inner
    | _ =>
      let (_, expr) ← inferSyntax e
      pure expr

/-- Elaborate an explicit type application argument -/
partial def elaborateTypeArg (typeArg : Soma.Syntax.TypeAppArg) : TCM Value := do
  match typeArg with
  | .label labelName =>
    match ← TCM.lookupLocal labelName.name with
    | some entry =>
      pure (Value.vNeutral entry.type (Neutral.nVar ⟨labelName.name, entry.level⟩))
    | none =>
      pure (Value.vLabelLit labelName.name)
  | .type tyExpr =>
    let expr ← inferTypeExpr tyExpr
    TCM.evalExpr expr

/-- Elaborate a tuple expression in type position as a nested `Pair` chain -/
partial def inferTupleAsSigma (elems : List Soma.Syntax.Expr)
    : TCM Soma.Core.Expr := do
  match elems with
  | [] =>
    pure (.primTy .unit)
  | [e] =>
    elabTypePosition e
  | e :: rest => do
    let fstExpr ← elabTypePosition e
    let sndExpr ← inferTupleAsSigma rest
    let span : Span := match elems with
      | head :: _ => head.span
      | [] => Span.uninhabited
    let pairTypeInfo ← requireUniqueWiredRole .typePair span
    return Soma.Core.Expr.dataTy pairTypeInfo.name.id #[fstExpr, sndExpr]
where
  /-- Elaborate a single tuple element in type position -/
  elabTypePosition (e : Soma.Syntax.Expr) : TCM Soma.Core.Expr := do
    match e with
    | .tuple inner _ => inferTupleAsSigma inner.toList
    | .parens inner _ => elabTypePosition inner
    | _ => checkSyntax e (.vType Level.zero)

/-- Build a Core.Expr row value from a field list and optional tail -/
partial def buildRowExpr
    (fields : Array (Soma.Syntax.QualName × Soma.Syntax.Expr))
    (tail : Option Soma.Syntax.QualName)
    : TCM Soma.Core.Expr := do
  let mut rowExpr : Soma.Core.Expr := ← do
    match tail with
    | some tailName =>
      match ← TCM.lookupLocal tailName.name with
      | some entry =>
        let tyExpr ← quoteTypeAnn entry.type
        pure (.fvar entry.fvarId tyExpr)
      | none =>
        let tailMeta ← TCM.freshMetaVal .vRowSort
        quoteValueToExpr tailMeta
    | none => pure .rowEmpty
  for (labelName, fieldTy) in fields.toList.reverse do
    let labelExpr : Soma.Core.Expr ← do
      match ← TCM.lookupLocal labelName.name with
      | some entry =>
        match entry.type with
        | .vLabelSort =>
          let tyExpr ← quoteTypeAnn entry.type
          pure (.fvar entry.fvarId tyExpr)
        | _ => pure (.labelLit labelName.name)
      | none => pure (.labelLit labelName.name)
    let tyExpr ← inferTypeExpr fieldTy
    rowExpr := .rowExtend labelExpr tyExpr rowExpr
  return rowExpr

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
        let _ ← solveConstraints
        return (resultTy, appExpr)
      else
        -- Explicit param with typeApp — insert implicits first, then apply
        let (fnTy'', fnExpr') ← insertImplicits fnTy fnExpr span
        let (_, _, _, _dom, cod) ← ensurePi fnTy'' span
        let argVal ← elaborateTypeArg typeArg
        let argExpr ← quoteValueToExpr argVal
        let resultTy ← applyClosure cod argVal
        let appExpr := Soma.Core.Expr.app fnExpr' argExpr
        let _ ← solveConstraints
        return (resultTy, appExpr)
    | .vRecord row =>
      -- Polymorphic field access: rec @l
      match typeArg with
      | .label name =>
        let (fieldTy, fieldExpr) ← inferPolymorphicFieldAccess fnExpr row name.name argSpan span
        let _ ← solveConstraints
        return (fieldTy, fieldExpr)
      | _ =>
        -- Not a label — insert implicits and apply
        let (fnTy'', fnExpr') ← insertImplicits fnTy fnExpr span
        let (_, _, _, _dom, cod) ← ensurePi fnTy'' span
        let argVal ← elaborateTypeArg typeArg
        let argExpr ← quoteValueToExpr argVal
        let resultTy ← applyClosure cod argVal
        let appExpr := Soma.Core.Expr.app fnExpr' argExpr
        let _ ← solveConstraints
        return (resultTy, appExpr)
    | _ =>
      let (fnTy'', fnExpr') ← insertImplicits fnTy fnExpr span
      let (_, _, _, _dom, cod) ← ensurePi fnTy'' span
      let argVal ← elaborateTypeArg typeArg
      let argExpr ← quoteValueToExpr argVal
      let resultTy ← applyClosure cod argVal
      let appExpr := Soma.Core.Expr.app fnExpr' argExpr
      let _ ← solveConstraints
      return (resultTy, appExpr)
  | _ =>
    -- Regular value application: insert implicits, then check arg against domain
    let (fnTy'', fnExpr') ← insertImplicits fnTy fnExpr span
    let (qty, _, _, dom, cod) ← ensurePi fnTy'' span
    let checkArg : TCM Soma.Core.Expr := checkSyntax arg dom
    let argExpr ← if qty == .zero then TCM.inErasedContext checkArg else checkArg
    let argVal ← TCM.evalExpr argExpr
    let resultTy ← applyClosure cod argVal
    let _ ← solveConstraints
    let appExpr := Soma.Core.Expr.app fnExpr' argExpr
    return (resultTy, appExpr)

/-- Elaborate `(λ name → body) value` as a let binding -/
partial def inferLetStyle (name : Soma.Syntax.QualName) (body : Soma.Syntax.Expr)
    (value : Soma.Syntax.Expr) (lamSpan : Span)
    : TCM (Value × Soma.Core.Expr) := do
  let (valueTy, valueExpr) ← inferSyntax value
  let report ← solveConstraintsSoft
  report.allowPostponed
  let valueTy ← zonkValue valueTy
  let bindingId ← TCM.freshLocalId name.name
  TCM.recordLocalBindingType name.span valueTy
  withCheckedBinding name.name bindingId valueTy .omega .explicit lamSpan do
    let some entry ← TCM.lookupLocal name.name
      | panic! s!"inferLetStyle: binding '{name.name}' missing immediately after withCheckedBinding"
    let (bodyTy, bodyExpr) ← inferSyntax body
    let domExpr ← quoteValueToExpr valueTy
    let lamExpr := buildLambdas [(entry.fvarId, name.name, domExpr)] bodyExpr
    return (bodyTy, .app lamExpr valueExpr)

/-- Check-mode counterpart to `inferLetStyle` -/
partial def checkLetStyle (name : Soma.Syntax.QualName) (body : Soma.Syntax.Expr)
    (value : Soma.Syntax.Expr) (expected : Value) (lamSpan : Span)
    : TCM Soma.Core.Expr := do
  let (valueTy, valueExpr) ← inferSyntax value
  let report ← solveConstraintsSoft
  report.allowPostponed
  let valueTy ← zonkValue valueTy
  let bindingId ← TCM.freshLocalId name.name
  TCM.recordLocalBindingType name.span valueTy
  withCheckedBinding name.name bindingId valueTy .omega .explicit lamSpan do
    let some entry ← TCM.lookupLocal name.name
      | panic! s!"checkLetStyle: binding '{name.name}' missing immediately after withCheckedBinding"
    let bodyExpr ← checkSyntax body expected
    let domExpr ← quoteValueToExpr valueTy
    let lamExpr := buildLambdas [(entry.fvarId, name.name, domExpr)] bodyExpr
    return .app lamExpr valueExpr

/-- Infer lambda body from Syntax params, building nested Core.Expr lambdas -/
partial def inferSyntaxLamBody
    (params : List (Soma.Syntax.QualName × Option Soma.Syntax.Expr))
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
    (params : List (Soma.Syntax.QualName × Option Soma.Syntax.Expr))
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

/-- Infer a list of Syntax.Exprs with a per-element erased-context flag-/
partial def inferSyntaxListErased
    (es : List (Soma.Syntax.Expr × Bool))
    : TCM (List Value × Array Soma.Core.Expr) := do
  match es with
  | [] => return ([], #[])
  | (e, erased) :: rest => do
    let (ty, expr) ←
      if erased then TCM.inErasedContext (inferSyntax e)
      else inferSyntax e
    let (restTys, restExprs) ← inferSyntaxListErased rest
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

/-- Build a constant motive, one lambda per scrutinee type -/
private partial def buildConstantMotive (scrutTys : List Value) (target : Value) : Value :=
  match scrutTys with
  | [] => target
  | _ :: rest =>
    Value.vLam "_" (Closure.const "_" (buildConstantMotive rest target))

/-- Apply a motive value to a spine of scrutinee/pattern values left to right -/
partial def applyMotiveSpine (motive : Value) (args : Array Value) : TCM Value := do
  let mut m := motive
  for a in args do
    let m' ← force m
    m ← vAppMotive m' a
  force m

/-- Synthesize a motive Value from an expected arm type in check mode -/
partial def synthesizeMotive (scrutVals : Array Value) (scrutTys : List Value)
    (expected : Value) (_span : Span) : TCM (Soma.Core.Expr × Value) := do
  -- Quote at depth 0 so every outer bound variable becomes a sentinel fvar
  let expectedExpr := Soma.Core.quoteExpr ⟨0⟩ expected
  let tyArr := scrutTys.toArray
  let mut body := expectedExpr
  let n := scrutVals.size
  for idx in [:n] do
    -- The Ith scrutinee becomes the i-th utermost lambda, so we must abstract the last one first and wrap our way outward
    let i := n - 1 - idx
    let scrutVal ← force scrutVals[i]!
    let abstracted : Soma.Core.Expr :=
      match scrutVal with
      | .vNeutral _ neu =>
        if neu.isBareHead then
          match neu.head with
          | .hVar bv =>
            body.abstractTyvar bv.level
          | _ =>
            -- Not a bound variable: motive is constant in this arg
            body.shiftUp
        else
          body.shiftUp
      | _ =>
        body.shiftUp
    let tyVal ← if h' : i < tyArr.size then pure tyArr[i] else pure (.vType .zero)
    let tyExpr := Soma.Core.quoteExpr ⟨0⟩ tyVal
    let name :=
      match scrutVal with
      | .vNeutral _ neu =>
        match neu.head with
        | .hVar bv => bv.name
        | _ => s!"s{i}"
      | _ => s!"s{i}"
    body := .lam .explicit name tyExpr abstracted
  let bodyVal ← TCM.evalExpr body
  return (body, bodyVal)

/-- Check each arm of a case expression against `motive @ patternValues` -/
partial def checkSyntaxArms (arms : List Soma.Syntax.MatchArm)
    (scrutTys : List Value) (scrutExprs : Array Soma.Core.Expr) (motive : Value)
    (caseSpan : Span)
    : TCM (Array Soma.Core.Arm) := do
  let ctx ← TCM.getCtx
  let scrutVals ← scrutExprs.mapM TCM.evalExpr
  let mut scruts : List (Value × Quantity × Value) := []
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
    let scrutVal := if h' : i < scrutVals.size then scrutVals[i] else ty
    scruts := scruts ++ [(ty, baseQty, scrutVal)]
    i := i + 1
  let mut results : Array Soma.Core.Arm := #[]
  let mut armUsagesList : Array UsageSnapshot := #[]
  for arm in arms do
    let pats := arm.patterns.toList
    let startLvl := (← TCM.getCtx).level.lvl
    let (corePatterns, patVals, bindings, _endLvl) ←
      convertPatternListWithBindings pats scruts startLvl
    let (bodyExpr, armUsages) ← captureUsages
      (checkArmBodyWithBindings bindings patVals motive arm.body arm.span)
    let abstractedBody := bindings.foldl
      (fun body b => body.abstractFVar b.fvarId) bodyExpr
    results := results.push (Soma.Core.Arm.mk corePatterns abstractedBody)
    armUsagesList := armUsagesList.push armUsages
  let span := match arms.head? with
    | some arm => arm.span
    | none => caseSpan
  let joined ← checkMultiBranchUsages armUsagesList span
  applyUsages joined
  Coverage.checkExhaustiveness results scrutTys span
  return results

/-- Push pattern bindings into the context and check the body against the reduced version -/
partial def checkArmBodyWithBindings
    (bindings : List PatternBinding) (patVals : Array Value) (motive : Value)
    (body : Soma.Syntax.Expr) (span : Span)
    : TCM Soma.Core.Expr := do
  match bindings with
  | [] =>
    let armExpectedTy ← applyMotiveSpine motive patVals
    checkSyntax body armExpectedTy
  | b :: rest =>
    match b.nbeValue? with
    | some nbeVal =>
      withCheckedBindingValue b.name b.fvarId b.type b.qty .explicit span nbeVal do
        checkArmBodyWithBindings rest patVals motive body span
    | none =>
      withCheckedBinding b.name b.fvarId b.type b.qty .explicit span do
        checkArmBodyWithBindings rest patVals motive body span

/-- Infer nested tuple as nested pairs -/
partial def inferSyntaxTuple (elems : List Soma.Syntax.Expr) (span : Span)
    : TCM (Value × Soma.Core.Expr) := do
  match elems with
  | [] => return (.vPrimTy .unit, .tuple #[])
  | [e] => inferSyntax e
  | e :: rest => do
    let (fstTy, fstExpr) ← inferSyntax e
    let (sndTy, sndExpr) ← inferSyntaxTuple rest span
    let pairCtor ← requireUniqueWiredRole .pair span
    let pairTypeInfo ← requireUniqueWiredRole .typePair span
    let lvl ← TCM.currentLevel
    let fstTyExpr := Soma.Core.quoteExpr lvl fstTy
    let sndTyExpr := Soma.Core.quoteExpr lvl sndTy
    let pairTyVal := Value.vDataType pairTypeInfo.name.id [fstTy, sndTy]
    let resultTyExpr := Soma.Core.Expr.dataTy pairTypeInfo.name.id #[fstTyExpr, sndTyExpr]
    let expr := Soma.Core.Expr.construct pairCtor.name pairCtor.ctorTag
                  #[fstExpr, sndExpr] resultTyExpr
    return (pairTyVal, expr)

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
        subtypeUnify inferred' expected'
        let _ ← solveConstraints
        return expr'

    -- If-then-else: check both branches
    | .if_ cond then_ else_ span, _ => do
      let condExpr ← checkSyntax cond (.vPrimTy .bool)
      let (thenExpr, thenUsages) ← captureUsages (checkSyntax then_ expected')
      let (elseExpr, elseUsages) ← captureUsages (checkSyntax else_ expected')
      let joined ← checkBranchUsages thenUsages elseUsages span
      applyUsages joined
      return .if_ condExpr thenExpr elseExpr

    -- Case expression in check mode synthesizes a dependent motive from the expected type by abstracting scrutinee values
    | .case scruts arms caseSpan, _ => do
      -- Per-scrutinee erased-context decision
      checkPropElimSoundness scruts.toList arms.toList (some expected')
      let erasedFlags ← scruts.toList.mapIdxM fun i scrut =>
        scrutineeCanBeErased scrut i arms.toList
      let (scrutTys, scrutsExpr) ←
        inferSyntaxListErased (scruts.toList.zip erasedFlags)
      let scrutVals ← scrutsExpr.mapM TCM.evalExpr
      let (motiveExpr, motive) ← synthesizeMotive scrutVals scrutTys expected' caseSpan
      let armsExpr ← checkSyntaxArms arms.toList scrutTys scrutsExpr motive caseSpan
      return .«case» scrutsExpr motiveExpr armsExpr

    -- Tuple against Pair / Sigma: desugar to nested pair-constructor checks
    | .tuple elems _, .vDataType uid _ => do
      let pairInfo? ← TCM.lookupWiredIn .typePair
      let sigmaInfo? ← TCM.lookupWiredIn .typeSigma
      if pairInfo?.any (·.name.id == uid) || sigmaInfo?.any (·.name.id == uid) then
        checkSyntaxTupleAgainstSigma elems.toList expected'
      else
        let (inferred, expr) ← inferSyntax e
        let (inferred', expr') ← insertImplicits inferred expr e.span
        subtypeUnify inferred' expected'
        let _ ← solveConstraints
        return expr'

    | .tuple elems _, .vType _ => do
      inferTupleAsSigma elems.toList

    -- Application: use expected type to guide implicit solving
    | .app fn arg span, _ => do
      match fn with
      | .lambda #[(name, none)] body lamSpan =>
        checkLetStyle name body arg expected' lamSpan
      | _ =>
        let (fnTy, fnExpr) ← inferSyntax fn
        let (fnTy', fnExpr') ← insertImplicitsWithExpected fnTy fnExpr (some expected') 1 span
        let (resultTy, appExpr) ← inferSyntaxApp fnTy' fnExpr' arg span
        let _ ← solveConstraints
        subtypeUnify resultTy expected'
        return appExpr

    | .composeBlock stmts final_ _, _ =>
      checkSyntax (desugarCompose stmts final_) expected'

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
        subtypeUnify inferred' expected'
        let _ ← solveConstraints
        return expr'

    -- Default: infer against expected
    | _, _ => do
      let (inferred, expr) ← inferSyntax e
      let (inferred', expr') ← insertImplicits inferred expr e.span
      subtypeUnify inferred' expected'
      let _ ← solveConstraints
      return expr'

/-- Check tuple elements against an expected pair type -/
partial def checkSyntaxTupleAgainstSigma (elems : List Soma.Syntax.Expr) (sigmaTy : Value)
    : TCM Soma.Core.Expr := do
  match elems with
  | [] => do
    let (_, expr) ← inferSyntax (.tuple #[] Span.uninhabited)
    return expr
  | [e] => checkSyntax e sigmaTy
  | e :: rest => do
    let sigmaTy' ← force sigmaTy
    let pairTypeInfo? ← TCM.lookupWiredIn .typePair
    let sigmaTypeInfo? ← TCM.lookupWiredIn .typeSigma
    let decomposed? : Option (Value × Value × Bool) ← do
      match sigmaTy' with
      | .vDataType uid args =>
        if pairTypeInfo?.any (·.name.id == uid) then
          match args with
          | [fstTy, sndTy] => pure (some (fstTy, sndTy, false))
          | _ => pure none
        else if sigmaTypeInfo?.any (·.name.id == uid) then
          match args with
          | [fstTy, sndFun] => pure (some (fstTy, sndFun, true))
          | _ => pure none
        else pure none
      | _ => pure none
    match decomposed? with
    | some (fstTy, sndRepr, isDependent) =>
      let fstExpr ← checkSyntax e fstTy
      let fstVal ← TCM.evalExpr fstExpr
      let sndTy ← if isDependent then
                    applyValueArgs sndRepr #[fstVal]
                  else
                    pure sndRepr
      let sndExpr ← checkSyntaxTupleAgainstSigma rest sndTy
      let pairCtor ← requireUniqueWiredRole .pair e.span
      let pairTypeInfo ← requireUniqueWiredRole .typePair e.span
      let lvl ← TCM.currentLevel
      let fstTyExpr := Soma.Core.quoteExpr lvl fstTy
      let sndTyExpr := Soma.Core.quoteExpr lvl sndTy
      let resultTyExpr := Soma.Core.Expr.dataTy pairTypeInfo.name.id #[fstTyExpr, sndTyExpr]
      return Soma.Core.Expr.construct pairCtor.name pairCtor.ctorTag
                #[fstExpr, sndExpr] resultTyExpr
    | none =>
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
