import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Quote
import Soma.Core.Eval
import Soma.Core.Primitive
import Soma.Core.TypeId
import Soma.Dependent.Prelude
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Unify
import Soma.Dependent.Error
import Soma.Dependent.Usage
import Soma.Dependent.Elaborate
import Soma.Metal.Expr
import Soma.Unique

namespace Soma.Dependent

open Soma (Unique)
open Soma.Core
open Soma.Metal (Expr ExprList Name BinderInfo HoleId Scope ScopedVar)
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
def ensureType (v : Value) (span : Span) : TCM Level := do
  let v' ← force v
  match v' with
  | .vType l => return l
  | .vNeutral (.vType l) _ => return l
  | _ =>
    TCM.throw (.expectedType v' span)

/-- Ensure a value is a Pi type -/
def ensurePi (v : Value) (span : Span) : TCM (Quantity × BinderInfo × String × Value × Closure) := do
  let v' ← force v
  match v' with
  | .vPi qty binder name dom cod => return (qty, binder, name, dom, cod)
  | _ => TCM.throw (.expectedFunction v' span)

/-- Ensure a value is a Sigma type -/
def ensureSigma (v : Value) (span : Span) : TCM (Quantity × String × Value × Closure) := do
  let v' ← force v
  match v' with
  | .vSigma qty name fst snd => return (qty, name, fst, snd)
  | _ => TCM.throw (.expectedSigma v' span)

/-- Apply a motive value to an argument.
    Used for transport where we have P : A -> Type and want P x. -/
def vAppMotive (motive : Value) (arg : Value) : TCM Value := do
  match motive with
  | .vLam _ _ _ _ body =>
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
  | .vDataType typeId args =>
    -- Convert TypeId to Unique for class resolution
    let classId : Unique := {
      id := typeId.unique
      module := typeId.module
      original := typeId.name
    }
    return (classId, args.toArray)
  | _ => none

/-- Insert implicit arguments for a function type, tracking created metavariables -/
partial def insertImplicitsCore (fnTy : Value) (fnExpr : Expr Value scope) (span : Span)
    : TCM (Value × Expr Value scope × Array (MetaId × Value × String)) := do
  let fnTy' ← force fnTy
  match fnTy' with
  | .vPi qty binder name dom cod =>
    if binder.isImplicit then
      -- Create metavariable for this implicit parameter
      let metaId ← TCM.freshMeta dom
      let argMeta := Value.vNeutral dom (.nMeta metaId)

      -- Handle instance parameters specially
      if binder == .instance_ then
        match extractClassInfo (← force dom) with
        | some (classId, args) =>
          TCM.addPendingInstance classId args metaId span
        | none => pure ()

      -- Apply the function to the metavariable
      let resultTy ← applyClosure cod argMeta
      let argExpr : Expr Value scope := .mvar metaId.id argMeta span
      let appExpr := Expr.call fnExpr (.cons argExpr .nil) resultTy span

      -- Recursively insert more implicits, accumulating metas
      let (finalTy, finalExpr, restMetas) ← insertImplicitsCore resultTy appExpr span
      return (finalTy, finalExpr, #[(metaId, dom, name)] ++ restMetas)
    else
      -- Explicit argument: stop inserting implicits
      return (fnTy', fnExpr, #[])
  | _ => return (fnTy', fnExpr, #[])

/-- Naive insert implicit arguments (TODO: remove legacy) -/
partial def insertImplicits (fnTy : Value) (fnExpr : Expr Value scope) (span : Span)
    : TCM (Value × Expr Value scope) := do
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
partial def insertImplicitsWithExpected (fnTy : Value) (fnExpr : Expr Value scope)
    (expected : Option Value) (numExplicitArgs : Nat) (span : Span)
    : TCM (Value × Expr Value scope) := do
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

/-- Extract bindings with names from a pattern list -/
def patternListBindingsWithNames : Soma.Metal.PatternList α → List (Soma.Metal.BindingId × String)
  | .nil => []
  | .cons p ps => p.bindingsWithNames.toList ++ patternListBindingsWithNames ps

/-- Get a short description of an expression for debug output -/
def exprKind : Expr α scope → String
  | .var v _ _ => s!"var({v.original})"
  | .lit l _ => s!"lit({l})"
  | .type _ _ => "Type"
  | .pi _ _ name _ _ _ => s!"Π({name})"
  | .sigma _ name _ _ _ => s!"Σ({name})"
  | .lam params _ _ _ => s!"λ({params.length} params)"
  | .call _ args _ _ => s!"call({args.length} args)"
  | .let_ _ name _ _ _ _ => s!"let({name})"
  | .pair _ _ _ _ => "pair"
  | .fst _ _ _ => "fst"
  | .snd _ _ _ => "snd"
  | .primTy p _ => s!"primTy({p.name})"
  | .higherPrimTy p _ => s!"higherPrimTy({p.name})"
  | .dataTy id _ _ => s!"dataTy({id.name})"
  | .ann _ _ _ _ => "ann"
  | .hole _ _ => "hole"
  | .mvar id _ _ => s!"mvar({id})"
  | .eq _ _ _ _ _ => "eq"
  | .refl _ _ _ => "refl"
  | .transport _ _ _ _ _ _ _ _ => "transport"
  | .global name _ _ => s!"global({name.display})"
  | .record _ _ _ => "record"
  | .tuple _ _ _ => "tuple"
  | .construct name _ _ _ _ => s!"construct({name.display})"
  | .fieldAccess _ name _ _ _ => s!"fieldAccess({name})"
  | .if_ _ _ _ _ _ => "if"
  | .case _ _ _ _ => "case"
  | .inject label _ _ _ => s!"inject({label})"
  | .array _ _ _ => "array"
  | .recordUpdate _ _ _ _ => "recordUpdate"
  | .closure name _ _ _ => s!"closure({name})"
  | .panic _ _ _ => "panic"
  | .proj _ name _ _ _ => s!"proj({name})"
  | .typeApp _ _ _ => "typeApp"
  | .rowEmpty _ => "rowEmpty"
  | .rowExtend _ _ _ _ => "rowExtend"
  | .recordTy _ _ => "recordTy"
  | .variantTy _ _ => "variantTy"
  | .labelLit name _ => s!"label({name})"

mutual

/-- Extend the typing context with bindings for all parameters in a ParamList.
    This processes params left-to-right, creating fresh metavariables for each param's type
    and extending the context. The continuation is run under the fully extended context. -/
partial def withAllParamBindings (params : Soma.Metal.ParamList Unit) (span : Span)
    (cont : TCM α) : TCM α := do
  match params with
  | .nil => cont
  | .cons _binding name () rest =>
    -- Create metavariable for this parameter's type
    let paramTy ← TCM.freshMetaVal (.vType .zero)
    -- Extend context with this binding, then process remaining params
    TCM.withBinding name paramTy .omega .explicit span do
      withAllParamBindings rest span cont

/-- Extend the typing context with bindings for parameters, extracting types from a nested Pi.
    This peels off one Pi layer per parameter, using the domain type for each binding.
    Returns the final codomain type (after all Pis are peeled) for checking the body. -/
partial def withParamBindingsFromPi (params : List (Soma.Metal.BindingId × String × Unit))
    (expectedTy : Value) (span : Span) (cont : Value → TCM α) : TCM α := do
  match params with
  | [] => cont expectedTy
  | (_, paramName, ()) :: rest =>
    let expectedTy' ← force expectedTy
    match expectedTy' with
    | .vPi qty binder _ dom cod =>
      -- Get the codomain by applying closure to fresh variable at current level
      let codTy ← do
        let lvl ← TCM.currentLevel
        let x := Value.vNeutral dom (.nVar ⟨paramName, lvl⟩)
        applyClosure cod x
      -- Extend context with this parameter and continue with remaining params
      withCheckedBinding paramName dom qty binder span do
        withParamBindingsFromPi rest codTy span cont
    | _ =>
      -- Expected type is not a Pi but we still have params - create metavariable
      -- This handles cases where the expected type is a metavariable
      let paramTy ← TCM.freshMetaVal (.vType .zero)
      TCM.withBinding paramName paramTy .omega .explicit span do
        withParamBindingsFromPi rest expectedTy' span cont

/-- Infer the body of a lambda, extending the context with parameter bindings.
    We first extend the context for ALL params, then infer the body.
    This avoids scope type transformations since infer is polymorphic in scope. -/
partial def inferLamBody {scope : Scope} (params : Soma.Metal.ParamList Unit)
    (body : Expr Unit (params.bindingIds ++ scope)) (span : Span)
    : TCM (Value × Expr Value (params.bindingIds ++ scope)) := do
  -- Extend context for all params, then infer body under that context
  withAllParamBindings params span (infer body)

/-- Infer the type of an expression and return it + elaborated -/
partial def infer {scope : Scope} (e : Expr Unit scope) : TCM (Value × Expr Value scope) := do
  let kind := exprKind e
  TCM.debugEnter "infer" kind
  let result ← TCM.withDebugIndent do
    TCM.withSpan e.span do
      inferCore e
  TCM.debugLeave "infer" (toString result.1)
  return result
where
  inferCore {scope : Scope} (e : Expr Unit scope) : TCM (Value × Expr Value scope) := do
    match e with
    -- Variables: look up in context and record usage
    | .var v () span =>
      match ← TCM.lookupLocal v.original with
      | some entry =>
        -- Record variable usage with QTT checking
        useVarChecked v.original span
        return (entry.type, .var v entry.type span)
      | none =>
        -- Check if it's a primitive type name used as a value (todo: review)
        match v.original with
        | "Int" => return (.vType .zero, .primTy .int span)
        | "Long" => return (.vType .zero, .primTy .long span)
        | "Short" => return (.vType .zero, .primTy .short span)
        | "Byte" => return (.vType .zero, .primTy .byte span)
        | "Bool" => return (.vType .zero, .primTy .bool span)
        | "String" => return (.vType .zero, .primTy .string span)
        | "Float" => return (.vType .zero, .primTy .float span)
        | "Double" => return (.vType .zero, .primTy .double span)
        | "Unit" => return (.vType .zero, .primTy .unit span)
        | "Type" => return (.vType .one, .type .zero span)
        | _ => TCM.throw (.unboundVariable v.original span)

    -- Literals
    | .lit (.int n) span =>
      return (.vPrimTy .int, .lit (.int n) span)

    | .lit (.string s) span =>
      return (.vPrimTy .string, .lit (.string s) span)

    | .lit (.bool b) span =>
      return (.vPrimTy .bool, .lit (.bool b) span)

    -- Type universes: Type_i : Type_(i+1)
    | .type level span =>
      let resultLevel := Level.mkSucc level
      return (.vType resultLevel, .type level span)

    -- Pi types: check domain and codomain are types
    | .pi qty binder name domain codomain span => do
      -- Check domain is a type (in erased context since types are erased)
      let (domTy, domExpr) ← TCM.inErasedContext do
        infer domain
      let domLevel ← ensureType domTy domain.span
      -- Evaluate domain for the context
      let domVal ← TCM.evalTyped domExpr

      -- Check codomain is a type, under extended context (also in erased context)
      let (codTy, codExpr) ← TCM.inErasedContext do
        TCM.withBinding name domVal qty binder span do
          infer codomain
      let codLevel ← ensureType codTy codomain.span

      -- Pi type has type Type (max i j)
      let resultLevel := Level.mkMax domLevel codLevel
      return (.vType resultLevel, .pi qty binder name domExpr codExpr span)

    -- Sigma types
    | .sigma qty name fst snd span => do
      -- Check first component is a type (in erased context)
      let (fstTy, fstExpr) ← TCM.inErasedContext do
        infer fst
      let fstLevel ← ensureType fstTy fst.span
      let fstVal ← TCM.evalTyped fstExpr

      -- Check second component is a type (in erased context)
      let (sndTy, sndExpr) ← TCM.inErasedContext do
        TCM.withBinding name fstVal qty .explicit span do
          infer snd
      let sndLevel ← ensureType sndTy snd.span

      let resultLevel := Level.mkMax fstLevel sndLevel
      return (.vType resultLevel, .sigma qty name fstExpr sndExpr span)

    -- Lambda: cannot infer without annotation, create metavariables
    | .lam params body () span => do
      -- Lambda inference: create metavariables for parameter types and infer body
      -- The body has type Expr Unit (params.bindingIds ++ scope)
      -- We need to infer its type under the extended scope
      let (bodyTy, bodyExpr) ← inferLamBody params body span
      -- Create the pi type from the result
      match params with
      | .nil =>
        -- No parameters - body type is the result type
        -- params.bindingIds = [] so [] ++ scope = scope definitionally
        return (bodyTy, .lam (.nil) bodyExpr bodyTy span)
      | .cons binding paramName () rest =>
        -- Create a closure for the codomain
        let domMeta ← TCM.freshMetaVal (.vType .zero)
        -- Convert the body expression to a Term for storage in the closure
        let bodyTerm := exprToTerm bodyExpr
        let codClosure ← TCM.mkClosureWithTerm paramName bodyTerm
        let piTy := Value.vPi .omega .explicit paramName domMeta codClosure
        let typedParams : Soma.Metal.ParamList Value := .cons binding paramName piTy (rest.mapInfo (fun () => piTy))
        let h : typedParams.bindingIds ++ scope = (Soma.Metal.ParamList.cons binding paramName () rest).bindingIds ++ scope := by
          unfold typedParams
          simp only [Soma.Metal.ParamList.bindingIds, Soma.Metal.ParamList.mapInfo_bindingIds]
        return (piTy, .lam typedParams (h ▸ bodyExpr) piTy span)

    -- Application
    | .call fn args () span => do
      let (fnTy, fnExpr) ← infer fn
      inferApp fnTy fnExpr args span

    -- Let binding
    | .let_ binding original value body () span => do
      let (valTy, valExpr) ← infer value
      -- We use the value's type for the binding, with unrestricted quantity
      let (bodyTy, bodyExpr) ← TCM.withBinding original valTy .omega .explicit span do
        infer body
      return (bodyTy, .let_ binding original valExpr bodyExpr bodyTy span)

    -- Pairs: can sometimes infer, but usually need annotation
    | .pair fst snd () span => do
      let (fstTy, fstExpr) ← infer fst
      let (sndTy, sndExpr) ← infer snd
      -- For inference, create a non-dependent sigma (constant second component)
      let clos ← TCM.mkEmptyClosure "_"
      let sigmaTy := Value.vSigma .omega "_" fstTy clos
      return (sigmaTy, .pair fstExpr sndExpr sigmaTy span)

    -- First projection
    | .fst e () span => do
      let (eTy, eExpr) ← infer e
      let (_, _, fstTy, _) ← ensureSigma eTy e.span
      return (fstTy, .fst eExpr fstTy span)

    -- Second projection
    | .snd e () span => do
      let (eTy, eExpr) ← infer e
      let (_, _, fstTy, sndClos) ← ensureSigma eTy e.span
      -- Apply closure to first projection to get second type
      let eVal ← TCM.evalTyped eExpr
      let fstVal := Value.vNeutral fstTy (.nFst (.nVar ⟨"_", ⟨0⟩⟩))
      let sndTy ← applyClosure sndClos fstVal
      return (sndTy, .snd eExpr sndTy span)

    -- Primitive types
    | .primTy p span =>
      return (.vType .zero, .primTy p span)

    | .higherPrimTy p span =>
      -- Higher-kinded primitives have kind * -> *
      -- The codomain is constant (Type), so use empty closure
      let clos ← TCM.mkEmptyClosure "_"
      let kindTy := Value.vPi .omega .explicit "_" (.vType .zero) clos
      return (kindTy, .higherPrimTy p span)

    -- Row types
    | .rowEmpty span =>
      -- Empty row has type Row (which is Type for now)
      return (.vType .zero, .rowEmpty span)

    | .rowExtend label fieldTy tail span => do
      let (_, labelExpr) ← infer label
      let (_, fieldTyExpr) ← infer fieldTy
      let (_, tailExpr) ← infer tail
      return (.vType .zero, .rowExtend labelExpr fieldTyExpr tailExpr span)

    | .recordTy row span => do
      let (_, rowExpr) ← infer row
      return (.vType .zero, .recordTy rowExpr span)

    | .variantTy row span => do
      let (_, rowExpr) ← infer row
      return (.vType .zero, .variantTy rowExpr span)

    | .labelLit name span =>
      -- Label literals have type Label (which is Type for now)
      return (.vType .zero, .labelLit name span)

    -- Data types
    | .dataTy id params span => do
      let (_, paramsExpr) ← inferExprList params
      return (.vType .zero, .dataTy id paramsExpr span)

    -- Type annotation: check against the annotation
    | .ann expr ty () span => do
      -- The type itself is in erased context
      let (_, tyExpr) ← TCM.inErasedContext do
        infer ty
      let tyVal ← TCM.evalTyped tyExpr
      -- But the expression is checked in current context
      let checkedExpr ← check expr tyVal
      return (tyVal, .ann checkedExpr tyExpr tyVal span)

    -- Holes: create a metavariable
    | .hole id span => do
      let holeTy ← TCM.freshMetaVal (.vType .zero)
      let _ ← TCM.freshMetaVal holeTy
      return (holeTy, .hole id span)

    -- Metavariables: look up
    | .mvar id () span => do
      let info? ← TCM.lookupMeta ⟨id⟩
      match info? with
      | some info => return (info.type, .mvar id info.type span)
      | none =>
        -- Unknown meta, create a fresh one
        let metaTy ← TCM.freshMetaVal (.vType .zero)
        return (metaTy, .mvar id metaTy span)

    -- Equality type
    | .eq tyLevel ty lhs rhs span => do
      -- The type argument is in erased context
      let (_, tyExpr) ← TCM.inErasedContext do
        infer ty
      let tyVal ← TCM.evalTyped tyExpr
      -- lhs and rhs are also in erased context (equality is a type former)
      let lhsExpr ← TCM.inErasedContext do
        check lhs tyVal
      let rhsExpr ← TCM.inErasedContext do
        check rhs tyVal
      return (.vType tyLevel, .eq tyLevel tyExpr lhsExpr rhsExpr span)

    -- Refl: infer the type from x
    | .refl ty x span => do
      -- The type argument is in erased context
      let (_, tyExpr) ← TCM.inErasedContext do
        infer ty
      let tyVal ← TCM.evalTyped tyExpr
      -- x is also in erased context (refl is a proof constructor)
      let (_, xExpr) ← TCM.inErasedContext do
        infer x
      let xVal ← TCM.evalTyped xExpr
      let eqTy := Value.vEq .zero tyVal xVal xVal
      return (eqTy, .refl tyExpr xExpr span)

    -- Transport: transport P eq px : P rhs
    -- Given P : ty -> Type, eq : lhs = rhs, body : P lhs
    -- Returns P rhs
    | .transport tyLevel ty motive lhs rhs eq body span => do
      -- All arguments are in erased context (transport is a proof eliminator)
      let (_, tyExpr) ← TCM.inErasedContext do
        infer ty
      let tyVal ← TCM.evalTyped tyExpr

      -- Check the motive: P : ty -> Type
      let (_, motiveExpr) ← TCM.inErasedContext do
        infer motive
      let motiveVal ← TCM.evalTyped motiveExpr

      -- Check lhs and rhs have type ty
      let lhsExpr ← TCM.inErasedContext do
        check lhs tyVal
      let lhsVal ← TCM.evalTyped lhsExpr
      let rhsExpr ← TCM.inErasedContext do
        check rhs tyVal
      let rhsVal ← TCM.evalTyped rhsExpr

      -- Check eq : lhs = rhs
      let eqTy := Value.vEq tyLevel tyVal lhsVal rhsVal
      let eqExpr ← TCM.inErasedContext do
        check eq eqTy

      -- Apply motive to lhs to get the expected type of body
      let pLhs ← vAppMotive motiveVal lhsVal
      -- Check body : P lhs
      let bodyExpr ← TCM.inErasedContext do
        check body pLhs

      -- The result type is P rhs
      let pRhs ← vAppMotive motiveVal rhsVal
      return (pRhs, .transport tyLevel tyExpr motiveExpr lhsExpr rhsExpr eqExpr bodyExpr span)

    -- Global references
    | .global name () span => do
      match ← TCM.lookupGlobal name.display with
      | some info =>
        if info.isConstructor then
          -- For constructors, instantiate implicit type parameters with fresh metas
          -- This is needed because constructors like `Nil : forall {n} {a}. Vec Zero a`
          -- need their implicits filled in even when used standalone (not in application)
          let instantiatedTy ← instantiateImplicits info.type span
          return (instantiatedTy, .global name instantiatedTy span)
        else
          -- For non-constructors, return the type directly
          -- Implicits will be inserted when used in application position
          return (info.type, .global name info.type span)
      | none => TCM.throw (.unboundGlobal name.display span)

    -- Records
    | .record fields () span => do
      let (rowTy, fieldsExpr) ← inferRecordFields fields
      let recTy := Value.vRecord rowTy
      return (recTy, .record fieldsExpr recTy span)

    -- Tuples (as pairs)
    | .tuple elems () span => do
      let (tys, elemsExpr) ← inferExprList elems
      -- Build a proper nested Sigma type for tuples
      let tupleTy ← match tys with
        | [] => pure (Value.vPrimTy .unit)
        | [t] => pure t
        | _ =>
          -- Build nested Sigma: (A, B, C) -> Σ(_ : A). Σ(_ : B). C
          tys.foldrM (init := Value.vPrimTy .unit) fun elemTy acc => do
            match acc with
            | .vPrimTy .unit => pure elemTy  -- Last element, no sigma wrapping
            | _ =>
              let sndClosure ← TCM.mkEmptyClosure "_"
              -- Create a Sigma type where the second component is the accumulator
              pure (Value.vSigma .omega "_" elemTy sndClosure)
      return (tupleTy, .tuple elemsExpr tupleTy span)

    -- Constructors
    | .construct name tag args () span => do
      -- Try to look up the constructor's type from globals for proper index inference
      match ← TCM.lookupGlobal name.display with
      | some ctorInfo =>
        -- Use its declared type for index inference
        let (resultTy, argsExpr) ← inferConstructorApp ctorInfo.type args span
        return (resultTy, .construct name tag argsExpr resultTy span)
      | none =>
        -- Fallback: constructor not in globals, use simple inference
        let (argTys, argsExpr) ← inferExprList args
        let resultTy := Value.vConstructor name tag argTys
        return (resultTy, .construct name tag argsExpr resultTy span)

    -- Field access
    | .fieldAccess expr fieldName fieldIdx () span => do
      let (exprTy, exprE) ← infer expr
      let fieldTy ← lookupFieldType exprTy fieldName span
      return (fieldTy, .fieldAccess exprE fieldName fieldIdx fieldTy span)

    -- If-then-else
    | .if_ cond then_ else_ () span => do
      let condExpr ← check cond (.vPrimTy .bool)
      let (thenTy, thenExpr) ← infer then_
      let elseExpr ← check else_ thenTy
      return (thenTy, .if_ condExpr thenExpr elseExpr thenTy span)

    -- Case expressions
    | .case scruts arms () span => do
      let (scrutTys, scrutsExpr) ← inferExprList scruts
      -- Create a metavariable for the result type
      let resultTy ← TCM.freshMetaVal (.vType .zero)
      -- Pass scrutinee types to inferArms so pattern bindings get proper types
      let armsExpr ← inferArms arms scrutTys resultTy
      return (resultTy, .case scrutsExpr armsExpr resultTy span)

    -- Variant injection
    | .inject label args () span => do
      let (argTys, argsExpr) ← inferExprList args
      let argTy := match argTys with
        | [t] => t
        | _ => Value.vRecordVal [] -- Unit for nullary
      let rowTail ← TCM.freshMetaVal (.vType .zero)
      let row := Value.vRowExtend (.vLabelLit label) argTy rowTail
      let variantTy := Value.vVariant row
      return (variantTy, .inject label argsExpr variantTy span)

    -- Array/List literals: infer as List type (not Array)
    | .array elems () span => do
      -- Create a fresh metavariable for element type
      let elemTy ← TCM.freshMetaVal (.vType .zero)
      -- Check each element against the element type (this unifies element types)
      let elemsChecked ← checkExprList elems.toList elemTy
      -- Build List type with stable builtin TypeId
      let listId := Soma.Core.TypeId.builtin "List" Soma.Core.HigherPrimitive.list.uniqueId
      let listTy := Value.vDataType listId [elemTy]
      return (listTy, .array (Soma.Metal.ExprList.fromList elemsChecked) listTy span)

    | .recordUpdate base updates () span => do
      let (baseTy, baseExpr) ← infer base
      let (_, updatesExpr) ← inferRecordFields updates
      return (baseTy, .recordUpdate baseExpr updatesExpr baseTy span)

    | .closure name caps () span => do
      let (_, capsExpr) ← inferCaptures caps
      let closTy ← TCM.freshMetaVal (.vType .zero)
      return (closTy, .closure name capsExpr closTy span)

    | .panic msg () span => do
      let resultTy ← TCM.freshMetaVal (.vType .zero)
      return (resultTy, .panic msg resultTy span)

    | .proj typeName fieldName fieldIdx () span => do
      let fieldTy ← TCM.freshMetaVal (.vType .zero)
      return (fieldTy, .proj typeName fieldName fieldIdx fieldTy span)

    | .typeApp arg () span => do
      let resultTy ← TCM.freshMetaVal (.vType .zero)
      return (resultTy, .typeApp arg resultTy span)

/-- Check a list of expressions against an expected element type -/
partial def checkExprList {scope : Scope} (exprs : List (Expr Unit scope)) (elemTy : Value)
    : TCM (List (Expr Value scope)) := do
  match exprs with
  | [] => return []
  | e :: es =>
    let e' ← check e elemTy
    let es' ← checkExprList es elemTy
    return e' :: es'

/-- Check an expression against an expected type -/
partial def check {scope : Scope} (e : Expr Unit scope) (expected : Value)
    : TCM (Expr Value scope) := do
  let kind := exprKind e
  TCM.debugEnter "check" s!"{kind} ⇐ {expected}"
  let result ← TCM.withDebugIndent do
    TCM.withSpan e.span do
      checkCore e expected
  TCM.debugLeave "check" "ok"
  return result
where
  checkCore {scope : Scope} (e : Expr Unit scope) (expected : Value)
      : TCM (Expr Value scope) := do
    -- Force expected type to resolve metavariables
    let expected' ← force expected

    match e, expected' with
    -- Lambda against Pi type: check body under extended context
    -- Handle multi-parameter lambdas by peeling off one Pi per parameter
    | .lam params body () span, .vPi _ _ _ _ _ => do
      let paramList := params.toList
      match paramList with
      | [] =>
        -- No params, shouldn't happen but handle it by inferring body and wrapping
        let (_, bodyExpr) ← infer body
        let typedParams := params.mapInfo (fun () => expected')
        let h : typedParams.bindingIds ++ scope = params.bindingIds ++ scope := by
          rw [Soma.Metal.ParamList.mapInfo_bindingIds]
        return .lam typedParams (h ▸ bodyExpr) expected' span
      | _ =>
        -- Use withParamBindingsFromPi to peel off all Pi layers and extend context
        let bodyExpr ← withParamBindingsFromPi paramList expected' span fun finalCodTy => do
          check body finalCodTy
        let typedParams := params.mapInfo (fun () => expected')
        -- Use the theorem that mapInfo preserves bindingIds
        let h : typedParams.bindingIds ++ scope = params.bindingIds ++ scope := by
          rw [Soma.Metal.ParamList.mapInfo_bindingIds]
        return .lam typedParams (h ▸ bodyExpr) expected' span

    -- Pair against Sigma type
    | .pair fst snd () span, .vSigma qty name fstTy sndClos => do
      let fstExpr ← check fst fstTy
      -- For the second component, apply closure to the first type (not value)
      let fstTy' ← force fstTy
      let sndTy ← applyClosure sndClos fstTy'
      let sndExpr ← check snd sndTy
      return .pair fstExpr sndExpr expected' span

    -- Let: infer value, check body
    | .let_ binding original value body () span, _ => do
      let (valTy, valExpr) ← infer value
      let bodyExpr ← TCM.withBinding original valTy .omega .explicit span do
        check body expected'
      return .let_ binding original valExpr bodyExpr expected' span

    -- If-then-else: check both branches against expected
    | .if_ cond then_ else_ () span, _ => do
      let condExpr ← check cond (.vPrimTy .bool)
      let thenExpr ← check then_ expected'
      let elseExpr ← check else_ expected'
      return .if_ condExpr thenExpr elseExpr expected' span

    -- Hole: register with expected type
    | .hole id span, _ => do
      -- Create a metavariable with the expected type
      let _ ← TCM.freshMeta expected'
      return .hole id span

    -- Function application: use expected type to guide implicit solving
    | .call fn args () span, _ => do
      -- Count explicit arguments for expected type propagation
      let numExplicitArgs := args.length
      -- Infer function type
      let (fnTy, fnExpr) ← infer fn
      -- Use expected type to solve implicits BEFORE processing arguments
      -- This is the key bidirectional propagation improvement
      let (fnTy', fnExpr') ← insertImplicitsWithExpected fnTy fnExpr (some expected') numExplicitArgs span
      -- Now infer the application with the (possibly improved) function type
      let (resultTy, appExpr) ← inferApp fnTy' fnExpr' args span
      -- After processing arguments, try greedy solving
      solveImplicitsGreedy
      -- Unify result with expected type (may solve more implicits)
      unify resultTy expected'
      return appExpr

    -- Array literal against List type: treat [] as List, not Array
    | .array elems () span, .vDataType typeId (elemTy :: _) => do
      -- Check if the expected type is List (using stable builtin TypeId)
      let listId := Soma.Core.TypeId.builtin "List" Soma.Core.HigherPrimitive.list.uniqueId
      if typeId == listId then
        -- Check each element against the expected element type
        let elemsChecked ← checkExprList elems.toList elemTy
        -- Return array with List type annotation
        return .array (Soma.Metal.ExprList.fromList elemsChecked) expected' span
      else
        -- Not a List, fall through to default
        let (inferred, expr) ← infer e
        let (inferred', expr') ← insertImplicits inferred expr e.span
        unify inferred' expected'
        solveImplicitsGreedy
        return expr'

    -- Default: infer and unify with expected type
    | _, _ => do
      let (inferred, expr) ← infer e
      -- If the inferred type has implicit arguments and the expected type doesn't,
      -- we need to instantiate the implicit arguments before unifying
      let (inferred', expr') ← insertImplicits inferred expr e.span
      -- Use unify to solve metavariables
      unify inferred' expected'
      -- After unification, try greedy solving to resolve any pending constraints
      solveImplicitsGreedy
      return expr'

/-- Elaborate a type argument (from explicit type application syntax like `f @T`) -/
partial def elaborateTypeArg (typeArg : Soma.Metal.TypeArg) : TCM Value := do
  match typeArg with
  | .label labelName =>
    -- Check if it's a bound variable or literal
    match ← TCM.lookupLocal labelName with
    | some entry =>
      -- Return neutral reference
      pure (Value.vNeutral entry.type (Neutral.nVar ⟨labelName, entry.level⟩))
    | none =>
      pure (Value.vLabelLit labelName)
  | .type tyExpr =>
    -- Elaborate the type expression
    Elaborate.elaborateType Elaborate.ElabEnv.empty tyExpr

/--
  Handle explicit type application: `f @T` where `f` has an implicit parameter.

  Given a function with type `∀ {a : K}. B a` and an explicit type argument `T`,
  elaborate `T` at kind `K` and return the instantiated type `B T`.
-/
partial def inferExplicitTypeApp {scope : Scope}
    (fnExpr : Expr Value scope) (cod : Closure)
    (typeArg : Soma.Metal.TypeArg) (argSpan : Span) (callSpan : Span)
    : TCM (Value × Expr Value scope) := do
  -- Elaborate the type argument
  let argVal ← elaborateTypeArg typeArg
  -- Apply the function type's codomain closure to get result type
  let resultTy ← applyClosure cod argVal
  -- Create the elaborated type application expression
  let argExpr : Expr Value scope := .typeApp typeArg resultTy argSpan
  let appExpr := Expr.call fnExpr (.cons argExpr .nil) resultTy callSpan
  return (resultTy, appExpr)

/--
  Handle polymorphic field access: `rec @l` where `rec` has a record type.

  Given a record with type `{ l : A | r }` and a label `l` (which may be a
  bound label variable or a literal), find the field type `A`.
-/
partial def inferPolymorphicFieldAccess {scope : Scope}
    (recExpr : Expr Value scope) (row : Value)
    (labelName : String) (argSpan : Span) (callSpan : Span)
    : TCM (Value × Expr Value scope) := do
  -- Resolve the label which may be a bound variable or literal
  let labelVal ← match ← TCM.lookupLocal labelName with
    | some entry =>
      pure (Value.vNeutral entry.type (Neutral.nVar ⟨labelName, entry.level⟩))
    | none =>
      pure (Value.vLabelLit labelName)
  -- Find the field type by unifying with row labels
  let fieldTy ← findFieldInRowByLabelVal row labelVal argSpan
  -- Create field access expression
  let fieldExpr := Expr.fieldAccess recExpr labelName 0 fieldTy callSpan
  return (fieldTy, fieldExpr)

/--
  Instantiate all leading implicit parameters in a type with fresh metavariables.
  This is used when a constructor is referenced without explicit application,

  Returns the instantiated type with all leading implicits filled in.
-/
partial def instantiateImplicits (ty : Value) (span : Span) : TCM Value := do
  let ty' ← force ty
  match ty' with
  | .vPi _qty binder _name dom cod =>
    if binder.isImplicit then
      -- Create metavariable for implicit parameter
      let metaVal ← TCM.freshMetaVal dom
      let resultTy ← applyClosure cod metaVal
      -- Continue instantiating more implicits
      instantiateImplicits resultTy span
    else
      -- Hit an explicit parameter, stop instantiating
      return ty'
  | _ =>
    -- Not a Pi type, return as-is
    return ty'

/--
  Infer constructor application with proper index constraint generation.

  For indexed type families like `Vec n a`, when we see a constructor like `Cons`:
  1. Look up the constructor's declared type: `forall {a}. a -> Vec n a -> Vec (n+1) a`
  2. Insert metavariables for implicit type parameters (creating index metas)
  3. Check each argument against the expected domain type
  4. Return the fully instantiated result type with proper indices

  This enables bidirectional index inference:
  - When checking `Cons x xs` against `Vec 5 Int`, we generate constraint `n+1 = 5`
  - When inferring `Cons x xs`, we get `Vec ?n+1 ?a` with fresh metas for indices
-/
partial def inferConstructorApp {scope : Scope}
    (ctorTy : Value) (args : ExprList Unit scope) (span : Span)
    : TCM (Value × ExprList Value scope) := do
  -- Insert implicit arguments (type parameters and indices become metavariables)
  -- This creates fresh metas for each implicit, e.g., ?a for type param, ?n for index
  let rec go (ty : Value) (remainingArgs : ExprList Unit scope)
      (checkedArgs : ExprList Value scope)
      : TCM (Value × ExprList Value scope) := do
    let ty' ← force ty
    match ty', remainingArgs with
    -- No more arguments: return the result type
    | _, .nil =>
      return (ty', checkedArgs)

    -- Pi type with implicit parameter: insert metavariable automatically
    | .vPi _qty binder name dom cod, _ =>
      if binder.isImplicit then
        -- Create metavariable for implicit type/index parameter
        let metaVal ← TCM.freshMetaVal dom
        let resultTy ← applyClosure cod metaVal
        -- Continue with the same remaining args (implicit was auto-inserted)
        go resultTy remainingArgs checkedArgs
      else
        -- Explicit parameter: check the next argument
        match remainingArgs with
        | .nil =>
          -- Partial application - return current type
          return (ty', checkedArgs)
        | .cons arg restArgs =>
          -- Check argument against domain type (generates unification constraints)
          let argExpr ← check arg dom
          let argVal ← TCM.evalTyped argExpr
          let resultTy ← applyClosure cod argVal
          -- Continue with remaining arguments
          go resultTy restArgs (.cons argExpr checkedArgs)

    -- Not a Pi type but have more arguments: error
    | _, .cons _ _ =>
      TCM.throw (.expectedFunction ty' span)

  let (resultTy, reversedArgs) ← go ctorTy args .nil
  -- Reverse the accumulated args to get correct order
  let argsExpr := reverseExprList reversedArgs
  return (resultTy, argsExpr)
where
  /-- Reverse an ExprList -/
  reverseExprList {scope : Scope} (xs : ExprList Value scope) : ExprList Value scope :=
    let rec go (acc : ExprList Value scope) : ExprList Value scope → ExprList Value scope
      | .nil => acc
      | .cons x rest => go (.cons x acc) rest
    go .nil xs

partial def inferValueApp {scope : Scope}
    (fnExpr : Expr Value scope) (dom : Value) (cod : Closure)
    (arg : Expr Unit scope) (callSpan : Span)
    : TCM (Value × Expr Value scope) := do
  -- First, infer the argument type to enable reverse propagation
  -- Enhancement 3: We infer first to get the argument's type, then use it
  -- to solve implicits that may appear in the domain type
  let (argTy, argExprInferred) ← infer arg

  -- Reverse propagation: unify argument type with domain
  -- This can solve implicits in the domain that depend on the argument type
  propagateFromArgument argTy dom

  -- Now check the argument against the (possibly refined) domain
  let argExpr ← check arg dom

  -- For full dependent types, always evaluate the argument to a value.
  -- This correctly handles:
  -- - Closed terms: evaluate to concrete values (e.g., 5 → vIntLit 5)
  -- - Open terms with free variables: evaluate to neutral terms that
  --   represent the "stuck" computation (e.g., x → vNeutral Nat (nVar "x"))
  -- - Type arguments: evaluate to type values for substitution
  --
  -- The closure application will then substitute this value into the codomain,
  -- correctly propagating type dependencies even for value-level arguments.
  -- For non-dependent codomains (const closures), the value is ignored anyway.
  let argVal ← TCM.evalTyped argExpr
  -- Apply codomain closure to get result type
  let resultTy ← applyClosure cod argVal
  -- Create application expression
  let appExpr := Expr.call fnExpr (.cons argExpr .nil) resultTy callSpan
  return (resultTy, appExpr)

/--
  Infer type of function application.

  Handles three cases:
  1. Explicit type application to implicit parameter: `f @T`
  2. Polymorphic field access on records: `rec @l`
  3. Regular value application: `f x`

  Implicit arguments are automatically inserted before explicit value arguments.
-/
partial def inferApp {scope : Scope} (fnTy : Value) (fnExpr : Expr Value scope)
    (args : ExprList Unit scope) (span : Span) : TCM (Value × Expr Value scope) := do
  match args with
  | .nil =>
    -- After processing all arguments, do a final greedy solve
    solveImplicitsGreedy
    return (fnTy, fnExpr)
  | .cons arg rest => do
    let fnTy' ← force fnTy

    -- Dispatch based on function type and argument form
    match fnTy', arg with

    -- Case 1: Explicit type application to implicit parameter
    | .vPi _qty binder _name _dom cod, .typeApp typeArg () argSpan =>
      if binder.isImplicit then
        let (resultTy, appExpr) ← inferExplicitTypeApp fnExpr cod typeArg argSpan span
        -- Greedy solve after each argument to propagate type info
        solveImplicitsGreedy
        inferApp resultTy appExpr rest span
      else
        -- Explicit parameter with typeApp - treat as regular application
        let (fnTy'', fnExpr') ← insertImplicits fnTy fnExpr span
        let (_, _, _, dom, cod) ← ensurePi fnTy'' span
        let (resultTy, appExpr) ← inferValueApp fnExpr' dom cod arg span
        -- Greedy solve after each argument
        solveImplicitsGreedy
        inferApp resultTy appExpr rest span

    -- Case 2: Polymorphic field access on record type
    | .vRecord row, .typeApp (.label labelName) () argSpan =>
      let (fieldTy, fieldExpr) ← inferPolymorphicFieldAccess fnExpr row labelName argSpan span
      -- Greedy solve after field access
      solveImplicitsGreedy
      inferApp fieldTy fieldExpr rest span

    -- Case 3: Regular value application
    | _, _ =>
      -- Insert implicit arguments first
      let (fnTy'', fnExpr') ← insertImplicits fnTy fnExpr span
      let (_, _, _, dom, cod) ← ensurePi fnTy'' span
      let (resultTy, appExpr) ← inferValueApp fnExpr' dom cod arg span
      -- Greedy solve after each argument to propagate constraints immediately
      -- This enables solving implicits as soon as we have enough information
      solveImplicitsGreedy
      inferApp resultTy appExpr rest span

/-- Infer types for an expression list -/
partial def inferExprList {scope : Scope} (es : ExprList Unit scope)
    : TCM (List Value × ExprList Value scope) := do
  match es with
  | .nil => return ([], .nil)
  | .cons e rest => do
    let (ty, expr) ← infer e
    let (restTys, restExprs) ← inferExprList rest
    return (ty :: restTys, .cons expr restExprs)

/-- Infer types for record fields -/
partial def inferRecordFields {scope : Scope} (fields : Soma.Metal.RecordFieldList Unit scope)
    : TCM (Value × Soma.Metal.RecordFieldList Value scope) := do
  match fields with
  | .nil =>
    return (.vRowEmpty, .nil)
  | .cons name expr rest => do
    let (ty, exprE) ← infer expr
    let (restRow, restFields) ← inferRecordFields rest
    let row := Value.vRowExtend (.vLabelLit name) ty restRow
    return (row, .cons name exprE restFields)

/-- Infer types for capture list -/
partial def inferCaptures {scope : Scope} (caps : Soma.Metal.CaptureList Unit scope)
    : TCM (List Value × Soma.Metal.CaptureList Value scope) := do
  match caps with
  | .nil => return ([], .nil)
  | .cons v () rest => do
    match ← TCM.lookupLocal v.original with
    | some entry =>
      let (restTys, restCaps) ← inferCaptures rest
      return (entry.type :: restTys, .cons v entry.type restCaps)
    | none =>
      TCM.throw (.unboundVariable v.original Span.uninhabited)

/-- Infer arms of a case expression.
    For each arm, we:
    1. Extract pattern bindings with types from scrutinee types
    2. Extend the context with these bindings
    3. Infer the body type under the extended context
    4. Check all arms produce the same result type -/
partial def inferArms {scope : Scope} (arms : Soma.Metal.ArmList Unit scope)
    (scrutTys : List Value) (expectedTy : Value)
    : TCM (Soma.Metal.ArmList Value scope) := do
  match arms with
  | .nil => return .nil
  | .cons (.mk pats body armSpan) rest => do
    -- Type the patterns with the expected type as annotation
    let typedPats := pats.mapInfo (fun () => expectedTy)

    -- Check the body - inferArmBody handles context extension for pattern bindings
    let bodyExpr ← inferArmBody pats scrutTys body expectedTy armSpan

    -- Check remaining arms
    let restArms ← inferArms rest scrutTys expectedTy

    -- Use the theorem that mapInfo preserves bindingIds
    let h : typedPats.bindingIds ++ scope = pats.bindingIds ++ scope := by
      rw [Soma.Metal.PatternList.mapInfo_bindingIds]
    return .cons (.mk typedPats (h ▸ bodyExpr) armSpan) restArms

/-- Extract field types from a constructor type, unifying the result type with the scrutinee type.

    For a constructor type like `forall {a}. a -> Vec n a -> Vec (n+1) a` and
    scrutinee type `Vec 5 Int`:
    1. Instantiate implicits with fresh metas: `?a -> Vec ?n ?a -> Vec (?n+1) ?a`
    2. Collect explicit argument types: [?a, Vec ?n ?a]
    3. Unify result type `Vec (?n+1) ?a` with scrutinee `Vec 5 Int`
    4. This generates constraints: `?n+1 = 5`, `?a = Int`
    5. Return field types with metas that will be solved: [Int, Vec 4 Int]

    This enables proper index inference in pattern matching. -/
partial def extractConstructorFieldTypes (ctorTy : Value) (scrutTy : Value)
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

  -- Unify the constructor's result type with the scrutinee type
  -- This generates constraints on the indices
  unify resultTy scrutTy

  return fieldTypes

/-- Extract binding types from a pattern and its scrutinee type.
    For example, if pattern is (x, y) and scrutinee type is (Int, Bool),
    returns [(x, Int), (y, Bool)]. -/
partial def extractPatternBindingTypes (pat : Soma.Metal.Pattern Unit) (scrutTy : Value)
    : TCM (List (Soma.Metal.BindingId × String × Value)) := do
  match pat with
  | .var binding orig () _ =>
    return [(binding, orig, scrutTy)]
  | .wildcard () _ =>
    return []
  | .lit _ _ =>
    return []
  | .tuple elems () _ =>
    -- For tuple patterns, decompose the sigma type
    extractTupleBindingTypes elems.toList scrutTy
  | .ctor ctorName args () _ =>
    -- For constructor patterns, try to get field types from the constructor's declared type
    -- This enables proper index inference in pattern matching
    match ← TCM.lookupGlobal ctorName.display with
    | some ctorInfo =>
      -- Extract field types from constructor type, unifying with scrutinee type
      let fieldTypes ← extractConstructorFieldTypes ctorInfo.type scrutTy
      let mut result : List (Soma.Metal.BindingId × String × Value) := []
      for (arg, fieldTy) in args.toList.zip fieldTypes.toList do
        let bindings ← extractPatternBindingTypes arg fieldTy
        result := result ++ bindings
      -- Handle remaining args with fresh metas if constructor has more args than extracted types
      for arg in args.toList.drop fieldTypes.size do
        let argTy ← TCM.freshMetaVal (.vType .zero)
        let bindings ← extractPatternBindingTypes arg argTy
        result := result ++ bindings
      return result
    | none =>
      -- Fallback: constructor not in globals, use fresh metas
      let mut result : List (Soma.Metal.BindingId × String × Value) := []
      for arg in args do
        let argTy ← TCM.freshMetaVal (.vType .zero)
        let bindings ← extractPatternBindingTypes arg argTy
        result := result ++ bindings
      return result
  | .array elems () _ =>
    -- Array/List elements all have the same type
    let elemTy ← TCM.freshMetaVal (.vType .zero)
    -- Try to extract element type from scrutinee and unify
    let scrutTy' ← force scrutTy
    match scrutTy' with
    | .vDataType _ (actualElemTy :: _) =>
      -- Scrutinee is a data type with at least one param (List a or Array a)
      unify elemTy actualElemTy
    | _ =>
      -- If scrutinee is a metavariable or other form, construct the expected
      -- list type and unify with scrutinee using stable builtin TypeId
      let listId := Soma.Core.TypeId.builtin "List" Soma.Core.HigherPrimitive.list.uniqueId
      let expectedListTy := Value.vDataType listId [elemTy]
      unify scrutTy expectedListTy
    let mut result : List (Soma.Metal.BindingId × String × Value) := []
    for elem in elems do
      let bindings ← extractPatternBindingTypes elem elemTy
      result := result ++ bindings
    return result
  | .cons head tail () _ =>
    -- List cons: head has element type, tail has list type
    -- Create a fresh meta for element type and unify with scrutinee structure
    let elemTy ← TCM.freshMetaVal (.vType .zero)
    -- Try to extract element type from scrutinee and unify
    let scrutTy' ← force scrutTy
    match scrutTy' with
    | .vDataType _ (actualElemTy :: _) =>
      -- Scrutinee is a data type with at least one param (List a)
      -- Unify our fresh meta with the actual element type
      unify elemTy actualElemTy
    | _ =>
      -- If scrutinee is a metavariable or other form, construct the expected
      -- list type and unify with scrutinee using stable builtin TypeId
      let listId := Soma.Core.TypeId.builtin "List" Soma.Core.HigherPrimitive.list.uniqueId
      let expectedListTy := Value.vDataType listId [elemTy]
      unify scrutTy expectedListTy
    let headBindings ← extractPatternBindingTypes head elemTy
    -- The tail has the same type as the scrutinee (List elemTy)
    let tailBindings ← extractPatternBindingTypes tail scrutTy
    return headBindings ++ tailBindings
  | .as binding orig inner () _ =>
    let innerBindings ← extractPatternBindingTypes inner scrutTy
    return (binding, orig, scrutTy) :: innerBindings
  | .variant _ arg () _ =>
    match arg with
    | some p =>
      let argTy ← TCM.freshMetaVal (.vType .zero)
      extractPatternBindingTypes p argTy
    | none => return []
where
  /-- Extract bindings from tuple pattern elements against a Sigma type -/
  extractTupleBindingTypes (elems : List (Soma.Metal.Pattern Unit)) (ty : Value)
      : TCM (List (Soma.Metal.BindingId × String × Value)) := do
    match elems with
    | [] => return []
    | [lastElem] =>
      -- Last element gets whatever type remains
      extractPatternBindingTypes lastElem ty
    | elem :: rest =>
      -- Try to decompose as a Sigma type
      let ty' ← force ty
      match ty' with
      | .vSigma _ _ fstTy sndClos =>
        let elemBindings ← extractPatternBindingTypes elem fstTy
        -- Apply closure to get the second component type
        let lvl ← TCM.currentLevel
        let dummyVal := Value.vNeutral fstTy (.nVar ⟨"_", lvl⟩)
        let sndTy ← applyClosure sndClos dummyVal
        let restBindings ← extractTupleBindingTypes rest sndTy
        return elemBindings ++ restBindings
      | _ =>
        -- Not a Sigma, fall back to fresh metas
        let mut result : List (Soma.Metal.BindingId × String × Value) := []
        for e in (elem :: rest) do
          let eTy ← TCM.freshMetaVal (.vType .zero)
          let bindings ← extractPatternBindingTypes e eTy
          result := result ++ bindings
        return result

/-- Extract binding types from a pattern list and corresponding scrutinee types -/
partial def extractPatternListBindingTypes (pats : Soma.Metal.PatternList Unit) (scrutTys : List Value)
    : TCM (List (Soma.Metal.BindingId × String × Value)) := do
  match pats, scrutTys with
  | .nil, _ => return []
  | .cons pat rest, ty :: tys =>
    let patBindings ← extractPatternBindingTypes pat ty
    let restBindings ← extractPatternListBindingTypes rest tys
    return patBindings ++ restBindings
  | .cons pat rest, [] =>
    -- No more scrutinee types, use fresh metas
    let freshTy ← TCM.freshMetaVal (.vType .zero)
    let patBindings ← extractPatternBindingTypes pat freshTy
    let restBindings ← extractPatternListBindingTypes rest []
    return patBindings ++ restBindings

/-- Infer a single arm body, extending context with pattern bindings.
    This function processes the pattern list to extend the context appropriately
    before type-checking the body. Uses scrutinee types to properly type pattern variables. -/
partial def inferArmBody {scope : Scope} (pats : Soma.Metal.PatternList Unit)
    (scrutTys : List Value) (body : Expr Unit (pats.bindingIds ++ scope))
    (expectedTy : Value) (span : Span)
    : TCM (Expr Value (pats.bindingIds ++ scope)) := do
  -- Get bindings with types from patterns and scrutinee types
  let bindingsWithTypes ← extractPatternListBindingTypes pats scrutTys

  -- Extend context with all bindings (with proper types) and check body
  inferArmBodyWithBindings bindingsWithTypes body expectedTy span

/-- Helper: extend context with bindings (with known types) and infer body.
    The scope parameter is implicit in the body type. -/
partial def inferArmBodyWithBindings {extScope : Scope}
    (bindings : List (Soma.Metal.BindingId × String × Value))
    (body : Expr Unit extScope) (expectedTy : Value) (span : Span)
    : TCM (Expr Value extScope) := do
  match bindings with
  | [] =>
    -- No bindings left, CHECK the body against expected type
    -- This is important: check (not infer) so that [] can be treated as List
    -- when the expected type is List, rather than being inferred as Array
    check body expectedTy
  | (_, name, bindingTy) :: rest =>
    -- Use the type from pattern matching against scrutinee
    TCM.withBinding name bindingTy .omega .explicit span do
      inferArmBodyWithBindings rest body expectedTy span

/-- Look up field type in a record type -/
partial def lookupFieldType (recTy : Value) (fieldName : String) (span : Span) : TCM Value := do
  let recTy' ← force recTy
  match recTy' with
  | .vRecord row => findFieldInRow row fieldName span
  | .vRecordVal fields =>
    match fields.find? (·.1 == fieldName) with
    | some (_, ty) => return ty
    | none => TCM.throw (.fieldNotFound fieldName recTy' span)
  | _ => TCM.throw (.expectedRecord recTy' span)

/-- Find a field in a row type -/
partial def findFieldInRow (row : Value) (fieldName : String) (span : Span) : TCM Value := do
  match row with
  | .vRowEmpty =>
    TCM.throw (.fieldNotFound fieldName row span)
  | .vRowExtend (.vLabelLit name) ty tail =>
    if name == fieldName then
      return ty
    else
      findFieldInRow tail fieldName span
  | .vNeutral _ _ =>
    -- Can't search in neutral row
    TCM.throw (.fieldNotFound fieldName row span)
  | _ =>
    TCM.throw (.fieldNotFound fieldName row span)

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
    TCM.throw (.fieldNotFound labelStr row' span)
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
    let tailMeta ← TCM.freshMetaVal (.vType .zero)
    let newRow := Value.vRowExtend lookupLabel' fieldTy tailMeta
    unify row' newRow
    return fieldTy
  | .vNeutral _ _ =>
    -- Can't search in other neutral rows
    let labelStr := match lookupLabel' with
      | .vLabelLit name => name
      | .vNeutral _ (.nVar v) => v.name
      | _ => "<label>"
    TCM.throw (.fieldNotFound labelStr row' span)
  | _ =>
    let labelStr := match lookupLabel' with
      | .vLabelLit name => name
      | .vNeutral _ (.nVar v) => v.name
      | _ => "<label>"
    TCM.throw (.fieldNotFound labelStr row' span)

end

/-! ## Top-Level Interface -/

/-- Type check an expression, inferring its type -/
def typeInfer (e : Expr Unit scope) (ctx : TCContext := TCContext.empty)
    : Except TCError (Value × Expr Value scope × TCState) := do
  let ((ty, expr), state) ← (infer e).run ctx
  return (ty, expr, state)

/-- Type check an expression against an expected type -/
def typeCheck (e : Expr Unit scope) (expected : Value)
    (ctx : TCContext := TCContext.empty) : Except TCError (Expr Value scope × TCState) := do
  let (expr, state) ← (check e expected).run ctx
  return (expr, state)

end Soma.Dependent
