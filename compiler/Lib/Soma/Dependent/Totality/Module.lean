import Soma.Core.Function
import Soma.Dependent.Totality.Core
import Soma.Dependent.Totality.CallMatrix
import Soma.Dependent.Totality.Check
import Soma.Dependent.Error
import Soma.Dependent.Coverage
import Soma.Dependent.Monad

namespace Soma.Dependent.Totality

open Soma.Core
open Soma.Syntax (Span)

/-- Outcome of checking a single function's totality -/
structure FunctionTotality where
  name : QualifiedName
  status : TotalityStatus
  span : Span
  error : Option TCError := none
  deriving Inhabited

/-- Result of the module-level totality pass -/
structure ModuleTotalityResult where
  /-- Registry recording the inferred status of every function -/
  registry : TotalityRegistry
  /-- Per-function totality outcomes, keyed by qualified name display -/
  outcomes : Std.HashMap String FunctionTotality
  /-- Errors to surface to the user -/
  errors : Array TCError
  deriving Inhabited

/-- Convert a `TypedFunction` into the `FunctionInfo` the checker expects -/
private def functionInfoOf (fn : TypedFunction) (span : Span) : FunctionInfo :=
  { name := fn.name
    markedTotal := fn.attrs.total
    status := .isUnknown
    params := fn.params.map (·.2)
    fnType := fn.fnType
    span := span }

/-- Skip checking functions that are not meaningfully recursive -/
private def needsCheck (fn : TypedFunction) : Bool :=
  fn.attrs.intrinsic.isNone ∧ fn.attrs.extern.isNone

/-- Run the matrix-based termination analysis for a mutual group -/
private def verifyGroup (fns : Array FunctionInfo) (bodies : Array Expr) : Bool × String :=
  checkMatrixTermination fns bodies

/-- Attempt to prove a single function terminates using the structural decrease checker -/
private def verifySingle (fnInfo : FunctionInfo) (body : Expr) : TotalityCheckResult :=
  checkFunctionTotality fnInfo body

/-- Is a return-type value "definitely uninhabited" at the module level -/
private partial def returnTypeIsUninhabited (ty : Value) : TCM Bool := do
  let ty' ← force ty
  match ty' with
  | .vPi _ _ name dom cod =>
    let lvl ← TCM.currentLevel
    let dummy := Value.vNeutral dom (.nVar ⟨name, lvl⟩)
    let cod' ← applyClosure cod dummy
    returnTypeIsUninhabited cod'
  | .vDataType _ _ =>
    let savedState ← get
    let (isOpen, cands) ← Coverage.liveCandidates ty'
    set savedState
    pure (!isOpen ∧ cands.isEmpty)
  | _ => pure false

/-- Build a termination-check error, flagging the function that failed -/
private def terminationError (fnInfo : FunctionInfo) (reason : String) : TCError :=
  .terminationCheckFailed fnInfo.name reason fnInfo.span #[] #[]

/-- Produce the final per-SCC verdicts -/
private def finalizeScc (sccFns : Array (FunctionInfo × TypedFunction × Expr))
    (ok : Bool) (reason : String)
    : Array FunctionTotality :=
  sccFns.map fun (info, fn, _) =>
    if ok then
      { name := info.name, status := .isTotal, span := info.span, error := none }
    else if fn.attrs.partial_ then
      { name := info.name, status := .isPartial, span := info.span, error := none }
    else
      { name := info.name, status := .isPartial, span := info.span,
        error := some (terminationError info reason) }

/-- Run the totality pass for an entire module -/
def runTotalityChecks
    (typed : Array TypedFunction)
    (spans : Std.HashMap String Span)
    : TCM ModuleTotalityResult := do
  let active : Array (FunctionInfo × TypedFunction × Expr) :=
    typed.filterMap fun fn =>
      if needsCheck fn then
        let span := spans.getD fn.name.display Span.uninhabited
        some (functionInfoOf fn span, fn, fn.body)
      else
        none

  let mut registry := TotalityRegistry.empty
  let mut outcomes : Std.HashMap String FunctionTotality := {}
  for fn in typed do
    if !needsCheck fn then
      let span := spans.getD fn.name.display Span.uninhabited
      registry := registry.register fn.name.display .isTotal
      outcomes := outcomes.insert fn.name.display
        { name := fn.name, status := .isTotal, span := span, error := none }

  let infos := active.map (·.1)
  let bodies := active.map (·.2.2)
  if active.isEmpty then
    return { registry, outcomes, errors := #[] }

  -- SCC decomposition over the call graph of all active functions
  let graph := buildCallGraph infos bodies
  let sccs := findSCCs graph

  let mut errors : Array TCError := #[]

  let findTriple (name : String) : Option (FunctionInfo × TypedFunction × Expr) :=
    active.find? fun (info, _, _) => info.name.display == name

  for scc in sccs do
    let sccTriples : Array (FunctionInfo × TypedFunction × Expr) :=
      scc.filterMap findTriple
    if sccTriples.isEmpty then continue

    let sccInfos := sccTriples.map (·.1)
    let sccBodies := sccTriples.map (·.2.2)

    let (ok, reason) :=
      match sccTriples.toList with
      | [(info, _, body)] =>
        let result := verifySingle info body
        match result.status with
        | .isTotal => (true, "structural recursion")
        | _ =>
          let reason :=
            match result.recursiveCalls.findSome? (fun c =>
              match c.decrease with
              | .notFound r => some r
              | _ => none) with
            | some r => r
            | none => "recursion is not structurally decreasing"
          (false, reason)
      | _ => verifyGroup sccInfos sccBodies

    let verdicts := finalizeScc sccTriples ok reason
    for v in verdicts do
      registry := registry.register v.name.display v.status
      outcomes := outcomes.insert v.name.display v
      match v.error with
      | some e => errors := errors.push e
      | none   => pure ()

  for (info, fn, _) in active do
    if fn.attrs.partial_ then
      if (← returnTypeIsUninhabited fn.fnType) then
        errors := errors.push (.partialInhabitsUninhabited info.name info.span)

  return { registry, outcomes, errors }

end Soma.Dependent.Totality
