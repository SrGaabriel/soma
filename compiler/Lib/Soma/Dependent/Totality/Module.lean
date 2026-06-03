import Soma.Core.Function
import Soma.Dependent.Totality.Core
import Soma.Dependent.Totality.Structure
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
    status := .isUnknown
    params := fn.valueParams.map (·.name)
    paramIds := fn.valueParams.map (·.uid)
    fnType := fn.fnType
    span := span }

/-- Functions that are not meaningfully checkable (foreign/intrinsic) -/
private def needsCheck (fn : TypedFunction) : Bool :=
  fn.attrs.intrinsic.isNone ∧ fn.attrs.extern.isNone

/-- Whether a return-type value is "definitely uninhabited" at the module level -/
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

/-- Run the totality pass for an entire module -/
def runTotalityChecks
    (typed : Array TypedFunction)
    (spans : Std.HashMap String Span)
    : TCM ModuleTotalityResult := do
  let mut registry := TotalityRegistry.empty
  let mut outcomes : Std.HashMap String FunctionTotality := {}
  for fn in typed do
    if !needsCheck fn then
      let span := spans.getD fn.name.display Span.uninhabited
      registry := registry.register fn.name.display .isTotal
      outcomes := outcomes.insert fn.name.display
        { name := fn.name, status := .isTotal, span := span, error := none }

  let activeFns := typed.filter needsCheck
  if activeFns.isEmpty then
    return { registry, outcomes, errors := #[] }

  let allTargets : Std.HashSet String :=
    activeFns.foldl (init := ({} : Std.HashSet String)) fun s fn => s.insert fn.name.display
  let prepared : Array (TypedFunction × PreparedFn) :=
    activeFns.map fun fn =>
      let span := spans.getD fn.name.display Span.uninhabited
      (fn, prepareFunction (functionInfoOf fn span) allTargets fn.body)

  let names := prepared.map (·.2.info.name.display)
  let calleesOf := prepared.map (·.2.analysis.calls.map (·.callee))
  let graph := CallGraph.build names calleesOf
  let sccs := graph.sccs

  let byName : Std.HashMap String (TypedFunction × PreparedFn) :=
    prepared.foldl (fun m e => m.insert e.2.info.name.display e) {}

  let mut errors : Array TCError := #[]
  for scc in sccs do
    let members : Array (TypedFunction × PreparedFn) := scc.filterMap byName.get?
    if members.isEmpty then continue
    let verdict := checkComponent (members.map (·.2))
    for (fn, pf) in members do
      let status := if verdict.ok then .isTotal else .isPartial
      let err? :=
        if verdict.ok then none
        else if fn.attrs.partial_ then none
        else some (terminationError pf.info verdict.reason)
      registry := registry.register pf.info.name.display status
      outcomes := outcomes.insert pf.info.name.display
        { name := pf.info.name, status, span := pf.info.span, error := err? }
      match err? with
      | some e => errors := errors.push e
      | none => pure ()

  for (fn, pf) in prepared do
    if fn.attrs.partial_ then
      if (← returnTypeIsUninhabited fn.fnType) then
        errors := errors.push (.partialInhabitsUninhabited pf.info.name pf.info.span)

  return { registry, outcomes, errors }

end Soma.Dependent.Totality
