import Soma.Dependent.Totality.Core
import Soma.Dependent.Totality.TermShape
import Soma.Dependent.Totality.CallMatrix
import Soma.Dependent.Totality.Positivity

namespace Soma.Dependent.Totality

open Soma.Core
open Soma.Metal (Name)
open Soma.Syntax (Span)

/-- Check if a recursive call terminates using SupGen-style structural comparison
    Returns a decrease witness if termination can be proven. -/
def checkRecursiveCallStructural (args : List Term) (ctx : TerminationContext)
    : DecreaseWitness :=
  let argShapes := args.map analyzeTermShape

  -- Try lexicographic comparison across arguments
  let rec go (shapes : List TermShape) (idx : Nat) : DecreaseWitness :=
    match shapes with
    | [] => .notFound "all arguments are equal or no relationship found"
    | shape :: rest =>
      if h : idx < ctx.params.size then
        let paramName := ctx.params[idx]
        let cmp := compareTermToParam shape idx paramName ctx

        match cmp with
        | .smaller reason =>
          .arg idx reason
        | .equal =>
          go rest (idx + 1)
        | .larger =>
          fallbackCheck argShapes idx
        | .unknown =>
          fallbackCheck argShapes idx
      else
        fallbackCheck argShapes idx

  go argShapes 0
where
  /-- Fallback: check if any argument at all is smaller -/
  fallbackCheck (shapes : List TermShape) (failedIdx : Nat) : DecreaseWitness :=
    let rec search (ss : List TermShape) (idx : Nat) : Option (Nat × String) :=
      match ss with
      | [] => none
      | shape :: rest =>
        let vars := shape.collectVars
        let allSmaller := vars.all fun v =>
          match ctx.lookup v with
          | some info => info.isSmaller
          | none => false
        let anySmaller := vars.any fun v =>
          match ctx.lookup v with
          | some info => info.isSmaller
          | none => false
        if anySmaller && allSmaller then
          some (idx, s!"argument {idx} uses only smaller bindings")
        else if anySmaller then
          some (idx, s!"argument {idx} uses at least one smaller binding")
        else
          search rest (idx + 1)

    match search shapes 0 with
    | some (idx, reason) => .arg idx reason
    | none => .notFound s!"no decreasing argument found (failed at position {failedIdx})"

/-- Find which parameter a scrutinee corresponds to -/
private def findScrutineeParam (scrutinee : Term) (params : Array String) : Option (Nat × String) :=
  match scrutinee with
  | .var _ name =>
    match params.findIdx? (· == name) with
    | some idx => some (idx, name)
    | none => none
  | _ => none

/-- Check termination for a function body -/
partial def checkTermination (fnInfo : FunctionInfo) (body : Term) : TermM Unit := do
  TermM.setCurrentFn fnInfo
  checkTerm body
where
  /-- Check a term for termination -/
  checkTerm (t : Term) : TermM Unit := do
    match t with
    | .var _ _ => pure ()
    | .lit _ => pure ()

    | .app fn args =>
      match fn with
      | .global name =>
        let fnInfo? ← TermM.getCurrentFn
        match fnInfo? with
        | some fnInfo =>
          if name == fnInfo.name then
            let ctx ← TermM.getContext
            let witness := checkRecursiveCallStructural args ctx
            let argNames := args.filterMap (fun t =>
              match t with
              | .var _ n => some n
              | _ => none) |>.toArray
            TermM.recordRecursiveCall {
              callSpan := Span.uninhabited
              callee := name
              argNames := argNames
              decrease := witness
            }
        | none => pure ()
      | _ => pure ()
      checkTerm fn
      for arg in args do
        checkTerm arg

    | .lam _ body => checkTerm body
    | .let_ _ value body =>
      checkTerm value
      checkTerm body

    | .if_ cond then_ else_ =>
      checkTerm cond
      checkTerm then_
      checkTerm else_

    | .pair fst snd =>
      checkTerm fst
      checkTerm snd

    | .fst e => checkTerm e
    | .snd e => checkTerm e

    | .pi _ _ _ dom cod =>
      checkTerm dom
      checkTerm cod

    | .sigma _ _ fst snd =>
      checkTerm fst
      checkTerm snd

    | .recordTy row => checkTerm row
    | .variantTy row => checkTerm row

    | .rowExtend label ty tail =>
      checkTerm label
      checkTerm ty
      checkTerm tail

    | .record fields =>
      for (_, t) in fields do
        checkTerm t

    | .fieldAccess e _ => checkTerm e

    | .construct _ _ args =>
      for arg in args do
        checkTerm arg

    | .case scrutinee arms =>
      checkTerm scrutinee

      let fnInfo? ← TermM.getCurrentFn
      let paramInfo := match fnInfo? with
        | some fnInfo => findScrutineeParam scrutinee fnInfo.params
        | none => none

      for (patName, _tag, armBody) in arms do
        match paramInfo with
        | some (paramIdx, paramName) =>
          let ctx ← TermM.getContext
          let bindings := analyzePatternFromArm patName (some (paramIdx, paramName))
                           armBody ctx.params
          TermM.withBindings bindings do
            checkTerm armBody
        | none =>
          checkTerm armBody

    | .eq _ ty lhs rhs =>
      checkTerm ty
      checkTerm lhs
      checkTerm rhs

    | .refl ty x =>
      checkTerm ty
      checkTerm x

    | .transport _ ty motive lhs rhs eq body =>
      checkTerm ty
      checkTerm motive
      checkTerm lhs
      checkTerm rhs
      checkTerm eq
      checkTerm body

    | _ => pure ()

/-- Verify all recursive calls are well-founded -/
def verifyRecursiveCalls (fnInfo : FunctionInfo) : TermM Bool := do
  let s ← TermM.getState
  let mut allOk := true

  for call in s.recursiveCalls do
    match call.decrease with
    | .arg _ _ => pure ()
    | .lex _ => pure ()
    | .notFound reason =>
      allOk := false
      TermM.addError (.terminationCheckFailed fnInfo.name reason call.callSpan #[] #[])

  return allOk

/-- Check totality for a function marked @[total] -/
def checkFunctionTotality (fnInfo : FunctionInfo) (body : Term) : TotalityCheckResult :=
  match (do
    checkTermination fnInfo body
    let ok ← verifyRecursiveCalls fnInfo
    return ok
  ).run with
  | .ok (ok, state) =>
    if ok then
      { status := .isTotal, errors := state.errors, recursiveCalls := state.recursiveCalls }
    else
      { status := .isPartial, errors := state.errors, recursiveCalls := state.recursiveCalls }
  | .error e =>
    { status := .isPartial, errors := #[e], recursiveCalls := #[] }

/-- Check if a function is total (for use in type indices) -/
def assertFunctionTotal (name : Name) (status : TotalityStatus) (span : Span) : TCM Unit := do
  match status with
  | .isTotal => pure ()
  | .isPartial => TCM.throw (.partialInTypeIndex name span)
  | .isUnknown => TCM.addWarning (.totalityUnknown name span)

/-- Check and register a function's totality -/
def checkAndRegisterTotality (fnInfo : FunctionInfo) (body : Term)
    (registry : TotalityRegistry) : TotalityRegistry × TotalityCheckResult :=
  if fnInfo.markedTotal then
    let result := checkFunctionTotality fnInfo body
    let registry' := registry.register fnInfo.name.display result.status
    (registry', result)
  else
    let registry' := registry.register fnInfo.name.display .isPartial
    (registry', { status := .isPartial, errors := #[], recursiveCalls := #[] })

/-- Check mutual recursion termination using call matrix -/
def checkMutualTermination (functions : Array FunctionInfo) (bodies : Array Term)
    : TotalityCheckResult :=
  let matrix := buildCallMatrix functions bodies
  match matrix.verifyTermination with
  | some reason =>
    let calls : Array RecursiveCallInfo := matrix.rows.map fun row =>
      { callSpan := row.span, callee := dummyName, argNames := #[], decrease := .arg 0 reason }
    { status := .isTotal, errors := #[], recursiveCalls := calls }
  | none =>
    let err := TCError.terminationCheckFailed dummyName "mutual recursion does not decrease" Span.uninhabited #[] #[]
    { status := .isPartial, errors := #[err], recursiveCalls := #[] }

end Soma.Dependent.Totality
