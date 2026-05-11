import Soma.Dependent.Totality.Core
import Soma.Dependent.Totality.TermShape
import Soma.Dependent.Totality.CallMatrix
import Soma.Dependent.Totality.Positivity
import Soma.Core.Expr

namespace Soma.Dependent.Totality

open Soma.Core
open Soma.Syntax (Span)

/-- Collect the application spine from nested binary apps -/
private partial def collectAppSpine' (e : Soma.Core.Expr) : Soma.Core.Expr × List Soma.Core.Expr :=
  match e with
  | .app fn arg =>
    let (head, args) := collectAppSpine' fn
    (head, args ++ [arg])
  | _ => (e, [])

/-- Get a variable name from an Expr for scrutinee parameter matching -/
private def exprVarName? : Soma.Core.Expr → Option String
  | .fvar id _ => some id.original
  | .const name _ => some name.display
  | _ => none

/-- Analyze a case arm and extract all bindings introduced by the pattern (Expr version). -/
private def analyzePatternFromArmExpr (patternName : String) (scrutineeParam : Option (Nat × String))
    (armBody : Soma.Core.Expr) (existingParams : Array String) : Array BindingInfo :=
  match scrutineeParam with
  | none => #[]
  | some (paramIdx, paramName) =>
    let usedVars := collectExprVars armBody
    let newVars := usedVars.filter fun v => !existingParams.contains v
    newVars.toArray.map fun name => {
      name := name
      paramIdx := paramIdx
      paramName := paramName
      path := .ctorArg .root patternName 0
      depth := 1
    }

/-- Check if a recursive call terminates using SupGen-style structural comparison
    Returns a decrease witness if termination can be proven. -/
def checkRecursiveCallStructural (args : List Soma.Core.Expr) (ctx : TerminationContext)
    : DecreaseWitness :=
  let argShapes := args.map analyzeExprShape

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
private def findScrutineeParam (scrutinee : Soma.Core.Expr) (params : Array String) : Option (Nat × String) :=
  match exprVarName? scrutinee with
  | some name =>
    match params.findIdx? (· == name) with
    | some idx => some (idx, name)
    | none => none
  | none => none

/-- Check termination for a function body -/
partial def checkTermination (fnInfo : FunctionInfo) (body : Soma.Core.Expr) : TermM Unit := do
  TermM.setCurrentFn fnInfo
  checkTerm body
where
  /-- Check a term for termination -/
  checkTerm (t : Soma.Core.Expr) : TermM Unit := do
    match t with
    | .bvar _ => pure ()
    | .fvar _ _ => pure ()
    | .mvar _ => pure ()
    | .tyvar _ _ => pure ()
    | .const name _ =>
      let fnInfo? ← TermM.getCurrentFn
      match fnInfo? with
      | some fnInfo =>
        if name.display == fnInfo.name.display then
          TermM.recordRecursiveCall {
            callSpan := Span.uninhabited
            callee := fnInfo.name
            argNames := #[]
            decrease := .notFound "self-reference has no arguments to decrease on"
          }
      | none => pure ()
    | .lit _ => pure ()
    | .sort _ => pure ()
    | .primTy _ => pure ()
    | .rowSort => pure ()
    | .labelSort => pure ()
    | .rowEmpty => pure ()
    | .labelLit _ => pure ()
    | .panic _ => pure ()
    | .proj _ _ _ => pure ()

    | .app _ _ =>
      let (head, args) := collectAppSpine' t
      match head with
      | .const name _ =>
        let fnInfo? ← TermM.getCurrentFn
        match fnInfo? with
        | some fnInfo =>
          if name.display == fnInfo.name.display then
            let ctx ← TermM.getContext
            let witness := checkRecursiveCallStructural args ctx
            let argNames := args.filterMap (fun e =>
              exprVarName? e) |>.toArray
            TermM.recordRecursiveCall {
              callSpan := Span.uninhabited
              callee := fnInfo.name
              argNames := argNames
              decrease := witness
            }
        | none => pure ()
      | _ => checkTerm head
      for arg in args do
        checkTerm arg

    | .lam _ _ _ body => checkTerm body

    | .let_ _ ty val body =>
      checkTerm ty
      checkTerm val
      checkTerm body

    | .if_ cond then_ else_ =>
      checkTerm cond
      checkTerm then_
      checkTerm else_

    | .pi _ _ _ dom cod =>
      checkTerm dom
      checkTerm cod

    | .recordTy row => checkTerm row
    | .variantTy row => checkTerm row

    | .rowExtend label ty tail =>
      checkTerm label
      checkTerm ty
      checkTerm tail

    | .record fields =>
      for (_, t) in fields do
        checkTerm t

    | .recordUpdate base updates =>
      checkTerm base
      for (_, t) in updates do
        checkTerm t

    | .fieldAccess e _ _ => checkTerm e

    | .inject _ args _ =>
      for arg in args do
        checkTerm arg

    | .construct _ _ args _ =>
      for arg in args do
        checkTerm arg

    | .«case» scruts _ arms =>
      for scrut in scruts do
        checkTerm scrut

      -- Use the first scrutinee for parameter matching
      let scrutinee := scruts[0]?
      let fnInfo? ← TermM.getCurrentFn
      let paramInfo := match fnInfo?, scrutinee with
        | some fnInfo, some s => findScrutineeParam s fnInfo.params
        | _, _ => none

      for arm in arms do
        let patName := match arm.patterns[0]? with
          | some (.ctor name _ _) => name.display
          | _ => "_"
        let armBody := arm.body
        match paramInfo with
        | some (paramIdx, paramName) =>
          let ctx ← TermM.getContext
          let bindings := analyzePatternFromArmExpr patName (some (paramIdx, paramName))
                           armBody ctx.params
          TermM.withBindings bindings do
            checkTerm armBody
        | none =>
          checkTerm armBody

    | .eqTy _ ty lhs rhs =>
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

    | .closure _ caps _ =>
      for cap in caps do
        checkTerm cap

    | .array elements _ =>
      for e in elements do
        checkTerm e

    | .tuple elements =>
      for e in elements do
        checkTerm e

    | .dataTy _ params =>
      for p in params do
        checkTerm p

    | .ann expr ty =>
      checkTerm expr
      checkTerm ty

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
def checkFunctionTotality (fnInfo : FunctionInfo) (body : Soma.Core.Expr) : TotalityCheckResult :=
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
def assertFunctionTotal (name : QualifiedName) (status : TotalityStatus) (span : Span) : TCM Unit := do
  match status with
  | .isTotal => pure ()
  | .isPartial => TCM.throw (.partialInTypeIndex name span)
  | .isUnknown => TCM.addWarning (.totalityUnknown name span)

/-- Check and register a function's totality -/
def checkAndRegisterTotality (fnInfo : FunctionInfo) (body : Soma.Core.Expr)
    (registry : TotalityRegistry) : TotalityRegistry × TotalityCheckResult :=
  if fnInfo.markedTotal then
    let result := checkFunctionTotality fnInfo body
    let registry' := registry.register fnInfo.name.display result.status
    (registry', result)
  else
    let registry' := registry.register fnInfo.name.display .isPartial
    (registry', { status := .isPartial, errors := #[], recursiveCalls := #[] })

/-- Check mutual recursion termination using call matrix -/
def checkMutualTermination (functions : Array FunctionInfo) (bodies : Array Soma.Core.Expr)
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
