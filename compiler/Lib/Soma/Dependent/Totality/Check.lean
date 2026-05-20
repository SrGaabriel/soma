import Soma.Dependent.Totality.Core
import Soma.Dependent.Totality.TermShape
import Soma.Dependent.Totality.LinArith
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

/-- Check if a recursive call terminates -/
def checkRecursiveCallStructural (args : List Soma.Core.Expr) (ctx : TerminationContext)
    (linCtx : LinCtx) : DecreaseWitness :=
  let argShapes := args.map analyzeExprShape

  -- Try lexicographic comparison across arguments
  let rec go (shapes : List TermShape) (idx : Nat) : DecreaseWitness :=
    match shapes with
    | [] => fallbackToLinear "all arguments are equal or no relationship found"
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
    | none => fallbackToLinear s!"no decreasing argument found (failed at position {failedIdx})"

  fallbackToLinear (structuralReason : String) : DecreaseWitness :=
    match findLinearDecrease ctx.params args linCtx ctx.bindings with
    | some w => .linear w.description
    | none => .notFound structuralReason

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
  checkTerm body LinCtx.empty
where
  /-- Check a term for termination -/
  checkTerm (t : Soma.Core.Expr) (linCtx : LinCtx) : TermM Unit := do
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
            let witness := checkRecursiveCallStructural args ctx linCtx
            let argNames := args.filterMap (fun e =>
              exprVarName? e) |>.toArray
            TermM.recordRecursiveCall {
              callSpan := Span.uninhabited
              callee := fnInfo.name
              argNames := argNames
              decrease := witness
            }
        | none => pure ()
      | _ => checkTerm head linCtx
      for arg in args do
        checkTerm arg linCtx

    | .lam _ _ _ body => checkTerm body linCtx

    | .let_ _ ty val body =>
      checkTerm ty linCtx
      checkTerm val linCtx
      checkTerm body linCtx

    | .if_ cond then_ else_ =>
      checkTerm cond linCtx
      let ctx ← TermM.getContext
      let posAtom? := analyzeCondAtom cond ctx.params ctx.bindings
      let thenCtx := match posAtom? with
        | some a => linCtx.addAtom a
        | none => linCtx
      let elseCtx := match posAtom? with
        | some a => linCtx.addAtom a.negate
        | none => linCtx
      checkTerm then_ thenCtx
      checkTerm else_ elseCtx

    | .pi _ _ _ dom cod =>
      checkTerm dom linCtx
      checkTerm cod linCtx

    | .recordTy row => checkTerm row linCtx
    | .variantTy row => checkTerm row linCtx

    | .rowExtend label ty tail =>
      checkTerm label linCtx
      checkTerm ty linCtx
      checkTerm tail linCtx

    | .record fields =>
      for (_, t) in fields do
        checkTerm t linCtx

    | .recordUpdate base updates =>
      checkTerm base linCtx
      for (_, t) in updates do
        checkTerm t linCtx

    | .fieldAccess e _ _ => checkTerm e linCtx

    | .inject _ args _ =>
      for arg in args do
        checkTerm arg linCtx

    | .construct _ _ args _ =>
      for arg in args do
        checkTerm arg linCtx

    | .«case» scruts _ arms =>
      for scrut in scruts do
        checkTerm scrut linCtx

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
            checkTerm armBody linCtx
        | none =>
          checkTerm armBody linCtx

    | .closure _ caps _ =>
      for cap in caps do
        checkTerm cap linCtx

    | .array elements _ =>
      for e in elements do
        checkTerm e linCtx

    | .tuple elements =>
      for e in elements do
        checkTerm e linCtx

    | .dataTy _ params =>
      for p in params do
        checkTerm p linCtx

    | .ann expr ty =>
      checkTerm expr linCtx
      checkTerm ty linCtx

/-- Verify all recursive calls are well-founded -/
def verifyRecursiveCalls (fnInfo : FunctionInfo) : TermM Bool := do
  let s ← TermM.getState
  let mut allOk := true

  for call in s.recursiveCalls do
    match call.decrease with
    | .arg _ _ => pure ()
    | .lex _ => pure ()
    | .linear _ => pure ()
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

end Soma.Dependent.Totality
