import Soma.Dependent.Totality.Core
import Soma.Dependent.Totality.Structure
import Soma.Dependent.Totality.CallMatrix
import Soma.Dependent.Totality.LinArith
import Soma.Core.Expr

namespace Soma.Dependent.Totality

open Soma.Core
open Soma (Unique)

/-- A function prepared for component analysis -/
structure PreparedFn where
  info : FunctionInfo
  body : Expr
  analysis : FnAnalysis
  paramIdx : Std.HashMap Unique Nat
  deriving Inhabited

/-- Map a parameter unique-id array to a position index -/
def mkParamIdx (params : Array Unique) : Std.HashMap Unique Nat :=
  params.foldl (init := ({}, 0)) (fun (m, i) u => (m.insert u i, i + 1)) |>.1

/-- Analyze one function up-front (dimensions + every call to any group member) -/
def prepareFunction (info : FunctionInfo) (allTargets : Std.HashSet String) (body : Expr)
    : PreparedFn :=
  { info, body
    analysis := analyzeFunction info.paramIds allTargets body
    paramIdx := mkParamIdx info.paramIds }

/-- Build the size-change graphs for every call internal to a component and run the termination test -/
def structuralTerminates (group : Array PreparedFn) : Bool :=
  let idxOf : Std.HashMap String Nat :=
    group.foldl (init := ({}, 0)) (fun (m, i) pf => (m.insert pf.info.name.display i, i + 1)) |>.1
  let edges : Array SizeMatrix := Id.run do
    let mut es : Array SizeMatrix := #[]
    for i in [:group.size] do
      let pf := group[i]!
      for call in pf.analysis.calls do
        match idxOf.get? call.callee with
        | some j =>
          if hj : j < group.size then
            es := es.push (SizeMatrix.ofCall pf.paramIdx i j pf.analysis.dims group[j].analysis.dims call)
        | none => pure ()
    return es
  sizeChangeTerminates edges

/-- A recursive call captured with its guard context for the linear measure -/
private structure GuardedCall where
  args : List Expr
  ctx : LinCtx
  deriving Inhabited

/-- Collect self-calls of `target` together with the path-condition context that holds at each call site -/
private partial def collectGuardedCalls (target : String) (params : Array String)
    (ctx : LinCtx) (e : Expr) (acc : Array GuardedCall) : Array GuardedCall :=
  let collectSpine (e : Expr) : Expr × List Expr :=
    let rec go (e : Expr) (as : List Expr) : Expr × List Expr :=
      match e with
      | .app fn arg => go fn (arg :: as)
      | _ => (e, as)
    go e []
  match e with
  | .app _ _ =>
    let (head, args) := collectSpine e
    let acc := match head with
      | .const name _ => if name.display == target then acc.push { args, ctx } else acc
      | _ => collectGuardedCalls target params ctx head acc
    args.foldl (fun a arg => collectGuardedCalls target params ctx arg a) acc
  | .const name _ =>
    if name.display == target then acc.push { args := [], ctx } else acc
  | .if_ c t el =>
    let acc := collectGuardedCalls target params ctx c acc
    let atom? := analyzeCondAtom c params
    let thenCtx := match atom? with | some a => ctx.addAtom a | none => ctx
    let elseCtx := match atom? with | some a => ctx.addAtom a.negate | none => ctx
    let acc := collectGuardedCalls target params thenCtx t acc
    collectGuardedCalls target params elseCtx el acc
  | .lam _ _ d b =>
    collectGuardedCalls target params ctx b (collectGuardedCalls target params ctx d acc)
  | .let_ _ t v b =>
    let acc := collectGuardedCalls target params ctx t acc
    let acc := collectGuardedCalls target params ctx v acc
    collectGuardedCalls target params ctx b acc
  | .«case» scruts _ arms =>
    let acc := scruts.foldl (fun a s => collectGuardedCalls target params ctx s a) acc
    arms.foldl (fun a arm => collectGuardedCalls target params ctx arm.body a) acc
  | .construct _ _ args _ => args.foldl (fun a x => collectGuardedCalls target params ctx x a) acc
  | .inject _ args _ => args.foldl (fun a x => collectGuardedCalls target params ctx x a) acc
  | .fieldAccess x _ _ => collectGuardedCalls target params ctx x acc
  | .ann x t => collectGuardedCalls target params ctx t (collectGuardedCalls target params ctx x acc)
  | .record fields => fields.foldl (fun a (_, x) => collectGuardedCalls target params ctx x a) acc
  | .recordUpdate base updates =>
    let acc := collectGuardedCalls target params ctx base acc
    updates.foldl (fun a (_, x) => collectGuardedCalls target params ctx x a) acc
  | .array elems _ => elems.foldl (fun a x => collectGuardedCalls target params ctx x a) acc
  | .tuple elems => elems.foldl (fun a x => collectGuardedCalls target params ctx x a) acc
  | .closure _ captures _ => captures.foldl (fun a x => collectGuardedCalls target params ctx x a) acc
  | .proj _ _ _ => acc
  | .pi _ _ _ d c => collectGuardedCalls target params ctx c (collectGuardedCalls target params ctx d acc)
  | .rowExtend l f t =>
    let acc := collectGuardedCalls target params ctx l acc
    let acc := collectGuardedCalls target params ctx f acc
    collectGuardedCalls target params ctx t acc
  | .recordTy r => collectGuardedCalls target params ctx r acc
  | .variantTy r => collectGuardedCalls target params ctx r acc
  | .dataTy _ ps => ps.foldl (fun a x => collectGuardedCalls target params ctx x a) acc
  | .bvar _ | .fvar _ _ | .mvar _ | .tyvar _ _ | .lit _ | .sort _
  | .rowSort | .labelSort | .rowEmpty | .labelLit _ | .panic _ => acc

/-- Try to prove a single (non-mutual) function terminates -/
def numericTerminates (pf : PreparedFn) : Option String :=
  let params := pf.info.params
  let arity := params.size
  let calls := collectGuardedCalls pf.info.name.display params LinCtx.empty pf.body #[]
  if calls.isEmpty then none
  else
    let pairs : List (Nat × Nat) :=
      (List.range arity).flatMap fun i =>
        (List.range arity).filterMap fun j => if i == j then none else some (i, j)
    pairs.findSome? fun (i, j) =>
      let measure := (LinForm.ofParam j).sub (LinForm.ofParam i)
      let okForAll := calls.all fun c =>
        let argArr := c.args.toArray
        match (argArr[i]?.bind (analyzeLinForm · params)),
              (argArr[j]?.bind (analyzeLinForm · params)) with
        | some argI, some argJ =>
          let afterCall := argJ.sub argI
          entailsNonneg c.ctx measure && entailsNonneg c.ctx ((measure.sub afterCall).sub (LinForm.ofConst 1))
        | _, _ => false
      if okForAll then some s!"linear measure {measure.toDisplay}" else none

/-- Outcome of checking one strongly-connected component -/
structure SccVerdict where
  ok : Bool
  reason : String
  deriving Inhabited

/-- Decide termination for one component -/
def checkComponent (group : Array PreparedFn) : SccVerdict :=
  if structuralTerminates group then
    { ok := true, reason := "structural recursion" }
  else if group.size == 1 then
    match numericTerminates group[0]! with
    | some why => { ok := true, reason := why }
    | none =>
      { ok := false
        reason := "no structural size-change or numeric measure decreases on every recursive call" }
  else
    { ok := false
      reason := "no shared dimension descends around every cycle" }

end Soma.Dependent.Totality
