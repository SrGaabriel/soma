import Soma.Dependent.Totality.Core
import Soma.Dependent.Totality.TermShape
import Soma.Core.Expr

namespace Soma.Dependent.Totality

open Soma.Core
open Soma.Syntax (Span)

/-- How an argument changes in a call -/
inductive ArgChange where
  | decrease -- Strictly smaller
  | equal -- Same size
  | increase -- Larger
  | unknown -- Can't determine
  deriving Repr, BEq, Inhabited

/-- A row in the call matrix: how each argument changes for one call -/
structure CallMatrixRow where
  /-- Source function -/
  caller : String
  /-- Target function -/
  callee : String
  /-- Change for each argument position -/
  changes : Array ArgChange
  /-- Span for error reporting -/
  span : Span
  deriving Repr, Inhabited

/-- Complete call matrix for a set of mutually recursive functions -/
structure CallMatrix where
  /-- Function names in the mutual recursion group -/
  functions : Array String
  /-- Number of arguments per function (assumed same for mutual group) -/
  arity : Nat
  /-- All calls between functions -/
  rows : Array CallMatrixRow
  deriving Repr, Inhabited

namespace CallMatrix

/-- Create an empty call matrix -/
def empty (functions : Array String) (arity : Nat) : CallMatrix :=
  { functions := functions, arity := arity, rows := #[] }

/-- Add a call to the matrix -/
def addCall (m : CallMatrix) (row : CallMatrixRow) : CallMatrix :=
  { m with rows := m.rows.push row }

/-- Convert a StructuralCmp to ArgChange -/
def toArgChange : StructuralCmp → ArgChange
  | .smaller _ => .decrease
  | .equal => .equal
  | .larger => .increase
  | .unknown => .unknown

/-- Check if a call matrix row represents a decreasing call (for some argument) -/
def isDecreasing (row : CallMatrixRow) : Bool :=
  -- Lexicographic: find first position that's not equal
  let rec check (i : Nat) : Bool :=
    if h : i < row.changes.size then
      match row.changes[i] with
      | .decrease => true -- Found decrease before any increase
      | .equal => check (i + 1) -- Continue checking
      | .increase => false -- Found increase before decrease
      | .unknown => false -- Can't prove termination
    else
      false
  check 0

/-- Find a lexicographic ordering that proves termination for all calls -/
def findLexOrder (m : CallMatrix) : Option (Array Nat) :=
  if m.arity == 0 then some #[]
  else if m.arity == 1 then
    if m.rows.all fun row => row.changes[0]? == some .decrease then
      some #[0]
    else
      none
  else if m.arity == 2 then
    let order1 := #[0, 1]
    let order2 := #[1, 0]
    if checkOrder m order1 then some order1
    else if checkOrder m order2 then some order2
    else none
  else if m.arity == 3 then
    let orders := #[#[0,1,2], #[0,2,1], #[1,0,2], #[1,2,0], #[2,0,1], #[2,1,0]]
    orders.findSome? fun order =>
      if checkOrder m order then some order else none
  else
    let order := Array.range m.arity
    if checkOrder m order then some order else none
where
  /-- Check if a given ordering proves termination for all calls -/
  checkOrder (m : CallMatrix) (order : Array Nat) : Bool :=
    m.rows.all fun row =>
      let rec checkLex (i : Nat) : Bool :=
        if h : i < order.size then
          let argIdx := order[i]
          match row.changes[argIdx]? with
          | some .decrease => true
          | some .equal => checkLex (i + 1)
          | _ => false
        else
          false
      checkLex 0

/-- Verify termination using the call matrix approach -/
def verifyTermination (m : CallMatrix) : Option String :=
  if m.rows.isEmpty then
    some "no recursive calls"
  else
    match findLexOrder m with
    | some order =>
      let orderStr := order.toList.map toString |> String.intercalate ", "
      some s!"lexicographic order [{orderStr}] proves termination"
    | none =>
      none

end CallMatrix

/-- A node in the call graph -/
structure CallGraphNode where
  name : String
  index : Nat
  calls : Array (String × CallMatrixRow)  -- (callee, call info)
  deriving Repr, Inhabited

/-- A call graph for a set of functions -/
structure CallGraph where
  nodes : Array CallGraphNode
  nameToIndex : Std.HashMap String Nat
  deriving Inhabited

namespace CallGraph

/-- Create an empty call graph -/
def empty : CallGraph :=
  { nodes := #[], nameToIndex := {} }

/-- Add a node to the graph -/
def addNode (g : CallGraph) (name : String) : CallGraph :=
  if g.nameToIndex.contains name then g
  else
    let idx := g.nodes.size
    let node : CallGraphNode := { name := name, index := idx, calls := #[] }
    { nodes := g.nodes.push node, nameToIndex := g.nameToIndex.insert name idx }

/-- Add a call edge to the graph -/
def addCall (g : CallGraph) (caller callee : String) (row : CallMatrixRow) : CallGraph :=
  match g.nameToIndex.get? caller with
  | some idx =>
    if h : idx < g.nodes.size then
      let node := g.nodes[idx]
      let node' := { node with calls := node.calls.push (callee, row) }
      { g with nodes := g.nodes.set idx node' }
    else g
  | none => g

end CallGraph

/-- State for Tarjan's SCC algorithm -/
structure TarjanState where
  index : Nat
  stack : List Nat
  onStack : Array Bool
  indices : Array (Option Nat)
  lowlinks : Array Nat
  sccs : Array (Array Nat)
  deriving Inhabited

/-- Find SCCs using Tarjan's algorithm -/
partial def findSCCs (g : CallGraph) : Array (Array String) :=
  let n := g.nodes.size
  let initState : TarjanState := {
    index := 0
    stack := []
    onStack := (List.replicate n false).toArray
    indices := (List.replicate n none).toArray
    lowlinks := (List.replicate n 0).toArray
    sccs := #[]
  }

  let finalState := (List.range n).foldl (fun st v =>
    if st.indices[v]? == some none then
      strongconnect g st v
    else st
  ) initState

  finalState.sccs.map fun scc =>
    scc.filterMap fun idx =>
      if h : idx < g.nodes.size then some g.nodes[idx].name else none
where
  strongconnect (g : CallGraph) (st : TarjanState) (v : Nat) : TarjanState :=
    if h : v < g.nodes.size then
      let st := { st with
        indices := st.indices.set! v (some st.index)
        lowlinks := st.lowlinks.set! v st.index
        index := st.index + 1
        stack := v :: st.stack
        onStack := st.onStack.set! v true
      }

      let node := g.nodes[v]
      let st := node.calls.foldl (fun s (callee, _) =>
        match g.nameToIndex.get? callee with
        | some w =>
          if s.indices[w]? == some none then
            let s' := strongconnect g s w
            let newLowlink := min (s'.lowlinks[v]?.getD 0) (s'.lowlinks[w]?.getD 0)
            { s' with lowlinks := s'.lowlinks.set! v newLowlink }
          else if s.onStack[w]?.getD false then
            let newLowlink := min (s.lowlinks[v]?.getD 0) (s.indices[w]?.getD (some 0) |>.getD 0)
            { s with lowlinks := s.lowlinks.set! v newLowlink }
          else s
        | none => s
      ) st

      if st.lowlinks[v]? == st.indices[v]?.bind id then
        let rec popUntil (stack : List Nat) (scc : Array Nat) (onStack : Array Bool)
            : List Nat × Array Nat × Array Bool :=
          match stack with
          | [] => ([], scc, onStack)
          | w :: rest =>
            let onStack' := onStack.set! w false
            let scc' := scc.push w
            if w == v then (rest, scc', onStack')
            else popUntil rest scc' onStack'
        let (stack', scc, onStack') := popUntil st.stack #[] st.onStack
        { st with stack := stack', onStack := onStack', sccs := st.sccs.push scc }
      else st
    else st

/-- A termination matrix for a mutual recursion group -/
structure TermMatrix where
  size : Nat                           -- Number of functions
  arity : Nat                          -- Number of arguments
  entries : Array (Array ArgChange)    -- size × size matrix of argument changes
  deriving Repr, Inhabited

namespace TermMatrix

/-- Create an identity-like matrix (all equal on diagonal) -/
def identity (size arity : Nat) : TermMatrix :=
  let entries := Array.range size |>.map fun i =>
    Array.range size |>.map fun j =>
      if i == j then .equal else .unknown
  { size := size, arity := arity, entries := entries }

/-- Get entry at (i, j) -/
def get (m : TermMatrix) (i j : Nat) : ArgChange :=
  if h1 : i < m.entries.size then
    let row := m.entries[i]
    if h2 : j < row.size then row[j]
    else .unknown
  else .unknown

/-- Compose two argument changes (for matrix multiplication) -/
def composeChange (c1 c2 : ArgChange) : ArgChange :=
  match c1, c2 with
  | .decrease, .decrease => .decrease
  | .decrease, .equal => .decrease
  | .equal, .decrease => .decrease
  | .equal, .equal => .equal
  | .increase, _ => .increase
  | _, .increase => .increase
  | .unknown, _ => .unknown
  | _, .unknown => .unknown

/-- Best of two changes (for taking minimum in path) -/
def bestChange (c1 c2 : ArgChange) : ArgChange :=
  match c1, c2 with
  | .decrease, _ => .decrease
  | _, .decrease => .decrease
  | .equal, .equal => .equal
  | .equal, .unknown => .equal
  | .unknown, .equal => .equal
  | .increase, .increase => .increase
  | _, _ => .unknown

/-- Multiply two termination matrices -/
def multiply (m1 m2 : TermMatrix) : TermMatrix :=
  let entries := Array.range m1.size |>.map fun i =>
    Array.range m2.size |>.map fun j =>
      let changes := Array.range m1.size |>.map fun k =>
        composeChange (m1.get i k) (m2.get k j)
      changes.foldl bestChange .unknown
  { size := m1.size, arity := m1.arity, entries := entries }

/-- Compute transitive closure (matrix^*) -/
partial def transitiveClosure (m : TermMatrix) : TermMatrix :=
  go m m
where
  go (current acc : TermMatrix) : TermMatrix :=
    let next := multiply current current
    let acc' := combineMatrices acc next
    if matrixEqual acc acc' then acc'
    else go next acc'

  combineMatrices (m1 m2 : TermMatrix) : TermMatrix :=
    let entries := Array.range m1.size |>.map fun i =>
      Array.range m1.size |>.map fun j =>
        bestChange (m1.get i j) (m2.get i j)
    { size := m1.size, arity := m1.arity, entries := entries }

  matrixEqual (m1 m2 : TermMatrix) : Bool :=
    m1.entries == m2.entries

/-- Check if all diagonal entries show decrease (all cycles terminate) -/
def allCyclesDecrease (m : TermMatrix) : Bool :=
  Array.range m.size |>.all fun i =>
    match m.get i i with
    | .decrease => true
    | _ => false

end TermMatrix

/-- Build a termination matrix from a call graph -/
def buildTermMatrix (g : CallGraph) : TermMatrix :=
  let size := g.nodes.size
  let entries := Array.range size |>.map fun i =>
    Array.range size |>.map fun j =>
      if h : i < g.nodes.size then
        let node := g.nodes[i]
        let callsToJ := node.calls.filter fun (callee, _) =>
          g.nameToIndex.get? callee == some j
        if callsToJ.isEmpty then .unknown
        else
          callsToJ.foldl (fun best (_, row) =>
            if row.changes.any (· == .decrease) then .decrease
            else if row.changes.all (· == .equal) then TermMatrix.bestChange best .equal
            else best
          ) .unknown
      else .unknown
  { size := size, arity := 0, entries := entries }

/-- Analyze results from constructor arguments -/
private def analyzeConstructorArgs (results : Array StructuralCmp) (ctorName : String) : StructuralCmp :=
  let hasSmaller := results.any (·.isSmaller)
  let hasLarger := results.any fun
    | .larger => true
    | _ => false
  let hasUnknown := results.any fun
    | .unknown => true
    | _ => false
  let allEqual := results.all (·.isEqual)

  if hasLarger then
    .larger
  else if hasSmaller && !hasUnknown then
    .smaller s!"constructor '{ctorName}' uses smaller components"
  else if allEqual then
    .equal
  else if hasSmaller then
    .smaller s!"constructor '{ctorName}' has at least one smaller component"
  else
    .unknown

/-- Compare a term shape against a parameter to determine if it's smaller -/
partial def compareTermToParam (shape : TermShape) (paramIdx : Nat) (paramName : String)
    (ctx : TerminationContext) : StructuralCmp :=
  match shape with
  | .var name =>
    match ctx.lookup name with
    | some info =>
      if info.paramIdx != paramIdx then
        .unknown
      else if info.depth > 0 then
        .smaller s!"'{name}' is a subterm of '{paramName}' (depth {info.depth})"
      else
        .equal
    | none =>
      .unknown

  | .ctor ctorName args =>
    let results := args.map fun arg => compareTermToParam arg paramIdx paramName ctx
    analyzeConstructorArgs results ctorName

  | .fieldProj inner field =>
    match inner.asVar? with
    | some name =>
      match ctx.lookup name with
      | some info =>
        if info.paramIdx == paramIdx then
          if info.depth == 0 then
            .smaller s!"'{name}.{field}' is a subterm of '{paramName}'"
          else
            .smaller s!"'{name}.{field}' is a subterm (already at depth {info.depth})"
        else
          .unknown
      | none => .unknown
    | none =>
      let innerCmp := compareTermToParam inner paramIdx paramName ctx
      if innerCmp.isSmaller || innerCmp.isEqual then
        .smaller s!"field '{field}' access on parameter component"
      else
        .unknown

  | .lit _ => .unknown
  | .app _ _ => .unknown
  | .unknown => .unknown

/-- Collect the spine of an application into (head, args) form -/
private partial def collectAppSpine (e : Soma.Core.Expr) : Soma.Core.Expr × List Soma.Core.Expr :=
  match e with
  | .app fn arg =>
    let (head, args) := collectAppSpine fn
    (head, args ++ [arg])
  | _ => (e, [])

/-- Recover if the scrutinee is a plain reference to one of the function's explicit parameters -/
private def scrutineeParam (scrut : Soma.Core.Expr) (params : Array String)
    : Option (Nat × String) :=
  let nameOpt : Option String :=
    match scrut with
    | .fvar id _ => some id.original
    | .const n _ => some n.display
    | _ => none
  nameOpt.bind fun name =>
    params.findIdx? (· == name) |>.map (·, name)

/-- Build a call matrix row from a recursive call -/
def buildRow (caller callee : String) (args : List Soma.Core.Expr) (ctx : TerminationContext)
    (span : Span) : CallMatrixRow :=
  let (changes, _) := args.foldl (init := (#[], 0)) fun (acc, idx) arg =>
    let change :=
      if h : idx < ctx.params.size then
        let paramName := ctx.params[idx]
        let shape := analyzeExprShape arg
        let cmp := compareTermToParam shape idx paramName ctx
        CallMatrix.toArgChange cmp
      else
        .unknown
    (acc.push change, idx + 1)
  { caller := caller, callee := callee, changes := changes, span := span }

/-- Collect all recursive/mutual calls in a term -/
private partial def collectCallsGo (caller : String) (targets : Array String)
    (t : Soma.Core.Expr) (ctx : TerminationContext) (acc : Array CallMatrixRow)
    : Array CallMatrixRow :=
  match t with
  | .const name _ =>
    let callee := name.display
    if targets.contains callee then
      let row : CallMatrixRow :=
        { caller := caller, callee := callee, changes := #[], span := Span.uninhabited }
      acc.push row
    else acc
  | e@(.app _ _) =>
    let (head, args) := collectAppSpine e
    match head with
    | .const name _ =>
      let callee := name.display
      if targets.contains callee then
        let row := buildRow caller callee args ctx Span.uninhabited
        collectCallsGoArgs caller targets args ctx (acc.push row)
      else
        collectCallsGoArgs caller targets args ctx acc
    | _ =>
      collectCallsGoArgs caller targets (head :: args) ctx acc
  | .lam _ _ _ body => collectCallsGo caller targets body ctx acc
  | .if_ c th el =>
    let acc' := collectCallsGo caller targets c ctx acc
    let acc'' := collectCallsGo caller targets th ctx acc'
    collectCallsGo caller targets el ctx acc''
  | .construct _ _ args _ => collectCallsGoArgs caller targets args.toList ctx acc
  | .«case» scruts _ arms =>
    let acc' := match scruts[0]? with
      | some s => collectCallsGo caller targets s ctx acc
      | none => acc
    let paramInfo := scruts[0]?.bind fun s => scrutineeParam s ctx.params
    arms.toList.foldl (fun a arm =>
      let ctx' :=
        match paramInfo with
        | some (pIdx, pName) =>
          let usedVars := collectExprVars arm.body
          let newVars := usedVars.filter fun v => !ctx.params.contains v
          let patName := match arm.patterns[0]? with
            | some (Soma.Core.Pattern.ctor name _ _) => name.display
            | _ => "_"
          let bs : Array BindingInfo := newVars.toArray.map fun name =>
            { name := name
              paramIdx := pIdx
              paramName := pName
              path := .ctorArg .root patName 0
              depth := 1 }
          ctx.addBindings bs
        | none => ctx
      collectCallsGo caller targets arm.body ctx' a) acc'
  | .record fields =>
    fields.toList.foldl (fun a (_, v) => collectCallsGo caller targets v ctx a) acc
  | .fieldAccess e _ _ => collectCallsGo caller targets e ctx acc
  | .pi _ _ _ d c =>
    let acc' := collectCallsGo caller targets d ctx acc
    collectCallsGo caller targets c ctx acc'
  | .eqTy _ ty l r =>
    let acc' := collectCallsGo caller targets ty ctx acc
    let acc'' := collectCallsGo caller targets l ctx acc'
    collectCallsGo caller targets r ctx acc''
  | .refl ty x =>
    let acc' := collectCallsGo caller targets ty ctx acc
    collectCallsGo caller targets x ctx acc'
  | .transport _ ty m l r eq b =>
    let acc' := collectCallsGo caller targets ty ctx acc
    let acc'' := collectCallsGo caller targets m ctx acc'
    let acc''' := collectCallsGo caller targets l ctx acc''
    let acc'''' := collectCallsGo caller targets r ctx acc'''
    let acc''''' := collectCallsGo caller targets eq ctx acc''''
    collectCallsGo caller targets b ctx acc'''''
  | .rowExtend l ty tail =>
    let acc' := collectCallsGo caller targets l ctx acc
    let acc'' := collectCallsGo caller targets ty ctx acc'
    collectCallsGo caller targets tail ctx acc''
  | .recordTy r => collectCallsGo caller targets r ctx acc
  | .variantTy r => collectCallsGo caller targets r ctx acc
  | _ => acc
where
  collectCallsGoArgs (caller : String) (targets : Array String)
      (args : List Soma.Core.Expr) (ctx : TerminationContext) (acc : Array CallMatrixRow)
      : Array CallMatrixRow :=
    args.foldl (fun a arg => collectCallsGo caller targets arg ctx a) acc

/-- Collect all recursive/mutual calls in a term -/
def collectCalls (caller : String) (targets : Array String) (t : Soma.Core.Expr)
    (ctx : TerminationContext) : Array CallMatrixRow :=
  collectCallsGo caller targets t ctx #[]

/-- Build a call matrix for mutual recursion -/
def buildCallMatrix (functions : Array FunctionInfo) (bodies : Array Soma.Core.Expr)
    : CallMatrix :=
  let names := functions.map (·.name.display)
  let arity := if functions.isEmpty then 0
               else functions[0]!.params.size
  let initial := CallMatrix.empty names arity

  let (result, _) := functions.foldl (init := (initial, 0)) fun (matrix, i) fnInfo =>
    if h : i < bodies.size then
      let body := bodies[i]
      let ctx := TerminationContext.fromParams fnInfo.params
      let calls := collectCalls fnInfo.name.display names body ctx
      let matrix' := calls.foldl (fun m call => m.addCall call) matrix
      (matrix', i + 1)
    else
      (matrix, i + 1)
  result

/-- Build a call graph from function info and bodies -/
def buildCallGraph (functions : Array FunctionInfo) (bodies : Array Soma.Core.Expr) : CallGraph :=
  let names := functions.map (·.name.display)
  let g := names.foldl (fun acc name => acc.addNode name) CallGraph.empty
  let (g', _) := functions.foldl (init := (g, 0)) fun (graph, i) fnInfo =>
    if h : i < bodies.size then
      let body := bodies[i]
      let ctx := TerminationContext.fromParams fnInfo.params
      let calls := collectCalls fnInfo.name.display names body ctx
      let graph' := calls.foldl (fun gr row => gr.addCall row.caller row.callee row) graph
      (graph', i + 1)
    else
      (graph, i + 1)
  g'

/-- Check termination using matrix analysis -/
def checkMatrixTermination (functions : Array FunctionInfo) (bodies : Array Soma.Core.Expr)
    : Bool × String :=
  let graph := buildCallGraph functions bodies
  let matrix := buildTermMatrix graph
  let closure := matrix.transitiveClosure

  if closure.allCyclesDecrease then
    (true, "matrix analysis proves termination")
  else
    let sccs := findSCCs graph
    let allSccsOk := sccs.all fun scc =>
      if scc.size <= 1 then true
      else
        scc.all fun fn =>
          match graph.nameToIndex.get? fn with
          | some idx => closure.get idx idx == .decrease
          | none => true

    if allSccsOk then
      (true, "SCC analysis proves termination")
    else
      (false, "cannot prove termination via matrix analysis")

end Soma.Dependent.Totality
