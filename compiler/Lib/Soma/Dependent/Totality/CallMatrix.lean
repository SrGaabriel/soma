import Soma.Dependent.Totality.Core
import Soma.Dependent.Totality.Structure

namespace Soma.Dependent.Totality

open Soma.Core

/-- A node in the call graph -/
structure CallGraphNode where
  name : String
  index : Nat
  calls : Array Nat
  deriving Inhabited

/-- The call graph of a set of functions -/
structure CallGraph where
  nodes : Array CallGraphNode
  nameToIndex : Std.HashMap String Nat
  deriving Inhabited

namespace CallGraph

def build (names : Array String) (calleesOf : Array (Array String)) : CallGraph :=
  let nameToIndex : Std.HashMap String Nat :=
    names.foldl (init := ({}, 0)) (fun (m, i) n => (m.insert n i, i + 1)) |>.1
  let nodes := names.mapIdx fun i n =>
    let callees := (calleesOf[i]?.getD #[]).filterMap (nameToIndex.get? ·)
    { name := n, index := i, calls := callees.foldl (fun acc j => acc.push j) #[] }
  { nodes, nameToIndex }

end CallGraph

/-- State for Tarjan's SCC algorithm -/
private structure TarjanState where
  index : Nat
  stack : List Nat
  onStack : Array Bool
  indices : Array (Option Nat)
  lowlinks : Array Nat
  sccs : Array (Array Nat)
  deriving Inhabited

/-- SCC in reverse topological order -/
partial def CallGraph.sccs (g : CallGraph) : Array (Array String) :=
  let n := g.nodes.size
  let initState : TarjanState := {
    index := 0, stack := [],
    onStack := (List.replicate n false).toArray,
    indices := (List.replicate n none).toArray,
    lowlinks := (List.replicate n 0).toArray,
    sccs := #[]
  }
  let finalState := (List.range n).foldl (fun st v =>
    if st.indices[v]? == some none then strongconnect g st v else st) initState
  finalState.sccs.map fun scc =>
    scc.filterMap fun idx => if h : idx < g.nodes.size then some g.nodes[idx].name else none
where
  strongconnect (g : CallGraph) (st : TarjanState) (v : Nat) : TarjanState :=
    if h : v < g.nodes.size then
      let st := { st with
        indices := st.indices.set! v (some st.index)
        lowlinks := st.lowlinks.set! v st.index
        index := st.index + 1
        stack := v :: st.stack
        onStack := st.onStack.set! v true }
      let node := g.nodes[v]
      let st := node.calls.foldl (fun s w =>
        if s.indices[w]? == some none then
          let s' := strongconnect g s w
          let newLow := min (s'.lowlinks[v]?.getD 0) (s'.lowlinks[w]?.getD 0)
          { s' with lowlinks := s'.lowlinks.set! v newLow }
        else if s.onStack[w]?.getD false then
          let newLow := min (s.lowlinks[v]?.getD 0) (s.indices[w]?.getD (some 0) |>.getD 0)
          { s with lowlinks := s.lowlinks.set! v newLow }
        else s) st
      if st.lowlinks[v]? == st.indices[v]?.bind id then
        let rec popUntil (stack : List Nat) (scc : Array Nat) (onStack : Array Bool)
            : List Nat × Array Nat × Array Bool :=
          match stack with
          | [] => ([], scc, onStack)
          | w :: rest =>
            let onStack' := onStack.set! w false
            let scc' := scc.push w
            if w == v then (rest, scc', onStack') else popUntil rest scc' onStack'
        let (stack', scc, onStack') := popUntil st.stack #[] st.onStack
        { st with stack := stack', onStack := onStack', sccs := st.sccs.push scc }
      else st
    else st

/-- A size-change graph for a single call `caller → callee` -/
structure SizeMatrix where
  caller : Nat
  callee : Nat
  entries : Std.HashMap (Prov × Prov) SizeRel := {}
  deriving Inhabited

namespace SizeMatrix

/-- Insert a relation keeping the strongest witness -/
def insert (m : SizeMatrix) (src dst : Prov) (r : SizeRel) : SizeMatrix :=
  let key := (src, dst)
  match m.entries.get? key with
  | some ex => { m with entries := m.entries.insert key (ex.join r) }
  | none => { m with entries := m.entries.insert key r }

/-- Build the size-change graph of one resolved call -/
def ofCall (paramIdx : Std.HashMap Unique Nat) (callerIdx calleeIdx : Nat)
    (callerDims calleeDims : Array Prov) (call : RawCall) : SizeMatrix :=
  let rels := callRelations paramIdx callerDims calleeDims call
  rels.foldl (init := { caller := callerIdx, callee := calleeIdx }) fun m (src, dst, r) =>
    m.insert src dst r

/-- Canonical key for set membership/fixpoint detection -/
def key (m : SizeMatrix) : String :=
  let parts := m.entries.toList.map fun ((s, d), r) =>
    let rs := match r with | .lt => "lt" | .le => "le"
    s!"{s}|{d}|{rs}"
  let sorted := (parts.toArray.qsort (· < ·)).toList
  s!"{m.caller}>{m.callee}:" ++ String.intercalate ";" sorted

/-- Sequential composition `(a → b) ; (b → c)` -/
def compose (m1 m2 : SizeMatrix) : Option SizeMatrix :=
  if m1.callee != m2.caller then none
  else
    let bySrc : Std.HashMap Prov (Array (Prov × SizeRel)) :=
      m2.entries.fold (init := {}) fun acc (b, c) r =>
        match acc.get? b with
        | some arr => acc.insert b (arr.push (c, r))
        | none => acc.insert b #[(c, r)]
    let result := m1.entries.fold (init := { caller := m1.caller, callee := m2.callee })
      fun acc (a, b) r1 =>
        match bySrc.get? b with
        | some tos => tos.foldl (fun acc (c, r2) => acc.insert a c (r1.compose r2)) acc
        | none => acc
    some result

/-- Is this graph a self-loop that is its own square -/
def isIdempotent (m : SizeMatrix) : Bool :=
  m.caller == m.callee &&
    match m.compose m with
    | some m2 => m2.key == m.key
    | none => false

/-- Does some dimension strictly descend along this loop? -/
def hasDescendingThread (m : SizeMatrix) : Bool :=
  m.entries.toList.any fun ((s, d), r) => s == d && r == .lt

end SizeMatrix

/-- Close a set of size-change graphs under composition -/
partial def sizeChangeClosure (edges : Array SizeMatrix) : Array SizeMatrix :=
  let seed : Std.HashSet String := edges.foldl (fun s m => s.insert m.key) {}
  go edges edges seed
where
  go (all frontier : Array SizeMatrix) (seen : Std.HashSet String) : Array SizeMatrix :=
    let (newOnes, seen') := Id.run do
      let mut acc : Array SizeMatrix := #[]
      let mut seen := seen
      for m1 in frontier do
        for m2 in all do
          match m1.compose m2 with
          | some m =>
            let k := m.key
            if !seen.contains k then
              seen := seen.insert k
              acc := acc.push m
          | none => pure ()
      for m1 in all do
        for m2 in frontier do
          match m1.compose m2 with
          | some m =>
            let k := m.key
            if !seen.contains k then
              seen := seen.insert k
              acc := acc.push m
          | none => pure ()
      return (acc, seen)
    if newOnes.isEmpty then all
    else go (all ++ newOnes) newOnes seen'

/-- The size-change termination decision -/
def sizeChangeTerminates (edges : Array SizeMatrix) : Bool :=
  if edges.isEmpty then true
  else
    let closure := sizeChangeClosure edges
    closure.all fun m => !m.isIdempotent || m.hasDescendingThread

end Soma.Dependent.Totality
