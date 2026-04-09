import Somac.Circuit.Reduce.Types
import Somac.Circuit.Reduce.Nf
import Somac.Circuit.Reduce.Readback
import Somac.Circuit.Graph
import Somac.Circuit.Lower
import Somac.Circuit.Node
import Soma.Core.Intrinsic

namespace Somac.Circuit.Reduce

open Somac.Circuit.Graph (Graph NodeEntry Reducibility)
open Somac.Circuit.Node (Node NodeId PortId)
open Soma.Core (Intrinsic)

/-- Result of a reduction: the final value plus statistics -/
structure ReduceResult where
  /-- The reduced value -/
  value : ReadbackValue
  /-- Reduction statistics -/
  stats : Stats
  /-- The modified graph after reduction -/
  graph : Graph
  deriving Inhabited

instance : ToString ReduceResult where
  toString r := s!"{r.value}\n\n{r.stats}"

/-- Reduce a graph to weak head normal form from its root, then read back the result -/
def reduce (graph : Graph) (config : Config := .forPartialEval) : IO ReduceResult := do
  let (result, state) ← ReduceM.run (do
    let _rootId ← whnf (← ReduceM.getGraph).root
    readbackRoot
  ) graph config
  match result with
  | .ok value => return { value, stats := state.stats, graph := state.graph }
  | .error _e => return {
      value := .stuck (.stuckApplication ⟨0⟩)
      stats := state.stats
      graph := state.graph
    }

/-- Reduce a graph to full normal form from its root, then read back the result -/
def reduceNF (graph : Graph) (config : Config := .forPartialEval) : IO ReduceResult := do
  let (result, state) ← ReduceM.run (do
    let _rootId ← nf (← ReduceM.getGraph).root
    readbackRoot
  ) graph config
  match result with
  | .ok value => return { value, stats := state.stats, graph := state.graph }
  | .error _e => return {
      value := .stuck (.stuckApplication ⟨0⟩)
      stats := state.stats
      graph := state.graph
    }

/-- Reduce a graph and return just the value (discarding stats and graph) -/
def eval (graph : Graph) (config : Config := .forPartialEval) : IO ReadbackValue := do
  let result ← reduce graph config
  return result.value

/-- Reduce a graph in total evaluation mode (executing IO) -/
def interpret (graph : Graph) (fuel : Nat := 1000000) : IO ReduceResult :=
  reduce graph { Config.forTotalEval with fuel }

/-- Compute a dependency-ordered processing sequence for definitions -/
private def defProcessingOrder (g : Graph) : Array Nat := Id.run do
  let n := g.book.size
  if n == 0 then return #[]
  let mut depCount : Array Nat := Array.mk (List.replicate n 0)
  let mut rdeps : Array (Array Nat) := Array.mk (List.replicate n #[])
  for i in [:n] do
    if let some def_ := g.book[i]? then
      if !def_.reducibility != .reducible then
        let reachable := g.reachableFrom (PortId.principal def_.root)
        let mut seen : Std.HashSet Nat := {}
        for nid in reachable do
          if let some entry := g.getNode nid then
            match entry.node with
            | .alo refId | .ref refId =>
              if refId != i && refId < n && !seen.contains refId then
                seen := seen.insert refId
                depCount := depCount.set! i (depCount[i]! + 1)
                rdeps := rdeps.set! refId (rdeps[refId]!.push i)
            | _ => ()
  let mut queue : Array Nat := #[]
  for i in [:n] do
    if depCount[i]! == 0 then queue := queue.push i
  let mut result : Array Nat := #[]
  let mut qi := 0
  for _ in [:n] do
    if qi >= queue.size then break
    let cur := queue[qi]!
    qi := qi + 1
    result := result.push cur
    for dependent in rdeps[cur]! do
      let newCount := depCount[dependent]! - 1
      depCount := depCount.set! dependent newCount
      if newCount == 0 then
        queue := queue.push dependent
  if result.size < n then
    let mut inResult : Std.HashSet Nat := {}
    for i in result do inResult := inResult.insert i
    for i in [:n] do
      if !inResult.contains i then result := result.push i
  result

/-- Run one pass of partial evaluation over all definitions -/
private def partialEvalPass (graph : Graph) (fuel : Nat)
    (abbrevEnv : Soma.Dependent.AbbrevEnv := {}) : IO (Graph × Stats) := do
  let order := defProcessingOrder graph
  let mut g := graph
  let mut stats : Stats := {}
  for i in order do
    if let some def_ := g.book[i]? then
      if !def_.reducibility != .reducible then
        -- IO-typed definitions are only reduced to WHNF not full NF (TODO)
        let unfoldedTy := Somac.Circuit.Lower.unfoldValue def_.ty abbrevEnv
        let isIO := false
        let (result, state) ← ReduceM.run (do
          let era ← ReduceM.addNode .era
          ReduceM.connect (PortId.principal era) (PortId.principal def_.root)
          ReduceM.addNormalizingDef i
          let resultId ← if isIO then whnf (PortId.principal era) else nf (PortId.principal era)
          ReduceM.removeNormalizingDef i
          if resultId != def_.root then
            ReduceM.updateDefinitionRoot i resultId
          ReduceM.disconnect (PortId.principal era)
          ReduceM.removeNode era
        ) g { Config.forPartialEval with fuel }
        match result with
        | .ok _ =>
          g := state.graph
          stats := stats.merge state.stats
        | .error _ =>
          stats := stats.merge state.stats
  return (g, stats)

/-- Partially evaluate each definition in the graph's book -/
def partialEval (graph : Graph) (fuel : Nat := 1000000) (maxPasses : Nat := 8)
    (abbrevEnv : Soma.Dependent.AbbrevEnv := {}) : IO (Graph × Stats) := do
  let mut g := graph
  let mut totalStats : Stats := {}
  let mut remainingFuel := fuel
  for _ in [:maxPasses] do
    if remainingFuel == 0 then break
    let (g', passStats) ← partialEvalPass g remainingFuel abbrevEnv
    totalStats := totalStats.merge passStats
    if passStats.totalSteps == 0 then
      g := g'
      break
    remainingFuel := remainingFuel - (min passStats.totalSteps remainingFuel)
    let (swept, _) := g'.sweep
    g := swept
  let (compacted, _) := g.sweep
  return (compacted, totalStats)

/-- Build a configuration with intrinsics from the compiler's elaboration context -/
def Config.withIntrinsics (config : Config) (intrinsics : Std.HashMap String Intrinsic)
    : Config :=
  { config with intrinsics }

end Somac.Circuit.Reduce
