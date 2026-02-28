import Somac.Circuit.Reduce.Types
import Somac.Circuit.Reduce.Nf
import Somac.Circuit.Reduce.Readback
import Somac.Circuit.Graph
import Somac.Circuit.Node
import Soma.Core.Intrinsic

namespace Somac.Circuit.Reduce

open Somac.Circuit.Graph (Graph)
open Somac.Circuit.Node (NodeId PortId)
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

/-- Run one pass of partial evaluation over all definitions -/
private def partialEvalPass (graph : Graph) (fuel : Nat) : IO (Graph × Stats) := do
  let (result, state) ← ReduceM.run (do
    let g ← ReduceM.getGraph
    for i in [:g.book.size] do
      let g' ← ReduceM.getGraph
      if let some def_ := g'.book[i]? then
        if !def_.isExternal then
          -- Wire a temporary ERA as demand endpoint to the definition root
          let era ← ReduceM.addNode .era
          ReduceM.connect (PortId.principal era) (PortId.principal def_.root)
          -- Normalize the definition's subgraph
          let resultId ← nf (PortId.principal era)
          -- Update the definition root if it changed
          if resultId != def_.root then
            ReduceM.updateDefinitionRoot i resultId
          -- Clean up the temporary demand node
          ReduceM.disconnect (PortId.principal era)
          ReduceM.removeNode era
  ) graph { Config.forPartialEval with fuel }
  match result with
  | .ok _ => return (state.graph, state.stats)
  | .error _ => return (state.graph, state.stats)

/-- Partially evaluate each definition in the graph's book -/
def partialEval (graph : Graph) (fuel : Nat := 1000000) (maxPasses : Nat := 8)
    : IO (Graph × Stats) := do
  let mut g := graph
  let mut totalStats : Stats := {}
  let mut remainingFuel := fuel
  for _ in [:maxPasses] do
    if remainingFuel == 0 then break
    let (g', passStats) ← partialEvalPass g remainingFuel
    totalStats := totalStats.merge passStats
    if passStats.totalSteps == 0 then
      g := g'
      break
    remainingFuel := remainingFuel - (min passStats.totalSteps remainingFuel)
    g := g'
  let (compacted, _) := g.sweep
  return (compacted, totalStats)

/-- Build a configuration with intrinsics from the compiler's elaboration context -/
def Config.withIntrinsics (config : Config) (intrinsics : Std.HashMap String Intrinsic)
    : Config :=
  { config with intrinsics }

end Somac.Circuit.Reduce
