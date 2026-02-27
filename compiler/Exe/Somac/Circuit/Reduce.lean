import Somac.Circuit.Reduce.Types
import Somac.Circuit.Reduce.Interact
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

/-- Reduce a graph in partial evaluation mode -/
def partialEval (graph : Graph) (fuel : Nat := 1000000) : IO (Graph × Stats) := do
  let (_result, state) ← ReduceM.run (do
    let _rootId ← nf (← ReduceM.getGraph).root
    pure ()
  ) graph { Config.forPartialEval with fuel }
  return (state.graph, state.stats)

/-- Build a configuration with intrinsics from the compiler's elaboration context -/
def Config.withIntrinsics (config : Config) (intrinsics : Std.HashMap String Intrinsic)
    : Config :=
  { config with intrinsics }

end Somac.Circuit.Reduce
