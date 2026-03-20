import Soma.Project.Module
import Std.Data.HashMap
import Std.Data.HashSet

namespace Soma.Project

open Soma.Syntax

/-- A graph of modules keyed by their qualified name -/
abbrev ModuleGraph := Std.HashMap String ModuleInfo

/-- An edge in the dependency graph: target module and the import span that created it -/
structure ImportEdge where
  targetModule : String
  importSpan : Span
  deriving Repr, BEq

/-- A dependency graph: module name → list of imports with spans -/
abbrev DependencyGraph := Std.HashMap String (Array ImportEdge)

/-- A cycle in the dependency graph with span information -/
structure DependencyCycle where
  /-- Modules involved in the cycle -/
  modules : Array String
  /-- Import edges forming the cycle (at least one per module in cycle) -/
  imports : Array ImportEdge
  deriving Repr

/-- Result of topological sort -/
inductive TopoSortResult where
  /-- Successfully sorted modules in dependency order -/
  | sorted (order : Array String)
  /-- Found one or more cycles with import span information -/
  | cycles (cycles : Array DependencyCycle)
  deriving Repr

/-- Convert a QualName to a module path string (/ filesystem layout) -/
def qualNameToModulePath (qn : QualName) : String :=
  if qn.path.isEmpty then qn.name
  else String.intercalate "/" qn.path.toList ++ "/" ++ qn.name

/-- Extract the list of imports with their spans from a module's AST -/
def extractImports (ast : Module) : Array ImportEdge :=
  ast.decls.filterMap fun decl =>
    match decl with
    | .use _ path _ span => some { targetModule := qualNameToModulePath path, importSpan := span }
    | _ => none

/-- Build a dependency graph from a module graph -/
def buildDependencyGraph (modules : ModuleGraph) : DependencyGraph :=
  modules.fold (init := {}) fun acc name info =>
    acc.insert name (extractImports info.ast)

/-- State for Tarjan's SCC algorithm -/
private structure TarjanState where
  index : Nat
  stack : Array String
  onStack : Std.HashMap String Bool
  indices : Std.HashMap String Nat
  lowlinks : Std.HashMap String Nat
  sccs : Array (Array String)

/-- Tarjan's strongly connected components algorithm -/
private partial def tarjanSCC (graph : DependencyGraph) : Array (Array String) :=
  let nodes := graph.toArray.map (·.1)
  let initState : TarjanState := {
    index := 0
    stack := #[]
    onStack := {}
    indices := {}
    lowlinks := {}
    sccs := #[]
  }
  let finalState := nodes.foldl (init := initState) fun state node =>
    if state.indices.contains node then state
    else strongConnect graph node state
  finalState.sccs
where
  strongConnect (graph : DependencyGraph) (v : String) (state : TarjanState) : TarjanState :=
    let state := { state with
      indices := state.indices.insert v state.index
      lowlinks := state.lowlinks.insert v state.index
      index := state.index + 1
      stack := state.stack.push v
      onStack := state.onStack.insert v true
    }

    let successors := graph.get? v |>.getD #[]
    let state := successors.foldl (init := state) fun state edge =>
      let w := edge.targetModule
      if !state.indices.contains w then
        let state := strongConnect graph w state
        let vLow := state.lowlinks.get? v |>.getD 0
        let wLow := state.lowlinks.get? w |>.getD 0
        { state with lowlinks := state.lowlinks.insert v (min vLow wLow) }
      else if state.onStack.get? w |>.getD false then
        let vLow := state.lowlinks.get? v |>.getD 0
        let wIdx := state.indices.get? w |>.getD 0
        { state with lowlinks := state.lowlinks.insert v (min vLow wIdx) }
      else
        state

    let vIdx := state.indices.get? v |>.getD 0
    let vLow := state.lowlinks.get? v |>.getD 0
    if vLow == vIdx then
      let rec popScc (stack : Array String) (scc : Array String) (onStack : Std.HashMap String Bool) :=
        match stack.back? with
        | none => (stack, scc, onStack)
        | some w =>
          let stack' := stack.pop
          let scc' := scc.push w
          let onStack' := onStack.insert w false
          if w == v then (stack', scc', onStack')
          else popScc stack' scc' onStack'
      let (stack', scc, onStack') := popScc state.stack #[] state.onStack
      { state with
        stack := stack'
        onStack := onStack'
        sccs := state.sccs.push scc
      }
    else
      state

/-- Check if an SCC represents a cycle (has >1 node, or self-loop) -/
private def isCyclicSCC (graph : DependencyGraph) (scc : Array String) : Bool :=
  if scc.size > 1 then true
  else match scc[0]? with
    | none => false
    | some node =>
      let deps := graph.get? node |>.getD #[]
      deps.any (·.targetModule == node)

/-- Extract import edges that participate in a cycle -/
private def extractCycleImports (graph : DependencyGraph) (scc : Array String) : Array ImportEdge :=
  let sccSet : Std.HashSet String := scc.foldl (init := {}) (·.insert ·)
  scc.foldl (init := #[]) fun acc moduleName =>
    let imports := graph.get? moduleName |>.getD #[]
    let cycleImports := imports.filter fun edge => sccSet.contains edge.targetModule
    acc ++ cycleImports

/-- Topologically sort modules, detecting cycles.-/
def topoSortModules (graph : DependencyGraph) : TopoSortResult :=
  let sccs := tarjanSCC graph
  let cyclicSccs := sccs.filter (isCyclicSCC graph)
  if cyclicSccs.isEmpty then
    -- Tarjan produces SCCs in reverse topological order of the condensation graph,
    -- which means dependencies come first (leaves of the dependency graph are output first)
    .sorted (sccs.map fun scc => scc[0]!)
  else
    let cycles := cyclicSccs.map fun scc =>
      { modules := scc, imports := extractCycleImports graph scc : DependencyCycle }
    .cycles cycles

/-- Find all modules in a directory tree. -/
partial def findModules (packageName : String) (rootDir : System.FilePath) : IO (Array (String × System.FilePath)) := do
  go "" rootDir
where
  extendPath (pfx name : String) : String :=
    if pfx.isEmpty then name
    else pfx ++ "/" ++ name

  go (pfx : String) (dir : System.FilePath) : IO (Array (String × System.FilePath)) := do
    let entries ← dir.readDir
    let results ← entries.foldlM (init := #[]) fun acc entry => do
      let fullPath := entry.path
      let name := entry.fileName
      if ← fullPath.isDir then
        let subResults ← go (extendPath pfx name) fullPath
        pure (acc ++ subResults)
      else if name.endsWith ".soma" then
        let baseName := name.dropEnd 5 |>.copy
        let moduleName := packageName ++ "/" ++ extendPath pfx baseName
        pure (acc.push (moduleName, fullPath))
      else
        pure acc
    pure results

/-- The well-known prelude module name -/
def preludeModuleName : String := "stdlib/prelude"

end Soma.Project
