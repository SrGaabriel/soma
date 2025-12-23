import Soma.Project.Module
import Std.Data.HashMap

namespace Soma.Project

open Soma.Syntax

/-- A graph of modules keyed by their qualified name -/
abbrev ModuleGraph := Std.HashMap String ModuleInfo

/-- A dependency graph: module name → list of modules it imports -/
abbrev DependencyGraph := Std.HashMap String (Array String)

/-- Result of topological sort -/
inductive TopoSortResult where
  /-- Successfully sorted modules in dependency order -/
  | sorted (order : Array String)
  /-- Found one or more cycles -/
  | cycles (groups : Array (Array String))
  deriving Repr

/-- Convert a QualName to a module path string using slashes (matching findModules format) -/
def qualNameToModulePath (qn : QualName) : String :=
  if qn.path.isEmpty then qn.name
  else String.intercalate "/" qn.path.toList ++ "/" ++ qn.name

/-- Extract the list of imported module names from a module's AST -/
def extractImports (ast : Module) : Array String :=
  ast.decls.filterMap fun decl =>
    match decl with
    | .use path _ _ => some (qualNameToModulePath path)
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
    let state := successors.foldl (init := state) fun state w =>
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
      deps.contains node

/-- Topologically sort modules, detecting cycles.-/
def topoSortModules (graph : DependencyGraph) : TopoSortResult :=
  let sccs := tarjanSCC graph
  let cyclicSccs := sccs.filter (isCyclicSCC graph)
  if cyclicSccs.isEmpty then
    -- Tarjan produces SCCs in reverse topological order of the condensation graph,
    -- which means dependencies come first (leaves of the dependency graph are output first)
    .sorted (sccs.map fun scc => scc[0]!)
  else
    .cycles cyclicSccs

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
        let baseName := name.dropRight 5  -- Remove ".soma"
        let moduleName := packageName ++ "/" ++ extendPath pfx baseName
        pure (acc.push (moduleName, fullPath))
      else
        pure acc
    pure results

/-- The well-known prelude module name -/
def preludeModuleName : String := "stdlib/prelude"

/-- Inject prelude imports into all modules that need it -/
def injectPreludeIntoGraph (preludeSymbols : Array String) (graph : ModuleGraph) : ModuleGraph :=
  graph.fold (init := {}) fun acc name info =>
    if name == preludeModuleName then
      acc.insert name info
    else
      let injectedAst := injectPreludeImport preludeSymbols info.ast
      acc.insert name { info with ast := injectedAst }
where
  injectPreludeImport (symbols : Array String) (ast : Module) : Module :=
    let preludeImport : Decl := .use
      { path := #["stdlib"], name := "prelude", span := Span.uninhabited }
      (symbols.map fun s => { value := s, span := Span.uninhabited })
      Span.uninhabited
    { ast with decls := #[preludeImport] ++ ast.decls }

end Soma.Project
