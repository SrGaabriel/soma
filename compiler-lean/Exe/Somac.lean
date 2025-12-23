import Cli
import Soma.Driver.Options
import Soma.Syntax
import Soma.Metal
import Soma.Logging
import Soma.Project
import Soma.Project.Check
import Somac.Build

open Cli
open Soma.Check (parseOnly toAst toMetal fullSimple)

namespace Soma.Driver

/-- Parse a dependency in the format NAME=PATH -/
def parseDep (s : String) : Except String (String × String) :=
  match s.splitOn "=" with
  | [name, path] =>
    if name.isEmpty || path.isEmpty then
      .error s!"Invalid dependency format: '{s}'. Expected NAME=PATH"
    else
      .ok (name, path)
  | _ => .error s!"Invalid dependency format: '{s}'. Expected NAME=PATH"

/-- Parse compilation mode from string -/
def parseMode (s : String) : Except String CompilationMode :=
  match s with
  | "standard" => .ok .standard
  | "graph" => .ok .graph
  | "hybrid" => .ok .hybrid
  | _ => .error s!"Unknown mode: '{s}'. Use 'standard', 'graph', or 'hybrid'"

/-- Parse output format from string -/
def parseFormat (s : String) : Except String OutputFormat :=
  match s with
  | "json" => .ok .json
  | "human" => .ok .human
  | _ => .error s!"Unknown format: '{s}'. Use 'json' or 'human'"

/-- Handler for the `lex` command -/
def runLex (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String

  -- Read the file
  let source ← IO.FS.readFile input

  -- todo: remove workaround
  let sourceFile := Syntax.SourceFile.create ⟨0⟩ input source

  -- Lex it
  let (tokens, diags) := Syntax.lexCode sourceFile

  -- Print diagnostics if any
  if diags.size > 0 then
    IO.eprintln s!"Found {diags.size} diagnostic(s):"
    for diag in diags do
      IO.eprintln s!"  {diag.severity}: {diag.message}"

  -- Print tokens
  IO.println s!"Lexed {tokens.size} tokens from {input}:"
  for tok in tokens do
    match tok.tokenKind? with
    | some kind => IO.println s!"  {kind}"
    | none => IO.println s!"  (node)"

  return if diags.size > 0 then 1 else 0

/-- Handler for the `parse` command -/
def runParse (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let showCst := p.hasFlag "cst"
  let showAst := p.hasFlag "ast"

  let content ← IO.FS.readFile input
  let (parseRes, lowerRes) := toAst input content
  let allDiags := parseRes.diagnostics ++ lowerRes.diagnostics

  if !allDiags.isEmpty then
    Logging.Error.printDiagnostics allDiags parseRes.sourceFile

  -- Show CST if requested
  if showCst then
    IO.println "=== Concrete Syntax Tree ==="
    IO.println (parseRes.tree.green.debugPrint)

  -- Show AST if requested (or by default if no flags)
  if showAst || (!showCst && !showAst) then
    IO.println "=== Abstract Syntax Tree ==="
    IO.println (Syntax.Pretty.ppModule lowerRes.ast)

  if allDiags.isEmpty then
    IO.println "\nParse successful!"
  else
    IO.eprintln ""
    IO.eprintln (Logging.Error.renderSummary allDiags)

  return if allDiags.hasErrors then 1 else 0

/-- Handler for the `lower` command - Metal HIR lowering -/
def runLower (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String

  let content ← IO.FS.readFile input
  let (parseRes, lowerRes, metalRes) := toMetal input content
  let allDiags := parseRes.diagnostics ++ lowerRes.diagnostics ++ metalRes.diagnostics

  -- Print diagnostics
  if !allDiags.isEmpty then
    Logging.Error.printDiagnostics allDiags parseRes.sourceFile

  if allDiags.hasErrors then
    IO.eprintln ""
    IO.eprintln (Logging.Error.renderSummary allDiags)
    return 1

  -- Success
  let module := metalRes.module
  let cfg : Metal.Pretty.Config := { showTypes := false, indent := 2 }
  IO.println (Metal.Pretty.ppUntypedModule cfg module)
  IO.println "\nMetal lowering successful!"
  return 0

/-- Parse dependency flags into array of (name, path) pairs -/
def parseDeps (p : Parsed) : Array (String × String) :=
  match p.flag? "dep" with
  | none => #[]
  | some flag =>
    let depStrs := flag.as! (Array String)
    depStrs.filterMap fun s =>
      match parseDep s with
      | .ok pair => some pair
      | .error _ => none

/-- Check a single .soma file -/
def checkSingleFile (opts : CheckOptions) : IO (Array Syntax.Diagnostic × Option Syntax.SourceFile) := do
  let path : System.FilePath := opts.input
  let result ← Soma.Check.fullFromFileSimple path.toString
  return (result.diagnostics, some result.sourceFile)

/-- Check a directory of .soma files -/
def checkDirectory (opts : CheckOptions) : IO (Array Syntax.Diagnostic) := do
  let rootDir : System.FilePath := opts.input
  let packageName := opts.name.getD (rootDir.fileName.getD "app")

  -- Find all modules
  let modules ← Project.findModules packageName rootDir

  -- Parse all modules
  let (parseDiags, graph) ← Somac.Build.parseModules modules

  if Syntax.Diagnostics.hasErrors parseDiags then
    return parseDiags

  let depGraph := Project.buildDependencyGraph graph

  -- Check for cycles
  match Project.topoSortModules depGraph with
  | .cycles groups =>
    let msg := s!"Cyclic imports detected: {groups.map (·.toList)}"
    return #[Syntax.Diagnostic.error msg Syntax.Span.uninhabited]

  | .sorted sortedNames =>
    -- Load external dependencies
    let externalDeps ← Somac.Build.loadExternalDependencies (opts.deps.map fun (n, p) => (n, ⟨p⟩))
    match externalDeps with
    | .error e =>
      return #[Syntax.Diagnostic.error (toString e) Syntax.Span.uninhabited]

    | .ok deps =>
      let (extSymbols, extInstances, extConstructors) := Somac.Build.processExternalDependencies deps

      -- Initialize UniqueSupply
      let supply := Soma.UniqueSupply.initial packageName

      -- Compile all modules (type check)
      let (compileDiags, _, _) := Somac.Build.compileModulesInOrder sortedNames graph extSymbols extInstances extConstructors packageName supply

      return compileDiags

/-- Handler for the `check` command -/
def runCheck (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let name := p.flag? "name" |>.map (·.as! String)
  let format := p.flag? "format" |>.map (·.as! String) |>.getD "json"

  let opts : CheckOptions := {
    input := input
    name := name
    deps := parseDeps p
    format := if format == "human" then .human else .json
  }

  let inputPath : System.FilePath := opts.input

  let (diags, sourceFile) ← if ← inputPath.isDir then
    let diags ← checkDirectory opts
    pure (diags, none)
  else if inputPath.extension == some "soma" then
    checkSingleFile opts
  else
    let msg := s!"Input is neither a .soma file nor a directory: {opts.input}"
    pure (#[Syntax.Diagnostic.error msg Syntax.Span.uninhabited], none)

  -- Output diagnostics
  match opts.format with
  | .json =>
    IO.println (Logging.Error.renderDiagnosticsJson diags)
  | .human =>
    match sourceFile with
    | some sf => Logging.Error.printDiagnostics diags sf
    | none =>
      for d in diags do
        let severity := toString d.severity
        IO.eprintln s!"{severity}: {d.message}"

    if !diags.isEmpty then
      IO.eprintln ""
      IO.eprintln (Logging.Error.renderSummary diags)
    else
      IO.println "No errors found."

  return if Syntax.Diagnostics.hasErrors diags then 1 else 0

/-- Handler for the `circuit` command -/
def runCircuit (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String

  let opts : CircuitOptions := {
    input := input
    linearize := p.hasFlag "linearize"
    graphFormat := p.hasFlag "graph"
    eval := p.hasFlag "eval"
    toAlloy := p.hasFlag "alloy"
    toLlvm := p.hasFlag "llvm"
  }

  IO.println s!"[circuit] Processing: {input}"
  IO.println s!"[circuit] Options: {repr opts}"
  IO.println "[circuit] (not yet implemented)"
  return 0

/-- Handler for the `build` command -/
def runBuild (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let output := p.flag? "out" |>.map (·.as! String)
  let name := p.flag? "name" |>.map (·.as! String)
  let mode := p.flag? "mode" |>.map (·.as! String) |>.getD "standard"
  let optLevel := p.flag? "opt-level" |>.map (·.as! Nat)

  let compMode := match mode with
    | "graph" => CompilationMode.graph
    | "hybrid" => CompilationMode.hybrid
    | _ => CompilationMode.standard

  let opts : BuildOptions := {
    input := input
    output := output
    name := name
    lib := p.hasFlag "lib"
    deps := parseDeps p
    skipCircuit := p.hasFlag "skip-circuit"
    mode := compMode
    optimizationLevel := optLevel
    validate := p.hasFlag "validate"
  }

  IO.println "Soma Compiler v0.1.0"

  let result ← Somac.Build.build opts

  if result.success then
    return 0
  else
    for diag in result.diagnostics do
      IO.eprintln s!"{diag.severity}: {diag.message}"
    return 1

/-- The `lex` subcommand -/
def lexCmd : Cmd := `[Cli|
  lex VIA runLex; ["0.1.0"]
  "Run the lexer on a source file and print tokens."

  ARGS:
    input : String; "Input source file (.soma)"
]

/-- The `parse` subcommand -/
def parseCmd : Cmd := `[Cli|
  parse VIA runParse; ["0.1.0"]
  "Run the parser on a source file and print the AST."

  FLAGS:
    cst; "Show the Concrete Syntax Tree (before lowering)"
    ast; "Show the Abstract Syntax Tree (after lowering)"

  ARGS:
    input : String; "Input source file (.soma)"
]

/-- The `lower` subcommand -/
def lowerCmd : Cmd := `[Cli|
  lower VIA runLower; ["0.1.0"]
  "Lower a source file to Metal HIR (untyped intermediate representation)."

  ARGS:
    input : String; "Input source file (.soma)"
]

/-- The `check` subcommand -/
def checkCmd : Cmd := `[Cli|
  check VIA runCheck; ["0.1.0"]
  "Type-check a source file or directory without compiling."

  FLAGS:
    name : String; "Name of the module"
    d, dep : Array String; "External dependency (NAME=PATH)"
    format : String; "Output format: json (default) or human"

  ARGS:
    input : String; "Input source file or directory"
]

/-- The `circuit` subcommand -/
def circuitCmd : Cmd := `[Cli|
  circuit VIA runCircuit; ["0.1.0"]
  "Lower to Circuit IR (Interaction Nets) and optionally transform."

  FLAGS:
    l, linearize; "Apply linearization pass (insert DUP/ERA nodes)"
    g, graph; "Output in graph format instead of term format"
    e, eval; "Evaluate using interaction net reduction"
    a, alloy; "Lower Circuit IR to Alloy MIR"
    llvm; "Lower to LLVM IR (implies -l -a)"

  ARGS:
    input : String; "Input source file (.soma)"
]

/-- The `build` subcommand -/
def buildCmd : Cmd := `[Cli|
  build VIA runBuild; ["0.1.0"]
  "Compile a Soma source file or project."

  FLAGS:
    o, out : String; "Output file path"
    name : String; "Name of the compiled program or library"
    lib; "Compile as a Soma library"
    d, dep : Array String; "External dependency (NAME=PATH)"
    "skip-circuit"; "Do not use Circuit IR pipeline"
    m, mode : String; "Compilation mode: standard (default), graph, or hybrid"
    O, "opt-level" : Nat; "Optimization level (0-3)"
    validate; "Validate the Circuit IR for correctness"

  ARGS:
    input : String; "Input source file or directory"
]

/-- Main compiler command with subcommands -/
def somaCmd : Cmd := `[Cli|
  somac VIA runBuild; ["0.1.0"]
  "The Soma compiler - compile and run Soma source files."

  FLAGS:
    o, out : String; "Output file path"
    name : String; "Name of the compiled program or library"
    lib; "Compile as a Soma library"
    d, dep : Array String; "External dependency (NAME=PATH)"
    "skip-circuit"; "Do not use Circuit IR pipeline"
    m, mode : String; "Compilation mode: standard (default), graph, or hybrid"
    O, "opt-level" : Nat; "Optimization level (0-3)"
    validate; "Validate the Circuit IR for correctness"

  ARGS:
    input : String; "Input source file or directory"

  SUBCOMMANDS:
    lexCmd;
    parseCmd;
    lowerCmd;
    checkCmd;
    circuitCmd;
    buildCmd
]

end Soma.Driver

def main (args : List String) : IO UInt32 :=
  Soma.Driver.somaCmd.validate args
