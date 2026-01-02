import Cli
import Soma.Driver.Options
import Soma.Syntax
import Soma.Metal
import Soma.Logging
import Soma.Project
import Soma.Project.Check
import Soma.Dependent
import Somac.Build

open Cli
open Soma.Check (parseOnly toAst toMetal)

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
  let cfg : Metal.Pretty.Config := { indent := 2 }
  IO.println (Metal.Pretty.ppModule cfg module)
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

/-- Handler for the `check-dep` command (dependent type checking) -/
def runCheckDep (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let format := p.flag? "format" |>.map (·.as! String) |>.getD "human"
  let full := p.hasFlag "full"

  -- Read the file
  let content ← IO.FS.readFile input

  -- Run dependent type checking
  let result := if full
    then Soma.Dependent.Driver.checkFileFull input content
    else Soma.Dependent.Driver.checkFile input content

  -- Output diagnostics
  match format with
  | "json" =>
    IO.println (Logging.Error.renderDiagnosticsJson result.diagnostics)
  | _ => -- "human"
    if !result.diagnostics.isEmpty then
      Logging.Error.printDiagnostics result.diagnostics result.sourceFile
      IO.eprintln ""
      IO.eprintln (Logging.Error.renderSummary result.diagnostics)
    else
      IO.println "Dependent type check passed."

    -- Show TC-specific errors with more detail
    if !result.tcErrors.isEmpty then
      IO.eprintln ""
      IO.eprintln "Type checking details:"
      for e in result.tcErrors do
        let diag := e.toDiagnostic
        let code := diag.code.getD "E????"
        IO.eprintln s!"  [{code}] {diag.message}"

  return if result.success then 0 else 1

/-- Handler for the `metadata` command -/
def runMetadata (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let name := p.flag? "name" |>.map (·.as! String)

  let opts : MetadataOptions := {
    input := input
    name := name
    deps := parseDeps p
  }

  -- let result ← Somac.Build.Metadata.metadata opts

  -- if result.success then
  --   match result.metadata with
  --   | some pm =>
  --     IO.println pm.toJson.compress
  --     return 0
  --   | none =>
  --     IO.eprintln "Internal error: metadata generation succeeded but no metadata produced"
  --     return 1
  -- else
  --   for diag in result.diagnostics do
  --     IO.eprintln s!"{diag.severity}: {diag.message}"
  --   return 1
  sorry

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

  IO.println "Soma Compiler"

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
  check VIA runCheckDep; ["0.1.0"]
  "Type-check a source file using the dependent type system (CQC)."

  FLAGS:
    name : String; "Name of the module"
    d, dep : Array String; "External dependency (NAME=PATH)"
    format : String; "Output format: json or human (default)"
    legacy; "Use the legacy HM-based type inference instead of dependent types"
    debug; "Print detailed type inference trace for debugging"

  ARGS:
    input : String; "Input source file"
]

/-- The `metadata` subcommand -/
def metadataCmd : Cmd := `[Cli|
  metadata VIA runMetadata; ["0.1.0"]
  "Generate type metadata JSON without codegen (for fast dependency checking)."

  FLAGS:
    name : String; "Name of the module"
    d, dep : Array String; "External dependency (NAME=PATH)"

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
    metadataCmd;
    circuitCmd;
    buildCmd
]

end Soma.Driver

def main (args : List String) : IO UInt32 :=
  Soma.Driver.somaCmd.validate args
