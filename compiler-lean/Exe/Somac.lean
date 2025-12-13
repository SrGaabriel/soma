import Cli
import Soma.Driver.Options
import Soma.Syntax
import Soma.Metal
import Soma.Logging
import Somac.Build

open Cli

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

  -- Lex it
  let (tokens, diags) := Syntax.lex source

  -- Print diagnostics if any
  if diags.size > 0 then
    IO.eprintln s!"Found {diags.size} diagnostic(s):"
    for diag in diags do
      IO.eprintln s!"  {diag.severity}: {diag.message}"

  -- Print tokens
  IO.println s!"Lexed {tokens.size} tokens from {input}:"
  for tok in tokens do
    IO.println s!"  {tok.kind} at {tok.span.start.line}:{tok.span.start.column}"

  return if diags.size > 0 then 1 else 0

/-- Handler for the `parse` command -/
def runParse (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let showCst := p.hasFlag "cst"
  let showAst := p.hasFlag "ast"

  -- Read the file
  let source ← IO.FS.readFile input

  -- Create source file
  let sourceFile := Syntax.SourceFile.create ⟨0⟩ input source

  -- Lex it
  let (tokens, lexDiags) := Syntax.lexCode sourceFile

  -- Print lex diagnostics if any
  if lexDiags.size > 0 then
    Logging.Error.printDiagnostics lexDiags sourceFile

  -- Parse it
  let (cst, parseDiags) := Syntax.Parse.parseSourceFile.run' tokens sourceFile

  -- Print parse diagnostics if any
  if parseDiags.size > 0 then
    Logging.Error.printDiagnostics parseDiags sourceFile

  -- Show CST if requested
  if showCst then
    IO.println "=== Concrete Syntax Tree ==="
    IO.println (cst.debugPrint)

  -- Lower to AST
  -- Extract module name from filename (without extension)
  let fileName := input.splitOn "/" |>.getLast!
  let moduleName := fileName.splitOn "." |>.head!
                    |> fun s => if s.isEmpty then "Main" else s
  let (astOpt, lowerDiags) := Syntax.lower cst moduleName

  -- Print lowering diagnostics if any
  if lowerDiags.size > 0 then
    Logging.Error.printDiagnostics lowerDiags sourceFile

  -- Collect all diagnostics
  let allDiags := lexDiags ++ parseDiags ++ lowerDiags

  -- Show AST if requested (or by default if no flags)
  match astOpt with
  | some ast =>
      if showAst || (!showCst && !showAst) then
        IO.println "=== Abstract Syntax Tree ==="
        IO.println (Syntax.Pretty.ppModule ast)
      if allDiags.isEmpty then
        IO.println "\nParse successful!"
  | none =>
      IO.eprintln "Parse failed - could not produce AST"

  -- Print summary if there were any diagnostics
  if !allDiags.isEmpty then
    IO.eprintln ""
    IO.eprintln (Logging.Error.renderSummary allDiags)

  return if allDiags.size > 0 then 1 else 0

/-- Handler for the `lower` command - Metal HIR lowering -/
def runLower (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String

  -- Read the file
  let source ← IO.FS.readFile input

  -- Create source file
  let sourceFile := Syntax.SourceFile.create ⟨0⟩ input source

  -- Lex
  let (tokens, lexDiags) := Syntax.lexCode sourceFile
  if lexDiags.size > 0 then
    Logging.Error.printDiagnostics lexDiags sourceFile

  -- Parse
  let (cst, parseDiags) := Syntax.Parse.parseSourceFile.run' tokens sourceFile
  if parseDiags.size > 0 then
    Logging.Error.printDiagnostics parseDiags sourceFile

  -- Lower CST to AST
  let fileName := input.splitOn "/" |>.getLast!
  let moduleName := fileName.splitOn "." |>.head!
                    |> fun s => if s.isEmpty then "Main" else s
  let (astOpt, astDiags) := Syntax.lower cst moduleName
  if astDiags.size > 0 then
    Logging.Error.printDiagnostics astDiags sourceFile

  -- Check for errors so far
  let frontendDiags := lexDiags ++ parseDiags ++ astDiags
  if frontendDiags.hasErrors then
    IO.eprintln "\nCannot proceed to Metal lowering due to errors."
    IO.eprintln (Logging.Error.renderSummary frontendDiags)
    return 1

  match astOpt with
  | none =>
    IO.eprintln "Failed to produce AST"
    return 1
  | some ast =>
    -- Lower AST to Metal IR
    let result := Metal.Lower.lower ast

    -- Convert and print Metal lowering errors
    let metalDiags := Metal.Lower.LowerError.toDiagnostics result.errors
    if metalDiags.size > 0 then
      Logging.Error.printDiagnostics metalDiags sourceFile

    -- Print summary
    let allDiags := frontendDiags ++ metalDiags
    if allDiags.hasErrors then
      IO.eprintln ""
      IO.eprintln (Logging.Error.renderSummary allDiags)
      return 1

    -- Success - print info about the lowered module
    IO.println s!"=== Metal IR (Untyped) ==="
    IO.println s!"Module: {result.module.name}"
    IO.println s!"Functions: {result.module.functions.size}"
    IO.println s!"Types: {result.module.types.size}"
    IO.println s!"Type classes: {result.module.typeClasses.size}"

    -- Print function names
    if result.module.functions.size > 0 then
      IO.println "\nFunctions:"
      for fn in result.module.functions do
        let sigInfo := if fn.hasSignature then " (has signature)" else ""
        IO.println s!"  - {fn.name.display}{sigInfo}"

    -- Print type names
    if result.module.types.size > 0 then
      IO.println "\nTypes:"
      for ty in result.module.types do
        IO.println s!"  - {ty.name.display}"

    IO.println "\nMetal lowering successful!"
    return 0

/-- Handler for the `check` command -/
def runCheck (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let name := p.flag? "name" |>.map (·.as! String)
  let format := p.flag? "format" |>.map (·.as! String) |>.getD "json"

  let opts : CheckOptions := {
    input := input
    name := name
    deps := #[]  -- TODO: parse deps
    format := if format == "human" then .human else .json
  }

  IO.println s!"[check] Checking: {input}"
  IO.println s!"[check] Options: {repr opts}"
  IO.println "[check] (not yet implemented)"
  return 0

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
