import Cli
import Soma.Driver.Options
import Soma.Syntax
import Soma.Core.LambdaLift
import Soma.Logging
import Soma.Project
import Soma.Project.Check
import Soma.Dependent
import Somac.Circuit
import Somac.Alloy
import Somac.Llvm
import Somac.Build
import Somac.Build.Metadata

open Cli
open Soma.Project.Check (parseOnly toAst toElaborated)

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

/-- Handler for the `lower` command -/
def runLower (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String

  let content ← IO.FS.readFile input
  let (parseRes, lowerRes, elabRes) := toElaborated input content
  let allDiags := parseRes.diagnostics ++ lowerRes.diagnostics ++ elabRes.diagnostics

  -- Print diagnostics
  if !allDiags.isEmpty then
    Logging.Error.printDiagnostics allDiags parseRes.sourceFile

  if allDiags.hasErrors then
    IO.eprintln ""
    IO.eprintln (Logging.Error.renderSummary allDiags)
    return 1

  -- Success
  let module := elabRes.module
  IO.println s!"Lowered module: {module.name}"
  IO.println s!"  functions: {module.functions.size}"
  IO.println s!"  types: {module.types.size}"
  IO.println s!"  instances: {module.instances.size}"
  IO.println s!"  typeclasses: {module.typeClasses.size}"
  IO.println s!"  abbreviations: {module.abbreviations.size}"
  IO.println "\nLowering successful!"
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
  let name := p.flag? "name" |>.map (·.as! String)
  let deps := parseDeps p

  -- Build project config
  let config : Soma.Project.Check.ProjectConfig := {
    input := ⟨input⟩
    name := name
    deps := deps.map fun (n, p) => (n, ⟨p⟩)
  }

  -- Run dependent type checking via Check module
  let result ← Soma.Project.Check.checkProject config Somac.Build.loadExternalDependencies

  -- Output diagnostics
  match format with
  | "json" =>
    IO.println (Logging.Error.renderDiagnosticsJson result.diagnostics)
  | _ => -- "human"
    if !result.diagnostics.isEmpty then
      Logging.Error.printDiagnosticsWithMap result.diagnostics result.sourceFiles
      IO.eprintln ""
      IO.eprintln (Logging.Error.renderSummary result.diagnostics)
    else
      IO.println "Dependent type check passed."

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

  let result ← Somac.Build.Metadata.metadata opts Somac.Build.loadExternalDependencies

  if result.success then
    match result.metadata with
    | some pm =>
      IO.println (Kenosis.Json.encode pm)
      return 0
    | none =>
      IO.eprintln "Internal error: metadata generation succeeded but no metadata produced"
      return 1
  else
    for diag in result.diagnostics do
      IO.eprintln s!"{diag.severity}: {diag.message}"
    return 1

/-- Handler for the `llvm` command -/
def runLLVM (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String

  -- Read source file
  let content ← IO.FS.readFile input

  -- Phase 1-3: Parse and lower to AST
  let moduleName := Soma.Project.Check.moduleNameFromPath input
  let (parseRes, lowerRes) := toAst input content (some moduleName)
  let parseDiags := parseRes.diagnostics ++ lowerRes.diagnostics

  if parseDiags.hasErrors then
    Soma.Logging.Error.printDiagnostics parseDiags parseRes.sourceFile
    IO.eprintln ""
    IO.eprintln (Soma.Logging.Error.renderSummary parseDiags)
    return 1

  -- Phase 4: Lower declarations to Core untyped module
  let elabRes := Soma.Project.Check.elaborate lowerRes.ast
  let elabDiags := parseDiags ++ elabRes.diagnostics

  if elabRes.diagnostics.hasErrors then
    Soma.Logging.Error.printDiagnostics elabDiags parseRes.sourceFile
    IO.eprintln ""
    IO.eprintln (Soma.Logging.Error.renderSummary elabDiags)
    return 1

  -- Phase 5: Type check with dependent types (this gives us usage counts)
  let tcResult := Soma.Project.Check.typeCheckModule
    elabRes.module moduleName
    Soma.Dependent.Globals.empty
    Soma.Dependent.InstanceEnv.empty
    Soma.Dependent.AbbrevEnv.empty
    none

  let tcDiags := tcResult.errors.map (·.toDiagnostic)
  let allDiags := elabDiags ++ tcDiags

  if allDiags.hasErrors then
    Soma.Logging.Error.printDiagnostics allDiags parseRes.sourceFile
    IO.eprintln ""
    IO.eprintln (Soma.Logging.Error.renderSummary allDiags)
    return 1

  -- Phase 5.5: Lambda lifting
  let liftedTypedFunctions := Soma.Core.LambdaLift.liftAll tcResult.typedFunctions moduleName tcResult.uniqueNextId (tcResult.globals.toGlobalEnvWithClasses tcResult.instanceEnv)

  -- Phase 6: Lower to Circuit IR with usage data and type info from type checking
  let graph := Somac.Circuit.Lower.lower elabRes.module.types liftedTypedFunctions tcResult.usages (some tcResult.globals) tcResult.instanceEnv

  -- Phase 7: Lower to Alloy MIR
  let primTypes := Somac.Alloy.Lower.buildPrimTypeRegistry tcResult.globals.wiredIn
  let alloyModule := Somac.Alloy.Lower.lower graph moduleName primTypes tcResult.globals.intrinsics

  -- Phase 8: Monomorphize the Alloy module
  let monoModule := Somac.Alloy.Monomorphize.monomorphize alloyModule

  -- Phase 9: Generate LLVM IR
  let llvmIR := Somac.Llvm.codegenToString monoModule

  IO.println llvmIR
  return 0

/-- Handler for the `alloy` command -/
def runAlloy (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String

  -- Read source file
  let content ← IO.FS.readFile input

  -- Phase 1-3: Parse and lower to AST
  let moduleName := Soma.Project.Check.moduleNameFromPath input
  let (parseRes, lowerRes) := toAst input content (some moduleName)
  let parseDiags := parseRes.diagnostics ++ lowerRes.diagnostics

  if parseDiags.hasErrors then
    Soma.Logging.Error.printDiagnostics parseDiags parseRes.sourceFile
    IO.eprintln ""
    IO.eprintln (Soma.Logging.Error.renderSummary parseDiags)
    return 1

  -- Phase 4: Lower declarations to Core untyped module
  let elabRes := Soma.Project.Check.elaborate lowerRes.ast
  let elabDiags := parseDiags ++ elabRes.diagnostics

  if elabRes.diagnostics.hasErrors then
    Soma.Logging.Error.printDiagnostics elabDiags parseRes.sourceFile
    IO.eprintln ""
    IO.eprintln (Soma.Logging.Error.renderSummary elabDiags)
    return 1

  -- Phase 5: Type check with dependent types (this gives us usage counts)
  let tcResult := Soma.Project.Check.typeCheckModule
    elabRes.module moduleName
    Soma.Dependent.Globals.empty
    Soma.Dependent.InstanceEnv.empty
    Soma.Dependent.AbbrevEnv.empty
    none

  let tcDiags := tcResult.errors.map (·.toDiagnostic)
  let allDiags := elabDiags ++ tcDiags

  if allDiags.hasErrors then
    Soma.Logging.Error.printDiagnostics allDiags parseRes.sourceFile
    IO.eprintln ""
    IO.eprintln (Soma.Logging.Error.renderSummary allDiags)
    return 1

  -- Phase 5.5: Lambda lifting
  let liftedTypedFunctions := Soma.Core.LambdaLift.liftAll tcResult.typedFunctions moduleName tcResult.uniqueNextId (tcResult.globals.toGlobalEnvWithClasses tcResult.instanceEnv)

  -- Phase 6: Lower to Circuit IR with usage data and type info from type checking
  let graph := Somac.Circuit.Lower.lower elabRes.module.types liftedTypedFunctions tcResult.usages (some tcResult.globals) tcResult.instanceEnv

  -- Phase 7: Lower to Alloy MIR
  let primTypes := Somac.Alloy.Lower.buildPrimTypeRegistry tcResult.globals.wiredIn
  let alloyModule := Somac.Alloy.Lower.lower graph moduleName primTypes tcResult.globals.intrinsics

  IO.println (Somac.Alloy.Pretty.pp alloyModule)
  IO.println ""
  IO.println s!"Alloy IR lowering successful ({alloyModule.funcs.size} functions)"
  return 0

/-- Handler for the `circuit` command -/
def runCircuit (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let graphFormat := p.hasFlag "graph"
  let showTypes := p.hasFlag "types"

  -- Read source file
  let content ← IO.FS.readFile input

  -- Phase 1-3: Parse and lower to AST
  let moduleName := Soma.Project.Check.moduleNameFromPath input
  let (parseRes, lowerRes) := toAst input content (some moduleName)
  let parseDiags := parseRes.diagnostics ++ lowerRes.diagnostics

  if parseDiags.hasErrors then
    Soma.Logging.Error.printDiagnostics parseDiags parseRes.sourceFile
    IO.eprintln ""
    IO.eprintln (Soma.Logging.Error.renderSummary parseDiags)
    return 1

  -- Phase 4: Lower declarations to Core untyped module
  let elabRes := Soma.Project.Check.elaborate lowerRes.ast
  let elabDiags := parseDiags ++ elabRes.diagnostics

  if elabRes.diagnostics.hasErrors then
    Soma.Logging.Error.printDiagnostics elabDiags parseRes.sourceFile
    IO.eprintln ""
    IO.eprintln (Soma.Logging.Error.renderSummary elabDiags)
    return 1

  -- Phase 5: Type check with dependent types (this gives us usage counts)
  let tcResult := Soma.Project.Check.typeCheckModule
    elabRes.module moduleName
    Soma.Dependent.Globals.empty
    Soma.Dependent.InstanceEnv.empty
    Soma.Dependent.AbbrevEnv.empty
    none

  let tcDiags := tcResult.errors.map (·.toDiagnostic)
  let allDiags := elabDiags ++ tcDiags

  if allDiags.hasErrors then
    Soma.Logging.Error.printDiagnostics allDiags parseRes.sourceFile
    IO.eprintln ""
    IO.eprintln (Soma.Logging.Error.renderSummary allDiags)
    return 1

  -- Phase 5.5: Lambda lifting
  let liftedTypedFunctions := Soma.Core.LambdaLift.liftAll tcResult.typedFunctions moduleName tcResult.uniqueNextId (tcResult.globals.toGlobalEnvWithClasses tcResult.instanceEnv)

  -- Phase 6: Lower to Circuit IR with usage data and type info from type checking
  let graph := Somac.Circuit.Lower.lower elabRes.module.types liftedTypedFunctions tcResult.usages (some tcResult.globals) tcResult.instanceEnv

  -- Pretty print the Circuit IR graph
  let cfg : Somac.Circuit.Pretty.Config := { showIds := true, showConnections := true, showLabels := true, showTypes := showTypes }
  if graphFormat then
    -- Full graph format with node IDs and connections
    IO.println (Somac.Circuit.Pretty.ppFull cfg graph)
  else
    -- Default: just the graph summary
    IO.println (Somac.Circuit.Pretty.ppGraph cfg graph)

  IO.println ""
  IO.println s!"Circuit IR lowering successful ({graph.nodeCount} nodes)"
  return 0

/-- Handler for the `build` command -/
def runBuild (p : Parsed) : IO UInt32 := do
  let input := p.positionalArg! "input" |>.as! String
  let output := p.flag? "out" |>.map (·.as! String)
  let name := p.flag? "name" |>.map (·.as! String)
  let mode := p.flag? "mode" |>.map (·.as! String) |>.getD "standard"
  let optLevel := p.flag? "opt-level" |>.map (·.as! Nat)
  let sysroot := p.flag? "sysroot" |>.map (·.as! String)
  let emitLlvm := p.hasFlag "emit-llvm"

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
    sysroot := sysroot
    emitLlvm := emitLlvm
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
  "Lower a source file to the Core untyped module representation."

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
    t, types; "Show type annotations on nodes"

  ARGS:
    input : String; "Input source file (.soma)"
]

/-- The `alloy` subcommand -/
def alloyCmd : Cmd := `[Cli|
  alloy VIA runAlloy; ["0.1.0"]
  "Lower to Alloy MIR (SSA-based mid-level IR)."

  ARGS:
    input : String; "Input source file (.soma)"
]

/-- The `llvm` subcommand -/
def llvmCmd : Cmd := `[Cli|
  llvm VIA runLLVM; ["0.1.0"]
  "Compile to LLVM IR (full pipeline: parse → typecheck → Circuit → Alloy → monomorphize → LLVM)."

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
    sysroot : String; "Path to sysroot (contains lib/ with runtime)"
    "emit-llvm"; "Keep the generated LLVM IR file (.ll) after compilation"

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
    sysroot : String; "Path to sysroot (contains lib/ with runtime)"
    "emit-llvm"; "Keep the generated LLVM IR file (.ll) after compilation"

  ARGS:
    input : String; "Input source file or directory"

  SUBCOMMANDS:
    lexCmd;
    parseCmd;
    lowerCmd;
    checkCmd;
    metadataCmd;
    circuitCmd;
    alloyCmd;
    llvmCmd;
    buildCmd
]

end Soma.Driver

def main (args : List String) : IO UInt32 :=
  Soma.Driver.somaCmd.validate args
