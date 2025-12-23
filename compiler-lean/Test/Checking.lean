/-
  Type Checking Tests (End-to-End)

  These tests run complete Soma programs through the full compilation pipeline:
  Source -> Lex -> Parse -> Lower -> Metal -> Type Inference

  Test fixtures are in Test/fixtures/checking/*.soma
  Each file starts with a comment like:
    // expect: success
    // expect: error mismatch
-/

import Soma.Syntax
import Soma.Metal
import Soma.Infer
import Soma.Infer.Module
import Soma.Project
import Somac.Build
import Test.Fixtures

namespace Test.Checking

open Soma.Syntax
open Soma.Infer
open Soma.Typing
open Soma.Metal (UntypedModule)
open Soma.Project
open Test.Fixtures

/-- Expectation parsed from fixture comment -/
inductive Expectation where
  | success : Expectation
  | error (substring : Option String) : Expectation
  deriving Repr

/-- Parse expectation from first line of source -/
def parseExpectation (source : String) : Expectation :=
  let firstLine := source.takeWhile (· != '\n')
  if firstLine.startsWith "// expect: success" then
    .success
  else if firstLine.startsWith "// expect: error" then
    let rest := firstLine.drop "// expect: error".length |>.trim
    if rest.isEmpty then .error none else .error (some rest)
  else
    .success  -- Default to success if no expectation comment

/-- Result of running the full pipeline on source code -/
structure CheckResult where
  lexDiags : Diagnostics
  parseDiags : Diagnostics
  astLowerDiags : Diagnostics
  metalLowerDiags : Diagnostics
  inferErrors : Array InferError

namespace CheckResult

def allDiagnostics (r : CheckResult) : Diagnostics :=
  r.lexDiags ++ r.parseDiags ++ r.astLowerDiags ++ r.metalLowerDiags

def allErrors (r : CheckResult) : Diagnostics :=
  r.allDiagnostics.filter (·.severity == .error)

def hasErrors (r : CheckResult) : Bool :=
  !r.allErrors.isEmpty || !r.inferErrors.isEmpty

def isSuccess (r : CheckResult) : Bool :=
  !r.hasErrors

def errorMessages (r : CheckResult) : Array String :=
  r.allErrors.map (·.message) ++ r.inferErrors.map (·.toDiagnostic.message)

def detailedErrorMessages (r : CheckResult) : Array String :=
  let diagMsgs := r.allErrors.map fun d =>
    let labels := d.labels.map fun l => s!"  {l.message}"
    s!"{d.message}\n{String.intercalate "\n" labels.toList}"
  let inferMsgs := r.inferErrors.map fun e =>
    let d := e.toDiagnostic
    let labels := d.labels.map fun l => s!"  {l.message}"
    s!"{d.message}\n{String.intercalate "\n" labels.toList}"
  diagMsgs ++ inferMsgs

def errorSpanInfo (r : CheckResult) : Array String :=
  r.inferErrors.map fun e =>
    let d := e.toDiagnostic
    let labels := d.labels.map fun l =>
      s!"    label: {l.span} (bytes {l.span.start.byteOffset}-{l.span.stop.byteOffset}) - {l.message}"
    s!"{d.message} at primary span line {d.span?.map (·.start.line) |>.getD 0}\n{String.intercalate "\n" labels.toList}"

end CheckResult

/-- Debug: print expression spans recursively -/
partial def debugExprSpan (e : Expr) (indent : String) : String :=
  match e with
  | .var name => s!"{indent}VAR {name.value} at {name.span} (bytes {name.span.start.byteOffset}-{name.span.stop.byteOffset})"
  | .app fn arg span =>
      let fnS := debugExprSpan fn (indent ++ "  ")
      let argS := debugExprSpan arg (indent ++ "  ")
      s!"{indent}APP at {span} (bytes {span.start.byteOffset}-{span.stop.byteOffset})\n{fnS}\n{argS}"
  | .lit lit => s!"{indent}LIT at {lit.span}"
  | _ => s!"{indent}OTHER at {e.span}"

/-- Run the full pipeline on source code -/
def runCheck (source : String) (moduleName : String := "Test") : CheckResult := Id.run do
  let fileId : FileId := ⟨0⟩
  let sourceFile := SourceFile.create fileId "test.soma" source

  -- Phase 1+2: Parse to tree (includes lexing)
  let (tree, parseDiags) := parseToTree sourceFile

  -- Phase 3: Lower CST to AST
  let (ast, astLowerDiags) := lower tree moduleName

  -- Phase 4: Lower AST to Metal IR
  let lowerResult := Soma.Metal.Lower.lower ast
  let metalLowerDiags := Soma.Metal.Lower.LowerError.toDiagnostics lowerResult.errors

  -- Phase 5: Type inference
  let supply := Soma.UniqueSupply.initial "Test"
  let (typeEnv, supply) := Soma.Infer.buildTypeEnvFromModule lowerResult.module #[] supply
  let instanceEnv := Soma.Infer.buildInstanceEnvFromModule lowerResult.module InstanceEnv.empty typeEnv
  let inferCtx : InferContext := {
    typeEnv := typeEnv
    instanceEnv := instanceEnv
    currentFunction := none
  }
  let _ := supply -- suppress unused warning
  let inferResult := Soma.Infer.inferModule lowerResult.module inferCtx

  return {
    lexDiags := #[]
    parseDiags := parseDiags
    astLowerDiags := astLowerDiags
    metalLowerDiags := metalLowerDiags
    inferErrors := inferResult.errors
  }

/-- Run a single checking test from a fixture -/
def runCheckingTest (tc : TestCase) : IO TestResult := do
  let expectation := parseExpectation tc.source
  let result := runCheck tc.source

  -- Debug: print span info for position_test
  if tc.name == "position_test.soma" || tc.name == "position_test2.soma" || tc.name == "position_nocomment.soma" then
    IO.println s!"  [DEBUG] position_test span info:"
    for info in result.errorSpanInfo do
      IO.println s!"    {info}"
    -- Also print AST spans for the last def
    let sf := SourceFile.create ⟨0⟩ "test.soma" tc.source
    IO.println s!"  [DEBUG] Source length: {tc.source.utf8ByteSize} bytes"
    IO.println s!"  [DEBUG] Source line starts: {sf.lineStarts.toList}"
    let (tree, _) := parseToTree sf
    IO.println s!"  [DEBUG] Green tree width: {tree.green.width} bytes"
    let (ast, _) := lower tree "Test"
    -- Print all decl spans
    IO.println s!"  [DEBUG] AST declarations:"
    for decl in ast.decls do
      match decl with
      | .def_ _ name _ clauses span =>
          IO.println s!"    def {name.value} at {span} (bytes {span.start.byteOffset}-{span.stop.byteOffset})"
          if name.value == "a" then
            for clause in clauses do
              IO.println s!"      body:"
              IO.println s!"    {debugExprSpan clause.body "      "}"
      | .data name _ _ _ span =>
          IO.println s!"    data {name.value} at {span} (bytes {span.start.byteOffset}-{span.stop.byteOffset})"
      | d => IO.println s!"    other decl at {d.span} (bytes {d.span.start.byteOffset}-{d.span.stop.byteOffset})"

  match expectation with
  | .success =>
    if result.isSuccess then
      return .passed
    else
      let errors := result.detailedErrorMessages
      return .failed s!"Expected success but got errors:\n{String.intercalate "\n" errors.toList}"

  | .error expectedSubstr =>
    if result.hasErrors then
      match expectedSubstr with
      | some substr =>
        let msgs := result.errorMessages
        if msgs.any (fun msg => msg.toSlice.contains substr) then
          return .passed
        else
          return .failed s!"Expected error containing '{substr}' but got: {msgs}"
      | none =>
        return .passed  -- Just expected some error, got one
    else
      return .failed "Expected error but compilation succeeded"

/-- Run all checking tests from fixtures -/
def runFromFixtures : IO TestRunner := do
  IO.println "=== Checking Tests (from fixtures) ==="
  let cases ← loadAllTestCases "checking"
  let mut runner := TestRunner.init
  for tc in cases do
    let result ← runCheckingTest tc
    match result with
    | .passed => IO.println s!"  [PASS] {tc.name}"
    | .failed msg => IO.println s!"  [FAIL] {tc.name}: {msg}"
    | .skipped reason => IO.println s!"  [SKIP] {tc.name}: {reason}"
    runner := runner.record tc.name result
  return runner

/-- Test multi-file package with internal dependencies -/
def testMultiFilePackage : IO TestResult := do
  -- Use the deplib fixture (multi-file package with internal dependencies)
  let deplibPath : System.FilePath := "Test/fixtures/multifile/deplib"
  let srcPath := deplibPath / "src"

  -- Check if fixture exists
  let dirExists ← srcPath.isDir
  if !dirExists then
    return .skipped "deplib fixture not found"

  -- Find all modules
  let modules ← Soma.Project.findModules "deplib" srcPath

  -- Parse all modules
  let (parseDiags, graph) ← Somac.Build.parseModules modules

  if Diagnostics.hasErrors parseDiags then
    let errors := parseDiags.filter (·.isError)
    let msgs := errors.map (·.message)
    return .failed s!"Parse errors: {msgs.toList}"

  -- Build dependency graph and sort
  let depGraph := Soma.Project.buildDependencyGraph graph
  match Soma.Project.topoSortModules depGraph with
  | .cycles groups =>
    return .failed s!"Cyclic imports detected: {groups.map (·.toList)}"
  | .sorted sortedNames =>
    -- Compile all modules
    let supply := Soma.UniqueSupply.initial "deplib"
    let (compileDiags, _compiledModules, _) := Somac.Build.compileModulesInOrder
      sortedNames graph {} {} {} "deplib" supply

    if Diagnostics.hasErrors compileDiags then
      let errors := compileDiags.filter (·.isError)
      return .failed s!"Type check failed with {errors.size} error(s)"
    else
      return .passed

/-- Main entry point for checking tests -/
def run : IO Unit := do
  let mut runner ← runFromFixtures

  -- Add multi-file package test
  IO.println ""
  IO.println "=== Multi-File Package Tests ==="
  let multiResult ← testMultiFilePackage
  match multiResult with
  | .passed => IO.println s!"  [PASS] deplib (multi-file with internal deps)"
  | .failed msg => IO.println s!"  [FAIL] deplib: {msg}"
  | .skipped reason => IO.println s!"  [SKIP] deplib: {reason}"
  runner := runner.record "deplib-multifile" multiResult

  IO.println ""
  runner.printSummary "Checking Summary"
  IO.println ""

end Test.Checking
