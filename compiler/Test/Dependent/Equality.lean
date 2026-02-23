/-
  Test.Dependent.Equality - Unit tests for equality types and proofs (Phase 8)

  Tests cover:
  - Equality type construction and conversion
  - Reflexivity proof construction
  - Transport elimination
  - Equality type inference
  - Definitional equality checking for equality types
  - Transport reduction (transport refl = body)
-/

import Soma.Dependent
import Soma.Dependent.Equality
import Soma.Core
import Test.Fixtures

namespace Test.Dependent.Equality

open Soma.Dependent
open Soma.Dependent.Equality
open Soma.Core
open Soma.Syntax (Span)
open Test.Fixtures

/-- Helper to create a dummy span -/
def testSpan : Span := Span.uninhabited

/-! ## Value Construction Tests -/

namespace ValueTests

/-- Test: Equality type construction -/
def testEqConstruction : IO TestResult := do
  let ty := Value.vPrimTy .int
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 1
  let eq := Value.vEq Level.zero ty lhs rhs
  match eq with
  | .vEq (.lit 0) (.vPrimTy .int) (.vIntLit 1) (.vIntLit 1) => return .passed
  | _ => return .failed "equality type should be constructed correctly"

/-- Test: Refl construction -/
def testReflConstruction : IO TestResult := do
  let ty := Value.vPrimTy .int
  let x := Value.vIntLit 42
  let refl := Value.vRefl ty x
  match refl with
  | .vRefl (.vPrimTy .int) (.vIntLit 42) => return .passed
  | _ => return .failed "refl should be constructed correctly"

/-- Test: Transport construction -/
def testTransportConstruction : IO TestResult := do
  let ty := Value.vPrimTy .int
  let motive := Value.vLabelLit "_motive"
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 2
  let eq := Value.vRefl ty lhs  -- Using refl for simplicity
  let body := Value.vIntLit 42
  let transport := Value.vTransport Level.zero ty motive lhs rhs eq body
  match transport with
  | .vTransport (.lit 0) (.vPrimTy .int) (.vLabelLit "_motive") (.vIntLit 1) (.vIntLit 2) _ (.vIntLit 42) =>
    return .passed
  | _ => return .failed "transport should be constructed correctly"

/-- Test: mkEq helper function -/
def testMkEq : IO TestResult := do
  let ty := Value.vPrimTy .bool
  let lhs := Value.vConstructor ⟨⟨0, "", "True"⟩⟩ 0 []
  let rhs := Value.vConstructor ⟨⟨0, "", "True"⟩⟩ 0 []
  let eq := mkEq Level.zero ty lhs rhs
  match eq with
  | .vEq (.lit 0) (.vPrimTy .bool) _ _ => return .passed
  | _ => return .failed "mkEq should create correct equality type"

/-- Test: mkRefl helper function -/
def testMkRefl : IO TestResult := do
  let ty := Value.vPrimTy .string
  let x := Value.vStringLit "test"
  let refl := mkRefl ty x
  match refl with
  | .vRefl (.vPrimTy .string) (.vStringLit "test") => return .passed
  | _ => return .failed "mkRefl should create correct refl proof"

/-- Test: mkTransport helper function -/
def testMkTransport : IO TestResult := do
  let ty := Value.vPrimTy .int
  let motive := Value.vLabelLit "_test"
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 1
  let eq := mkRefl ty lhs
  let body := Value.vIntLit 100
  let transport := mkTransport Level.zero ty motive lhs rhs eq body
  match transport with
  | .vTransport _ _ _ _ _ _ _ => return .passed
  | _ => return .failed "mkTransport should create transport value"

def run : IO TestRunner := do
  IO.println "  === Value Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "eq_construction" (← testEqConstruction)
  runner := runner.record "refl_construction" (← testReflConstruction)
  runner := runner.record "transport_construction" (← testTransportConstruction)
  runner := runner.record "mk_eq" (← testMkEq)
  runner := runner.record "mk_refl" (← testMkRefl)
  runner := runner.record "mk_transport" (← testMkTransport)
  return runner

end ValueTests

/-! ## Conversion Tests for Equality -/

namespace ConversionTests

/-- Test: Equal equality types are convertible -/
def testEqConvertSame : IO TestResult := do
  let ty := Value.vPrimTy .int
  let x := Value.vIntLit 1
  let eq1 := Value.vEq Level.zero ty x x
  let eq2 := Value.vEq Level.zero ty x x
  match (convert eq1 eq2).run' with
  | .ok true => return .passed
  | .ok false => return .failed "identical equality types should be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Equality types with different lhs are not convertible -/
def testEqNotConvertDiffLhs : IO TestResult := do
  let ty := Value.vPrimTy .int
  let eq1 := Value.vEq Level.zero ty (Value.vIntLit 1) (Value.vIntLit 2)
  let eq2 := Value.vEq Level.zero ty (Value.vIntLit 3) (Value.vIntLit 2)
  match (convert eq1 eq2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "equality types with different lhs should not be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Equality types with different rhs are not convertible -/
def testEqNotConvertDiffRhs : IO TestResult := do
  let ty := Value.vPrimTy .int
  let eq1 := Value.vEq Level.zero ty (Value.vIntLit 1) (Value.vIntLit 2)
  let eq2 := Value.vEq Level.zero ty (Value.vIntLit 1) (Value.vIntLit 3)
  match (convert eq1 eq2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "equality types with different rhs should not be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Equality types with different base types are not convertible -/
def testEqNotConvertDiffType : IO TestResult := do
  let eq1 := Value.vEq Level.zero (Value.vPrimTy .int) (Value.vIntLit 1) (Value.vIntLit 1)
  let eq2 := Value.vEq Level.zero (Value.vPrimTy .string) (Value.vStringLit "1") (Value.vStringLit "1")
  match (convert eq1 eq2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "equality types with different base types should not be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Equal refl proofs are convertible -/
def testReflConvertSame : IO TestResult := do
  let ty := Value.vPrimTy .int
  let x := Value.vIntLit 42
  let refl1 := Value.vRefl ty x
  let refl2 := Value.vRefl ty x
  match (convert refl1 refl2).run' with
  | .ok true => return .passed
  | .ok false => return .failed "identical refl proofs should be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Refl proofs with different values are not convertible -/
def testReflNotConvertDiffValue : IO TestResult := do
  let ty := Value.vPrimTy .int
  let refl1 := Value.vRefl ty (Value.vIntLit 1)
  let refl2 := Value.vRefl ty (Value.vIntLit 2)
  match (convert refl1 refl2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "refl proofs with different values should not be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Transport values with same components are convertible -/
def testTransportConvertSame : IO TestResult := do
  let ty := Value.vPrimTy .int
  let motive := Value.vLabelLit "_m"
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 2
  let eq := Value.vRefl ty lhs
  let body := Value.vIntLit 100
  let t1 := Value.vTransport Level.zero ty motive lhs rhs eq body
  let t2 := Value.vTransport Level.zero ty motive lhs rhs eq body
  match (convert t1 t2).run' with
  | .ok true => return .passed
  | .ok false => return .failed "identical transport values should be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Transport values with different bodies are not convertible -/
def testTransportNotConvertDiffBody : IO TestResult := do
  let ty := Value.vPrimTy .int
  let motive := Value.vLabelLit "_m"
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 2
  let eq := Value.vRefl ty lhs
  let t1 := Value.vTransport Level.zero ty motive lhs rhs eq (Value.vIntLit 100)
  let t2 := Value.vTransport Level.zero ty motive lhs rhs eq (Value.vIntLit 200)
  match (convert t1 t2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "transport values with different bodies should not be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

def run : IO TestRunner := do
  IO.println "  === Conversion Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "eq_convert_same" (← testEqConvertSame)
  runner := runner.record "eq_not_convert_diff_lhs" (← testEqNotConvertDiffLhs)
  runner := runner.record "eq_not_convert_diff_rhs" (← testEqNotConvertDiffRhs)
  runner := runner.record "eq_not_convert_diff_type" (← testEqNotConvertDiffType)
  runner := runner.record "refl_convert_same" (← testReflConvertSame)
  runner := runner.record "refl_not_convert_diff_value" (← testReflNotConvertDiffValue)
  runner := runner.record "transport_convert_same" (← testTransportConvertSame)
  runner := runner.record "transport_not_convert_diff_body" (← testTransportNotConvertDiffBody)
  return runner

end ConversionTests

/-! ## Type Inference Tests for Equality -/

namespace InferTests

def synName (s : String) : Soma.Syntax.Name := ⟨s, testSpan⟩

/-- Test: Infer integer literal in equality suite -/
def testInferIntLit : IO TestResult := do
  let expr : Soma.Syntax.Expr := .lit (.int 1 testSpan)
  match typeInfer expr with
  | .ok (.vPrimTy .int, _, _) => return .passed
  | .ok (resTy, _, _) => return .failed s!"Expected Int, got {resTy}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Infer string literal in equality suite -/
def testInferStringLit : IO TestResult := do
  let expr : Soma.Syntax.Expr := .lit (.string "hello" testSpan)
  match typeInfer expr with
  | .ok (.vPrimTy .string, _, _) => return .passed
  | .ok (resTy, _, _) => return .failed s!"Expected String, got {resTy}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Infer Type literal in equality suite -/
def testInferType : IO TestResult := do
  let expr : Soma.Syntax.Expr := .var (synName "Type")
  match typeInfer expr with
  | .ok (.vType (.lit 1), _, _) => return .passed
  | .ok (resTy, _, _) => return .failed s!"Expected Type₁, got {resTy}"
  | .error e => return .failed s!"Unexpected error: {e}"

def run : IO TestRunner := do
  IO.println "  === Infer Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "infer_int_lit" (← testInferIntLit)
  runner := runner.record "infer_string_lit" (← testInferStringLit)
  runner := runner.record "infer_type" (← testInferType)
  return runner

end InferTests

/-! ## Unification Tests for Equality -/

namespace UnifyTests

/-- Test: Unify identical equality types -/
def testUnifyEqSame : IO TestResult := do
  let ty := Value.vPrimTy .int
  let x := Value.vIntLit 1
  let eq1 := Value.vEq Level.zero ty x x
  let eq2 := Value.vEq Level.zero ty x x
  match (unify eq1 eq2).run' with
  | .ok _ => return .passed
  | .error e => return .failed s!"Failed to unify identical equality types: {e}"

/-- Test: Unify identical refl proofs -/
def testUnifyReflSame : IO TestResult := do
  let ty := Value.vPrimTy .int
  let x := Value.vIntLit 42
  let refl1 := Value.vRefl ty x
  let refl2 := Value.vRefl ty x
  match (unify refl1 refl2).run' with
  | .ok _ => return .passed
  | .error e => return .failed s!"Failed to unify identical refl proofs: {e}"

/-- Test: Unify identical transport values -/
def testUnifyTransportSame : IO TestResult := do
  let ty := Value.vPrimTy .int
  let motive := Value.vLabelLit "_m"
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 2
  let eq := Value.vRefl ty lhs
  let body := Value.vIntLit 100
  let t1 := Value.vTransport Level.zero ty motive lhs rhs eq body
  let t2 := Value.vTransport Level.zero ty motive lhs rhs eq body
  match (unify t1 t2).run' with
  | .ok _ => return .passed
  | .error e => return .failed s!"Failed to unify identical transport values: {e}"

def run : IO TestRunner := do
  IO.println "  === Unify Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "unify_eq_same" (← testUnifyEqSame)
  runner := runner.record "unify_refl_same" (← testUnifyReflSame)
  runner := runner.record "unify_transport_same" (← testUnifyTransportSame)
  return runner

end UnifyTests

/-! ## Evaluation Tests for Equality -/

namespace EvalTests

/-- Test: Eval equality type -/
def testEvalEqType : IO TestResult := do
  let ty : Soma.Core.Expr := .primTy .int
  let lhs : Soma.Core.Expr := .lit (.int 1)
  let rhs : Soma.Core.Expr := .lit (.int 2)
  let eqExpr : Soma.Core.Expr := .eqTy (.lit 0) ty lhs rhs
  let result := evalCoreExpr EvalCtx.empty eqExpr
  match result with
  | .vEq (.lit 0) (.vPrimTy .int) (.vIntLit 1) (.vIntLit 2) => return .passed
  | _ => return .failed s!"Expected vEq, got {result}"

/-- Test: Eval refl -/
def testEvalRefl : IO TestResult := do
  let ty : Soma.Core.Expr := .primTy .int
  let x : Soma.Core.Expr := .lit (.int 42)
  let reflExpr : Soma.Core.Expr := .refl ty x
  let result := evalCoreExpr EvalCtx.empty reflExpr
  match result with
  | .vRefl (.vPrimTy .int) (.vIntLit 42) => return .passed
  | _ => return .failed s!"Expected vRefl, got {result}"

/-- Test: Transport with refl reduces to body -/
def testTransportReflReduces : IO TestResult := do
  let ty : Soma.Core.Expr := .primTy .int
  let motive : Soma.Core.Expr := .labelLit "_motive"
  let lhs : Soma.Core.Expr := .lit (.int 1)
  let rhs : Soma.Core.Expr := .lit (.int 1)
  let eq : Soma.Core.Expr := .refl ty lhs
  let body : Soma.Core.Expr := .lit (.int 42)
  let transportExpr : Soma.Core.Expr := .transport (.lit 0) ty motive lhs rhs eq body
  let result := evalCoreExpr EvalCtx.empty transportExpr
  match result with
  | .vIntLit 42 => return .passed
  | _ => return .failed s!"Expected 42 (transport refl reduces to body), got {result}"

def run : IO TestRunner := do
  IO.println "  === Eval Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "eval_eq_type" (← testEvalEqType)
  runner := runner.record "eval_refl" (← testEvalRefl)
  runner := runner.record "transport_refl_reduces" (← testTransportReflReduces)
  return runner

end EvalTests

/-! ## Quote Tests for Equality -/

namespace QuoteTests

/-- Test: Quote equality type -/
def testQuoteEq : IO TestResult := do
  let ty := Value.vPrimTy .int
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 2
  let eq := Value.vEq Level.zero ty lhs rhs
  let quoted := quoteExpr0 eq
  match quoted with
  | .eqTy (.lit 0) _ _ _ => return .passed
  | _ => return .failed s!"Expected .eq expression"

/-- Test: Quote refl -/
def testQuoteRefl : IO TestResult := do
  let ty := Value.vPrimTy .int
  let x := Value.vIntLit 42
  let refl := Value.vRefl ty x
  let quoted := quoteExpr0 refl
  match quoted with
  | .refl _ _ => return .passed
  | _ => return .failed s!"Expected .refl expression"

/-- Test: Quote transport -/
def testQuoteTransport : IO TestResult := do
  let ty := Value.vPrimTy .int
  let motive := Value.vLabelLit "_m"
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 2
  let eq := Value.vRefl ty lhs
  let body := Value.vIntLit 100
  let transport := Value.vTransport Level.zero ty motive lhs rhs eq body
  let quoted := quoteExpr0 transport
  match quoted with
  | .transport (.lit 0) _ _ _ _ _ _ => return .passed
  | _ => return .failed s!"Expected .transport expression"

def run : IO TestRunner := do
  IO.println "  === Quote Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "quote_eq" (← testQuoteEq)
  runner := runner.record "quote_refl" (← testQuoteRefl)
  runner := runner.record "quote_transport" (← testQuoteTransport)
  return runner

end QuoteTests

/-! ## Zonk Tests for Equality -/

namespace ZonkTests

/-- Test: Zonk equality type preserves structure -/
def testZonkEq : IO TestResult := do
  let ty := Value.vPrimTy .int
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 2
  let eq := Value.vEq Level.zero ty lhs rhs
  match (zonkValue eq).run' with
  | .ok (.vEq (.lit 0) (.vPrimTy .int) (.vIntLit 1) (.vIntLit 2)) => return .passed
  | .ok v => return .failed s!"Expected vEq, got {v}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Zonk refl preserves structure -/
def testZonkRefl : IO TestResult := do
  let ty := Value.vPrimTy .int
  let x := Value.vIntLit 42
  let refl := Value.vRefl ty x
  match (zonkValue refl).run' with
  | .ok (.vRefl (.vPrimTy .int) (.vIntLit 42)) => return .passed
  | .ok v => return .failed s!"Expected vRefl, got {v}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Zonk transport preserves structure -/
def testZonkTransport : IO TestResult := do
  let ty := Value.vPrimTy .int
  let motive := Value.vLabelLit "_m"
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 2
  let eq := Value.vRefl ty lhs
  let body := Value.vIntLit 100
  let transport := Value.vTransport Level.zero ty motive lhs rhs eq body
  match (zonkValue transport).run' with
  | .ok (.vTransport _ _ _ _ _ _ _) => return .passed
  | .ok v => return .failed s!"Expected vTransport, got {v}"
  | .error e => return .failed s!"Unexpected error: {e}"

def run : IO TestRunner := do
  IO.println "  === Zonk Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "zonk_eq" (← testZonkEq)
  runner := runner.record "zonk_refl" (← testZonkRefl)
  runner := runner.record "zonk_transport" (← testZonkTransport)
  return runner

end ZonkTests

/-! ## Main Test Runner -/

def runAllTests : IO TestRunner := do
  IO.println "=== Phase 8: Equality Tests ==="
  IO.println ""

  let valueRunner ← ValueTests.run
  valueRunner.printSummary "Value"

  let conversionRunner ← ConversionTests.run
  conversionRunner.printSummary "Conversion"

  let inferRunner ← InferTests.run
  inferRunner.printSummary "Infer"

  let unifyRunner ← UnifyTests.run
  unifyRunner.printSummary "Unify"

  let evalRunner ← EvalTests.run
  evalRunner.printSummary "Eval"

  let quoteRunner ← QuoteTests.run
  quoteRunner.printSummary "Quote"

  let zonkRunner ← ZonkTests.run
  zonkRunner.printSummary "Zonk"

  IO.println ""

  let combined := valueRunner.merge conversionRunner |>.merge inferRunner
    |>.merge unifyRunner |>.merge evalRunner |>.merge quoteRunner
    |>.merge zonkRunner

  IO.println s!"Total: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Dependent.Equality
