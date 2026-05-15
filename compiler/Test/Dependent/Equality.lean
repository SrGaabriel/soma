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

/-- Synthetic test placeholders for the kernel-level primitive types -/
def testIntTy : Soma.Core.Value := .vDataType ⟨1001, "test", "Int32"⟩ []
def testBoolTy : Soma.Core.Value := .vDataType ⟨1002, "test", "Bool"⟩ []
def testStringTy : Soma.Core.Value := .vDataType ⟨1003, "test", "String"⟩ []

/-- Synthetic id for the wired-in `Eq` inductive -/
def eqTestId : Soma.Unique := ⟨2000, "test", "Eq"⟩

/-- Synthetic name + tag for the wired-in `refl` constructor -/
def reflTestName : QualifiedName := ⟨⟨2001, "test", "refl"⟩⟩
def reflTestTag : Nat := 0

/-- Build an `Eq ty lhs rhs` value for tests -/
private def mkTestEq (ty lhs rhs : Value) : Value :=
  Value.vDataType eqTestId [ty, lhs, rhs]

/-- Build a `refl : Eq ty x x` value for tests -/
private def mkTestRefl (ty x : Value) : Value :=
  Value.vConstructor reflTestName reflTestTag [ty, x] (mkTestEq ty x x)

/-- A `Soma.Core.Expr` building `Eq ty lhs rhs` for tests -/
private def mkTestEqExpr (ty lhs rhs : Soma.Core.Expr) : Soma.Core.Expr :=
  Soma.Core.Expr.dataTy eqTestId #[ty, lhs, rhs]

/-- An `EvalCtx` for the equality tests -/
private def testEvalCtx : EvalCtx :=
  let g : GlobalEnv :=
    { eqInductiveId := some eqTestId
      reflConstructor := some (reflTestName, reflTestTag) }
  { EvalCtx.empty with globals := g }

namespace ValueTests

/-- Test: Equality type construction -/
def testEqConstruction : IO TestResult := do
  let ty := testIntTy
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 1
  let eq := mkTestEq ty lhs rhs
  match eq with
  | .vDataType id [.vDataType ⟨1001, "test", "Int32"⟩ [], .vIntLit 1, .vIntLit 1] =>
    if id == eqTestId then return .passed
    else return .failed s!"unexpected data-type id: {id.original}"
  | _ => return .failed "equality type should be constructed correctly"

/-- Test: Refl construction -/
def testReflConstruction : IO TestResult := do
  let ty := testIntTy
  let x := Value.vIntLit 42
  let refl := mkTestRefl ty x
  match refl with
  | .vConstructor name tag
      [.vDataType ⟨1001, "test", "Int32"⟩ [], .vIntLit 42] _ =>
    if name == reflTestName ∧ tag == reflTestTag then return .passed
    else return .failed s!"unexpected refl ctor: {name.display}/{tag}"
  | _ => return .failed "refl should be constructed correctly"


/-- Test: mkEq helper function -/
def testMkEq : IO TestResult := do
  let ty := testBoolTy
  let lhs := Value.vConstructor ⟨⟨0, "", "True"⟩⟩ 0 [] testBoolTy
  let rhs := Value.vConstructor ⟨⟨0, "", "True"⟩⟩ 0 [] testBoolTy
  let eq := mkEq eqTestId ty lhs rhs
  match eq with
  | .vDataType id [.vDataType ⟨1002, "test", "Bool"⟩ [], _, _] =>
    if id == eqTestId then return .passed
    else return .failed s!"unexpected data-type id: {id.original}"
  | _ => return .failed "mkEq should create correct equality type"

/-- Test: mkRefl helper function -/
def testMkRefl : IO TestResult := do
  let ty := testStringTy
  let x := Value.vStringLit "test"
  let refl := mkRefl eqTestId (reflTestName, reflTestTag) ty x
  match refl with
  | .vConstructor name tag
      [.vDataType ⟨1003, "test", "String"⟩ [], .vStringLit "test"] _ =>
    if name == reflTestName ∧ tag == reflTestTag then return .passed
    else return .failed s!"unexpected refl ctor: {name.display}/{tag}"
  | _ => return .failed "mkRefl should create correct refl proof"

def run : IO TestRunner := do
  IO.println "  === Value Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "eq_construction" (← testEqConstruction)
  runner := runner.record "refl_construction" (← testReflConstruction)
  runner := runner.record "mk_eq" (← testMkEq)
  runner := runner.record "mk_refl" (← testMkRefl)
  return runner

end ValueTests

/-! ## Conversion Tests for Equality -/

namespace ConversionTests

/-- Test: Equal equality types are convertible -/
def testEqConvertSame : IO TestResult := do
  let ty := testIntTy
  let x := Value.vIntLit 1
  let eq1 := mkTestEq ty x x
  let eq2 := mkTestEq ty x x
  match (convert eq1 eq2).run' with
  | .ok true => return .passed
  | .ok false => return .failed "identical equality types should be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Equality types with different lhs are not convertible -/
def testEqNotConvertDiffLhs : IO TestResult := do
  let ty := testIntTy
  let eq1 := mkTestEq ty (Value.vIntLit 1) (Value.vIntLit 2)
  let eq2 := mkTestEq ty (Value.vIntLit 3) (Value.vIntLit 2)
  match (convert eq1 eq2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "equality types with different lhs should not be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Equality types with different rhs are not convertible -/
def testEqNotConvertDiffRhs : IO TestResult := do
  let ty := testIntTy
  let eq1 := mkTestEq ty (Value.vIntLit 1) (Value.vIntLit 2)
  let eq2 := mkTestEq ty (Value.vIntLit 1) (Value.vIntLit 3)
  match (convert eq1 eq2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "equality types with different rhs should not be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Equality types with different base types are not convertible -/
def testEqNotConvertDiffType : IO TestResult := do
  let eq1 := mkTestEq testIntTy (Value.vIntLit 1) (Value.vIntLit 1)
  let eq2 := mkTestEq testStringTy (Value.vStringLit "1") (Value.vStringLit "1")
  match (convert eq1 eq2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "equality types with different base types should not be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Equal refl proofs are convertible -/
def testReflConvertSame : IO TestResult := do
  let ty := testIntTy
  let x := Value.vIntLit 42
  let refl1 := mkTestRefl ty x
  let refl2 := mkTestRefl ty x
  match (convert refl1 refl2).run' with
  | .ok true => return .passed
  | .ok false => return .failed "identical refl proofs should be convertible"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Refl proofs with different values are not convertible -/
def testReflNotConvertDiffValue : IO TestResult := do
  let ty := testIntTy
  let refl1 := mkTestRefl ty (Value.vIntLit 1)
  let refl2 := mkTestRefl ty (Value.vIntLit 2)
  match (convert refl1 refl2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "refl proofs with different values should not be convertible"
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
  return runner

end ConversionTests

/-! ## Type Inference Tests for Equality -/

namespace InferTests

def synName (s : String) : Soma.Syntax.QualName := ⟨#[], s, testSpan⟩

/-- Test: Infer integer literal -/
def testInferIntLit : IO TestResult := do
  let expr : Soma.Syntax.Expr := .lit (.int 1 testSpan)
  match typeInfer expr with
  | .ok (resTy, _, _) =>
    return .failed s!"Expected internal error for missing `Int` wired registration, got {resTy}"
  | .error _ => return .passed

/-- Test: Infer string literal -/
def testInferStringLit : IO TestResult := do
  let expr : Soma.Syntax.Expr := .lit (.string "hello" testSpan)
  match typeInfer expr with
  | .ok (resTy, _, _) =>
    return .failed s!"Expected internal error for missing `String` wired registration, got {resTy}"
  | .error _ => return .passed

/-- Test: Infer Type literal in equality suite -/
def testInferType : IO TestResult := do
  let expr : Soma.Syntax.Expr := .var (synName "Type")
  match typeInfer expr with
  | .ok (.vType (.succ _), _, _) => return .passed
  | .ok (resTy, _, _) => return .failed s!"Expected Type with successor level, got {resTy}"
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
  let ty := testIntTy
  let x := Value.vIntLit 1
  let eq1 := mkTestEq ty x x
  let eq2 := mkTestEq ty x x
  match (unify eq1 eq2).run' with
  | .ok _ => return .passed
  | .error e => return .failed s!"Failed to unify identical equality types: {e}"

/-- Test: Unify identical refl proofs -/
def testUnifyReflSame : IO TestResult := do
  let ty := testIntTy
  let x := Value.vIntLit 42
  let refl1 := mkTestRefl ty x
  let refl2 := mkTestRefl ty x
  match (unify refl1 refl2).run' with
  | .ok _ => return .passed
  | .error e => return .failed s!"Failed to unify identical refl proofs: {e}"


def run : IO TestRunner := do
  IO.println "  === Unify Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "unify_eq_same" (← testUnifyEqSame)
  runner := runner.record "unify_refl_same" (← testUnifyReflSame)
  return runner

end UnifyTests

/-! ## Evaluation Tests for Equality -/

namespace EvalTests

/-- Test: Eval equality type -/
def testEvalEqType : IO TestResult := do
  let intDataId : Soma.Unique := ⟨0, "test", "Int"⟩
  let ty : Soma.Core.Expr := .dataTy intDataId #[]
  let lhs : Soma.Core.Expr := .lit (.int 1)
  let rhs : Soma.Core.Expr := .lit (.int 2)
  let eqExpr : Soma.Core.Expr := mkTestEqExpr ty lhs rhs
  let result := evalCoreExpr EvalCtx.empty eqExpr
  match result with
  | .vDataType id [_, .vIntLit 1, .vIntLit 2] =>
    if id == eqTestId then return .passed
    else return .failed s!"unexpected data-type id: {id.original}"
  | _ => return .failed s!"Expected vDataType (Eq form), got {result}"

/-- Test: Eval refl -/
def testEvalRefl : IO TestResult := do
  let intDataId : Soma.Unique := ⟨0, "test", "Int"⟩
  let ty : Soma.Core.Expr := .dataTy intDataId #[]
  let x : Soma.Core.Expr := .lit (.int 42)
  let resultTy : Soma.Core.Expr := mkTestEqExpr ty x x
  let reflExpr : Soma.Core.Expr :=
    .construct reflTestName reflTestTag #[ty, x] resultTy
  let result := evalCoreExpr testEvalCtx reflExpr
  match result with
  | .vConstructor name tag [_, .vIntLit 42] _ =>
    if name == reflTestName ∧ tag == reflTestTag then return .passed
    else return .failed s!"unexpected refl ctor in eval: {name.display}/{tag}"
  | _ => return .failed s!"Expected vConstructor (refl), got {result}"

def run : IO TestRunner := do
  IO.println "  === Eval Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "eval_eq_type" (← testEvalEqType)
  runner := runner.record "eval_refl" (← testEvalRefl)
  return runner

end EvalTests

/-! ## Quote Tests for Equality -/

namespace QuoteTests

/-- Test: Quote equality type -/
def testQuoteEq : IO TestResult := do
  let ty := testIntTy
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 2
  let eq := mkTestEq ty lhs rhs
  let quoted := quoteExpr0 eq
  match quoted with
  | .dataTy id args =>
    if id == eqTestId && args.size == 3 then return .passed
    else return .failed s!"Quote produced unexpected dataTy: id={id.original} args.size={args.size}"
  | _ => return .failed s!"Expected .dataTy expression for quoted Eq, got {quoted}"

/-- Test: Quote refl -/
def testQuoteRefl : IO TestResult := do
  let ty := testIntTy
  let x := Value.vIntLit 42
  let refl := mkTestRefl ty x
  let quoted := quoteExpr0 refl
  match quoted with
  | .construct name 0 args _ =>
    if name == reflTestName ∧ args.size == 2 then return .passed
    else return .failed s!"Quote produced wrong construct: {name.display}, args.size={args.size}"
  | _ => return .failed s!"Expected .construct expression for quoted refl, got something else"

def run : IO TestRunner := do
  IO.println "  === Quote Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "quote_eq" (← testQuoteEq)
  runner := runner.record "quote_refl" (← testQuoteRefl)
  return runner

end QuoteTests

/-! ## Zonk Tests for Equality -/

namespace ZonkTests

/-- Test: Zonk equality type preserves structure -/
def testZonkEq : IO TestResult := do
  let ty := testIntTy
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 2
  let eq := mkTestEq ty lhs rhs
  match (zonkValue eq).run' with
  | .ok (.vDataType id [.vDataType ⟨1001, "test", "Int32"⟩ [], .vIntLit 1, .vIntLit 2]) =>
    if id == eqTestId then return .passed
    else return .failed s!"unexpected zonk result id: {id.original}"
  | .ok v => return .failed s!"Expected vDataType (Eq form), got {v}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Zonk refl preserves structure -/
def testZonkRefl : IO TestResult := do
  let ty := testIntTy
  let x := Value.vIntLit 42
  let refl := mkTestRefl ty x
  match (zonkValue refl).run' with
  | .ok (.vConstructor name tag
      [.vDataType ⟨1001, "test", "Int32"⟩ [], .vIntLit 42] _) =>
    if name == reflTestName ∧ tag == reflTestTag then return .passed
    else return .failed s!"unexpected zonked refl ctor: {name.display}/{tag}"
  | .ok v => return .failed s!"Expected vConstructor (refl), got {v}"
  | .error e => return .failed s!"Unexpected error: {e}"


def run : IO TestRunner := do
  IO.println "  === Zonk Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "zonk_eq" (← testZonkEq)
  runner := runner.record "zonk_refl" (← testZonkRefl)
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
