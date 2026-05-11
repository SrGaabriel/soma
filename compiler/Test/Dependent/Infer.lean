/-
  Test.Dependent.Infer - Unit tests for the bidirectional type checker (Phase 2)

  Tests cover:
  - Basic type inference for literals and primitives
  - Pi type formation and checking
  - Sigma type formation and checking
  - Type annotation checking
  - Conversion/definitional equality
  - Error handling
-/

import Soma.Dependent
import Soma.Core
import Test.Fixtures

namespace Test.Dependent.Infer

open Soma.Dependent
open Soma (Unique)
open Soma.Core
open Soma.Syntax (Span)
open Test.Fixtures

/-- Helper to create a dummy span -/
def testSpan : Span := Span.uninhabited

/-- Helper to create a syntax name at test span -/
def synName (s : String) : Soma.Syntax.QualName := ⟨#[], s, testSpan⟩

/-- Helper to create a simple unique ID -/
def mkUnique (n : Nat) (name : String) : Soma.Unique :=
  ⟨n, "test", name⟩

/-- Synthetic test placeholders for the kernel-level primitive types -/
def testIntTy : Soma.Core.Value := .vDataType ⟨1001, "test", "Int32"⟩ []
def testBoolTy : Soma.Core.Value := .vDataType ⟨1002, "test", "Bool"⟩ []
def testStringTy : Soma.Core.Value := .vDataType ⟨1003, "test", "String"⟩ []

/-! ## Conversion Tests -/

namespace ConversionTests

/-- Test: Type universes are equal at same level -/
def testTypeEqualSameLevel : IO TestResult := do
  let v1 := Value.vType (Level.lit 0)
  let v2 := Value.vType (Level.lit 0)
  match (convert v1 v2).run' with
  | .ok true => return .passed
  | .ok false => return .failed "Type₀ should equal Type₀"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Type universes are different at different levels -/
def testTypeNotEqualDifferentLevel : IO TestResult := do
  let v1 := Value.vType (Level.lit 0)
  let v2 := Value.vType (Level.lit 1)
  match (convert v1 v2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "Type₀ should not equal Type₁"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Primitive types equal themselves -/
def testPrimTyEqual : IO TestResult := do
  let v1 := testIntTy
  let v2 := testIntTy
  match (convert v1 v2).run' with
  | .ok true => return .passed
  | .ok false => return .failed "Int should equal Int"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Different primitive types are not equal -/
def testPrimTyNotEqual : IO TestResult := do
  let v1 := testIntTy
  let v2 := testStringTy
  match (convert v1 v2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "Int should not equal String"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Integer literals equal themselves -/
def testIntLitEqual : IO TestResult := do
  let v1 := Value.vIntLit 42
  let v2 := Value.vIntLit 42
  match (convert v1 v2).run' with
  | .ok true => return .passed
  | .ok false => return .failed "42 should equal 42"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Different integer literals are not equal -/
def testIntLitNotEqual : IO TestResult := do
  let v1 := Value.vIntLit 42
  let v2 := Value.vIntLit 43
  match (convert v1 v2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "42 should not equal 43"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: String literals equal themselves -/
def testStringLitEqual : IO TestResult := do
  let v1 := Value.vStringLit "hello"
  let v2 := Value.vStringLit "hello"
  match (convert v1 v2).run' with
  | .ok true => return .passed
  | .ok false => return .failed "\"hello\" should equal \"hello\""
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Empty rows are equal -/
def testRowEmptyEqual : IO TestResult := do
  let v1 := Value.vRowEmpty
  let v2 := Value.vRowEmpty
  match (convert v1 v2).run' with
  | .ok true => return .passed
  | .ok false => return .failed "empty rows should be equal"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Label literals equal themselves -/
def testLabelLitEqual : IO TestResult := do
  let v1 := Value.vLabelLit "foo"
  let v2 := Value.vLabelLit "foo"
  match (convert v1 v2).run' with
  | .ok true => return .passed
  | .ok false => return .failed "'foo should equal 'foo"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Different label literals are not equal -/
def testLabelLitNotEqual : IO TestResult := do
  let v1 := Value.vLabelLit "foo"
  let v2 := Value.vLabelLit "bar"
  match (convert v1 v2).run' with
  | .ok false => return .passed
  | .ok true => return .failed "'foo should not equal 'bar"
  | .error e => return .failed s!"Unexpected error: {e}"

def run : IO TestRunner := do
  IO.println "  === Conversion Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "type_equal_same_level" (← testTypeEqualSameLevel)
  runner := runner.record "type_not_equal_different_level" (← testTypeNotEqualDifferentLevel)
  runner := runner.record "prim_ty_equal" (← testPrimTyEqual)
  runner := runner.record "prim_ty_not_equal" (← testPrimTyNotEqual)
  runner := runner.record "int_lit_equal" (← testIntLitEqual)
  runner := runner.record "int_lit_not_equal" (← testIntLitNotEqual)
  runner := runner.record "string_lit_equal" (← testStringLitEqual)
  runner := runner.record "row_empty_equal" (← testRowEmptyEqual)
  runner := runner.record "label_lit_equal" (← testLabelLitEqual)
  runner := runner.record "label_lit_not_equal" (← testLabelLitNotEqual)

  return runner

end ConversionTests

/-! ## TCM Tests -/

namespace TCMTests

/-- Test: Fresh metavariable creation -/
def testFreshMeta : IO TestResult := do
  let action : TCM MetaId := do
    let m1 ← TCM.freshMeta (.vType .zero)
    let m2 ← TCM.freshMeta (.vType .zero)
    if m1.id == 0 && m2.id == 1 then
      return m1
    else
      TCM.throw (.internalError "wrong meta IDs" testSpan)
  match action.run' with
  | .ok _ => return .passed
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Fresh level variable creation -/
def testFreshLevelVar : IO TestResult := do
  let action : TCM LevelVarId := do
    let l1 ← TCM.freshLevelVar "u"
    let l2 ← TCM.freshLevelVar "v"
    if l1.id == 0 && l2.id == 1 then
      return l1
    else
      TCM.throw (.internalError "wrong level IDs" testSpan)
  match action.run' with
  | .ok _ => return .passed
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Context extension and lookup -/
def testContextExtend : IO TestResult := do
  let action : TCM Bool := do
    -- Initially empty
    let lookup1 ← TCM.lookupLocal "x"
    if lookup1.isSome then
      TCM.throw (.internalError "x should not be in empty context" testSpan)
    -- Extend and lookup
    let xId := mkUnique 0 "x"
    TCM.withBinding "x" xId testIntTy .omega .explicit testSpan do
      let lookup2 ← TCM.lookupLocal "x"
      match lookup2 with
      | some entry =>
        if entry.name != "x" then
          TCM.throw (.internalError "wrong name" testSpan)
        return true
      | none =>
        TCM.throw (.internalError "x should be in extended context" testSpan)
  match action.run' with
  | .ok true => return .passed
  | .ok false => return .failed "Expected true"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Metavariable solving -/
def testMetaSolve : IO TestResult := do
  let action : TCM Bool := do
    let m ← TCM.freshMeta (.vType .zero)
    let solved1 ← TCM.isMetaSolved m
    if solved1 then
      TCM.throw (.internalError "meta should not be solved initially" testSpan)
    TCM.solveMeta m testIntTy
    let solved2 ← TCM.isMetaSolved m
    if !solved2 then
      TCM.throw (.internalError "meta should be solved after solveMeta" testSpan)
    return true
  match action.run' with
  | .ok true => return .passed
  | .ok false => return .failed "Expected true"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Fresh name generation -/
def testFreshName : IO TestResult := do
  let action : TCM Bool := do
    let n1 ← TCM.freshName "x"
    let n2 ← TCM.freshName "x"
    if n1 == n2 then
      TCM.throw (.internalError "fresh names should be different" testSpan)
    return true
  match action.run' with
  | .ok true => return .passed
  | .ok false => return .failed "Expected true"
  | .error e => return .failed s!"Unexpected error: {e}"

def run : IO TestRunner := do
  IO.println "  === TCM Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "fresh_meta" (← testFreshMeta)
  runner := runner.record "fresh_level_var" (← testFreshLevelVar)
  runner := runner.record "context_extend" (← testContextExtend)
  runner := runner.record "meta_solve" (← testMetaSolve)
  runner := runner.record "fresh_name" (← testFreshName)

  return runner

end TCMTests

/-! ## Error Tests -/

namespace ErrorTests

/-- Test: CheckPurpose.describe -/
def testCheckPurposeDescribe : IO TestResult := do
  let p1 := CheckPurpose.functionBody "foo"
  let p2 := CheckPurpose.general
  if p1.describe != "in return type of function 'foo'" then
    return .failed s!"wrong description: {p1.describe}"
  if p2.describe != "" then
    return .failed s!"general should have empty description: {p2.describe}"
  return .passed

/-- Test: UnifyFailure.message -/
def testUnifyFailureMessage : IO TestResult := do
  let f := UnifyFailure.headMismatch testIntTy testStringTy
  if !f.message.toSlice.contains "unify" then
    return .failed s!"message should mention 'unify': {f.message}"
  return .passed

/-- Test: TCError.toDiagnostic creates valid diagnostic -/
def testErrorToDiagnostic : IO TestResult := do
  let err := TCError.unboundVariable "x" testSpan #[]
  let diag := err.toDiagnostic
  if diag.message.isEmpty then
    return .failed "diagnostic message should not be empty"
  if diag.code.isNone then
    return .failed "diagnostic should have error code"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Error Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "check_purpose_describe" (← testCheckPurposeDescribe)
  runner := runner.record "unify_failure_message" (← testUnifyFailureMessage)
  runner := runner.record "error_to_diagnostic" (← testErrorToDiagnostic)

  return runner

end ErrorTests

/-! ## Inference Tests -/

namespace InferTests

open Soma.Core (PrimType)

/-- Test: Infer integer literal type -/
def testInferIntLit : IO TestResult := do
  let expr : Soma.Syntax.Expr := .lit (.int 42 testSpan)
  match typeInfer expr with
  | .ok (ty, _, _) =>
    return .failed s!"Expected internal error for missing `Int` wired registration, got type {ty}"
  | .error e =>
    let msg := toString e
    if (msg.splitOn "int").length > 1 || (msg.splitOn "Int").length > 1 then
      return .passed
    else
      return .failed s!"Expected error about missing `Int` wired role, got: {msg}"

/-- Test: Infer string literal type -/
def testInferStringLit : IO TestResult := do
  let expr : Soma.Syntax.Expr := .lit (.string "hello" testSpan)
  match typeInfer expr with
  | .ok (ty, _, _) =>
    return .failed s!"Expected internal error for missing `String` wired registration, got type {ty}"
  | .error e =>
    let msg := toString e
    if (msg.splitOn "string").length > 1 || (msg.splitOn "String").length > 1 then
      return .passed
    else
      return .failed s!"Expected error about missing `String` wired role, got: {msg}"

/-- Test: Infer boolean literal type -/
def testInferBoolLit : IO TestResult := do
  let expr : Soma.Syntax.Expr := .lit (.bool true testSpan)
  match typeInfer expr with
  | .ok (ty, _, _) =>
    return .failed s!"Expected internal error for missing `Bool` wired registration, got type {ty}"
  | .error e =>
    let msg := toString e
    if (msg.splitOn "Bool").length > 1 || (msg.splitOn "bool").length > 1 then
      return .passed
    else
      return .failed s!"Expected error about missing `Bool` wired role, got: {msg}"

/-- Test: Infer Type universe -/
def testInferTypeUniverse : IO TestResult := do
  let expr : Soma.Syntax.Expr := .var (synName "Type")
  match typeInfer expr with
  | .ok (ty, _, _) =>
    match ty with
    | .vType (.succ _) => return .passed
    | .vType l => return .failed s!"Expected Type with successor level, got Type with level {l}"
    | _ => return .failed s!"Expected Type, got {ty}"
  | .error e => return .failed s!"Inference failed: {e}"

/-- Test: Primitive type names are not hardcoded in inference -/
def testInferPrimTy : IO TestResult := do
  let expr : Soma.Syntax.Expr := .var (synName "Int32")
  match typeInfer expr with
  | .ok (_, _, state) =>
    if state.errors.any (fun e => match e with | .unboundVariable .. => true | _ => false) then
      return .passed
    else
      return .failed "Expected unbound variable error for Int without wired-in registration"
  | .error _ => return .passed

/-- Test: Infer tuple -/
def testInferTuple : IO TestResult := do
  let expr : Soma.Syntax.Expr :=
    .tuple #[(.lit (.int 1 testSpan)), (.lit (.int 2 testSpan))] testSpan
  match typeInfer expr with
  | .ok (ty, _, _) =>
    return .failed s!"Expected error but inference succeeded with {ty}"
  | .error _ => return .passed

def run : IO TestRunner := do
  IO.println "  === Inference Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "infer_int_lit" (← testInferIntLit)
  runner := runner.record "infer_string_lit" (← testInferStringLit)
  runner := runner.record "infer_bool_lit" (← testInferBoolLit)
  runner := runner.record "infer_type_universe" (← testInferTypeUniverse)
  runner := runner.record "infer_prim_ty" (← testInferPrimTy)
  runner := runner.record "infer_tuple" (← testInferTuple)

  return runner

end InferTests

/-! ## Check Tests -/

namespace CheckTests

open Soma.Core (PrimType)

/-- Test: Check integer literal against Int -/
def testCheckIntAgainstInt : IO TestResult := do
  let expr : Soma.Syntax.Expr := .lit (.int 42 testSpan)
  match typeCheck expr (.vDataType ⟨999_999, "test", "Int"⟩ []) with
  | .ok _ => return .failed "Expected internal error for missing `Int` wired registration"
  | .error _ => return .passed

/-- Test: Check string literal against String -/
def testCheckStringAgainstString : IO TestResult := do
  let expr : Soma.Syntax.Expr := .lit (.string "hello" testSpan)
  match typeCheck expr (.vDataType ⟨999_999, "test", "String"⟩ []) with
  | .ok _ => return .failed "Expected internal error for missing `String` wired registration"
  | .error _ => return .passed

/-- Test: Check Type₀ against Type₁ -/
def testCheckTypeAgainstType : IO TestResult := do
  let expr : Soma.Syntax.Expr := .var (synName "Type")
  match typeCheck expr (.vType (.lit 1)) with
  | .ok _ => return .passed
  | .error e => return .failed s!"Check failed: {e}"

/-- Test: Check pair against Sigma type -/
def testCheckPairAgainstSigma : IO TestResult := do
  let fst : Soma.Syntax.Expr := .lit (.int 1 testSpan)
  let snd : Soma.Syntax.Expr := .lit (.int 2 testSpan)
  let pairExpr : Soma.Syntax.Expr := .tuple #[fst, snd] testSpan
  let intTy := Value.vDataType ⟨999_999, "test", "Int"⟩ []
  let pairTy := Value.vDataType ⟨999_999, "test", "Pair"⟩ [intTy, intTy]
  match typeCheck pairExpr pairTy with
  | .ok _ => return .failed "Expected error but check succeeded"
  | .error _ =>
    return .passed

/-- Test: Check if-then-else with matching branch types -/
def testCheckIfThenElse : IO TestResult := do
  let cond : Soma.Syntax.Expr := .lit (.bool true testSpan)
  let then_ : Soma.Syntax.Expr := .lit (.int 1 testSpan)
  let else_ : Soma.Syntax.Expr := .lit (.int 2 testSpan)
  let ifExpr : Soma.Syntax.Expr := .if_ cond then_ else_ testSpan
  match typeCheck ifExpr (.vDataType ⟨999_999, "test", "Int"⟩ []) with
  | .ok _ => return .failed "Expected internal error for missing wired-in registrations"
  | .error _ => return .passed

def run : IO TestRunner := do
  IO.println "  === Check Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "check_int_against_int" (← testCheckIntAgainstInt)
  runner := runner.record "check_string_against_string" (← testCheckStringAgainstString)
  runner := runner.record "check_type_against_type" (← testCheckTypeAgainstType)
  runner := runner.record "check_pair_against_sigma" (← testCheckPairAgainstSigma)
  runner := runner.record "check_if_then_else" (← testCheckIfThenElse)

  return runner

end CheckTests

/-! ## Usage Tracking Tests -/

namespace UsageTests

/-- Test: Variable usage is recorded -/
def testUsageRecorded : IO TestResult := do
  let xId := mkUnique 0 "x"
  let action : TCM Nat := do
    TCM.useVar xId
    TCM.getUsage xId
  match action.run' with
  | .ok count =>
    if count == 1 then return .passed
    else return .failed s!"Expected 1, got {count}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Multiple usages accumulate -/
def testUsageAccumulates : IO TestResult := do
  let xId := mkUnique 0 "x"
  let action : TCM Nat := do
    TCM.useVar xId 1
    TCM.useVar xId 1
    TCM.getUsage xId
  match action.run' with
  | .ok count =>
    if count == 2 then return .passed  -- 1 + 1 = 2
    else return .failed s!"Expected 2, got {count}"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Zero usage doesn't change -/
def testZeroUsage : IO TestResult := do
  let xId := mkUnique 0 "x"
  let action : TCM Nat := do
    TCM.useVar xId 0
    TCM.getUsage xId
  match action.run' with
  | .ok count =>
    if count == 0 then return .passed
    else return .failed s!"Expected 0, got {count}"
  | .error e => return .failed s!"Unexpected error: {e}"

def run : IO TestRunner := do
  IO.println "  === Usage Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "usage_recorded" (← testUsageRecorded)
  runner := runner.record "usage_accumulates" (← testUsageAccumulates)
  runner := runner.record "zero_usage" (← testZeroUsage)

  return runner

end UsageTests

/-! ## Implicit Propagation Tests (Improvement #2) -/

namespace ImplicitPropagationTests

open Soma.Core (PrimType)

/-- Helper to create a polymorphic identity function type: forall {a : Type}. a -> a -/
def mkIdType : TCM Value := do
  -- Create Type at level 0
  let typeTy := Value.vType .zero
  -- Create the codomain closure: a -> a
  -- When applied to a type 'a', returns Pi(x : a) -> a
  let innerCod := Closure.const "x" typeTy  -- Returns Type (placeholder, will be overwritten)
  let outerCod := Closure.const "a" (Value.vPi .omega .explicit "x" typeTy innerCod)
  -- forall {a : Type}. a -> a
  return Value.vPi .omega .implicit "a" typeTy outerCod

/-- Test: Expected type propagation solves implicits immediately
    When checking `id 5` against `Int`, the implicit `a` should be solved to `Int`
    before we even check the argument `5`. -/
def testExpectedTypeSolvesImplicit : IO TestResult := do
  -- This test verifies the bidirectional propagation mechanism
  -- We create a scenario where expected type info should flow backward
  let action : TCM Bool := do
    -- Create a metavariable for the implicit type parameter
    let metaId ← TCM.freshMeta (.vType .zero)
    let metaVal := Value.vNeutral (.vType .zero) (.nMeta metaId)

    -- Try to solve the meta from expected type Int
    let solved ← trySolveMetaFromExpected metaId testIntTy

    -- Check if it was solved
    if solved then
      match ← TCM.lookupMeta metaId with
      | some info =>
        match info.solution with
        | some sol =>
          -- Verify the solution is Int
          match sol with
          | .vDataType ⟨1001, "test", "Int32"⟩ [] => return true
          | _ => return false
        | none => return false
      | none => return false
    else
      return false

  match action.run' with
  | .ok true => return .passed
  | .ok false => return .failed "Expected implicit to be solved to Int"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Greedy solving resolves constraints immediately -/
def testGreedySolving : IO TestResult := do
  let action : TCM Bool := do
    -- Create two metavariables
    let meta1 ← TCM.freshMeta (.vType .zero)
    let meta2 ← TCM.freshMeta (.vType .zero)
    let metaVal1 := Value.vNeutral (.vType .zero) (.nMeta meta1)
    let metaVal2 := Value.vNeutral (.vType .zero) (.nMeta meta2)

    -- Postpone a constraint: ?meta1 = Int
    TCM.postpone (.unify metaVal1 testIntTy testSpan)

    let _ ← solveConstraints

    -- Check if meta1 was solved
    let solved1 ← TCM.isMetaSolved meta1
    return solved1

  match action.run' with
  | .ok true => return .passed
  | .ok false => return .failed "Expected greedy solving to resolve the constraint"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: extractResultTypeAfterArgs correctly projects result type -/
def testExtractResultType : IO TestResult := do
  let action : TCM Bool := do
    -- Create type: Int -> Bool -> String
    let stringTy := testStringTy
    let boolToString := Value.vPi .omega .explicit "y" testBoolTy (Closure.const "y" stringTy)
    let intToBoolToString := Value.vPi .omega .explicit "x" testIntTy (Closure.const "x" boolToString)

    -- Extract result type after 2 explicit arguments
    match ← projectResultTypeWithMetas intToBoolToString 2 #[] with
    | some resultTy =>
      -- Should be String
      let resultTy' ← force resultTy
      match resultTy' with
      | .vDataType ⟨1003, "test", "String"⟩ [] => return true
      | _ => return false
    | none => return false

  match action.run' with
  | .ok true => return .passed
  | .ok false => return .failed "Expected result type to be String"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: extractResultTypeAfterArgs handles implicit parameters -/
def testExtractResultTypeWithImplicits : IO TestResult := do
  let action : TCM Bool := do
    -- Create type: forall {a : Type}. a -> a
    -- When we extract result after 1 explicit arg, we should get 'a' (a metavariable)
    let typeTy := Value.vType .zero
    let aClosure := Closure.const "x" typeTy  -- Placeholder
    let aToA := Value.vPi .omega .explicit "x" typeTy aClosure
    let forallAToA := Value.vPi .omega .implicit "a" typeTy (Closure.const "a" aToA)

    -- Extract result type after 1 explicit argument (skipping the implicit)
    match ← projectResultTypeWithMetas forallAToA 1 #[] with
    | some resultTy =>
      -- Result should be some type (the implicit 'a' instantiated with a meta)
      return true  -- Just verify we get a result
    | none => return false

  match action.run' with
  | .ok true => return .passed
  | .ok false => return .failed "Expected to extract result type through implicit"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Constraint solving makes progress -/
def testConstraintSolvingProgress : IO TestResult := do
  let action : TCM Bool := do
    -- Create a metavariable and unify it with a concrete type
    let metaId ← TCM.freshMeta (.vType .zero)
    let metaVal := Value.vNeutral (.vType .zero) (.nMeta metaId)

    -- Directly unify (should solve immediately)
    unify metaVal testBoolTy

    -- Check if solved
    TCM.isMetaSolved metaId

  match action.run' with
  | .ok true => return .passed
  | .ok false => return .failed "Expected meta to be solved after unification"
  | .error e => return .failed s!"Unexpected error: {e}"

/-- Test: Multiple constraints can be solved in sequence -/
def testMultipleConstraintsSolving : IO TestResult := do
  let action : TCM Bool := do
    -- Create multiple metas
    let meta1 ← TCM.freshMeta (.vType .zero)
    let meta2 ← TCM.freshMeta (.vType .zero)
    let metaVal1 := Value.vNeutral (.vType .zero) (.nMeta meta1)
    let metaVal2 := Value.vNeutral (.vType .zero) (.nMeta meta2)

    -- Unify both with concrete types
    unify metaVal1 testIntTy
    unify metaVal2 testStringTy

    -- Check both are solved
    let solved1 ← TCM.isMetaSolved meta1
    let solved2 ← TCM.isMetaSolved meta2
    return solved1 && solved2

  match action.run' with
  | .ok true => return .passed
  | .ok false => return .failed "Expected both metas to be solved"
  | .error e => return .failed s!"Unexpected error: {e}"

def run : IO TestRunner := do
  IO.println "  === Implicit Propagation Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "expected_type_solves_implicit" (← testExpectedTypeSolvesImplicit)
  runner := runner.record "greedy_solving" (← testGreedySolving)
  runner := runner.record "extract_result_type" (← testExtractResultType)
  runner := runner.record "extract_result_type_with_implicits" (← testExtractResultTypeWithImplicits)
  runner := runner.record "constraint_solving_progress" (← testConstraintSolvingProgress)
  runner := runner.record "multiple_constraints_solving" (← testMultipleConstraintsSolving)

  return runner

end ImplicitPropagationTests

/-! ## Main Test Runner -/

def run : IO TestRunner := do
  IO.println "=== Dependent Types Infer Tests (Phase 2) ==="
  IO.println ""

  let conversionRunner ← ConversionTests.run
  conversionRunner.printSummary "Conversion"

  let tcmRunner ← TCMTests.run
  tcmRunner.printSummary "TCM"

  let errorRunner ← ErrorTests.run
  errorRunner.printSummary "Error"

  let inferRunner ← InferTests.run
  inferRunner.printSummary "Inference"

  let checkRunner ← CheckTests.run
  checkRunner.printSummary "Check"

  let usageRunner ← UsageTests.run
  usageRunner.printSummary "Usage"

  let implicitRunner ← ImplicitPropagationTests.run
  implicitRunner.printSummary "Implicit Propagation"

  IO.println ""

  let combined := conversionRunner.merge tcmRunner |>.merge errorRunner
    |>.merge inferRunner |>.merge checkRunner |>.merge usageRunner |>.merge implicitRunner

  IO.println s!"Total: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Dependent.Infer
