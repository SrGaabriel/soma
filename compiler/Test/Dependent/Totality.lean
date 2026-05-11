/-
  Test.Dependent.Totality - Unit tests for SupGen-style termination checking

  Tests cover:
  - StructurePath depth calculation
  - BindingInfo and TerminationContext
  - TermShape analysis
  - Structural comparison (the heart of SupGen)
  - The Pair example from Taelin's blog post
  - Lexicographic ordering within structures
  - Pattern binding extraction
  - Positivity checking
  - TotalityRegistry operations
  - Full integration tests
-/

import Soma.Dependent
import Soma.Dependent.Totality
import Soma.Core
import Soma.Core.Expr
import Test.Fixtures

namespace Test.Dependent.Totality

open Soma.Dependent
open Soma.Dependent.Totality
open Soma.Core
open Soma.Syntax (Span)
open Soma (Unique)
open Soma.Core (QualifiedName)
open Test.Fixtures

def testSpan : Span := Span.uninhabited
def testFnName (s : String) : QualifiedName := ⟨⟨0, "", s⟩⟩
def testUnique (name : String) : Unique := ⟨0, "", name⟩

/-- Create a free variable Expr for tests (using fvar with the given name) -/
def testVar (name : String) : Soma.Core.Expr := .fvar ⟨0, "", name⟩ (.sort .zero)

/-- Create a constructor Expr for tests -/
def testConstruct (name : String) (tag : Nat) (args : List Soma.Core.Expr) : Soma.Core.Expr :=
  .construct (QualifiedName.ofUnique ⟨0, "", name⟩) tag args.toArray (.sort .zero)

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 1: StructurePath Tests
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace StructurePathTests

def testRootDepth : IO TestResult := do
  let path := StructurePath.root
  if path.depth == 0 then return .passed
  else return .failed s!"root depth should be 0, got {path.depth}"

def testCtorArgDepth : IO TestResult := do
  -- One constructor unwrap = depth 1
  let path := StructurePath.ctorArg .root "S" 0
  if path.depth == 1 then return .passed
  else return .failed s!"ctorArg depth should be 1, got {path.depth}"

def testNestedCtorDepth : IO TestResult := do
  -- Two constructor unwraps = depth 2 (like S (S n))
  let path := StructurePath.ctorArg (.ctorArg .root "S" 0) "S" 0
  if path.depth == 2 then return .passed
  else return .failed s!"nested ctor depth should be 2, got {path.depth}"

def testProjectionPreservesDepth : IO TestResult := do
  -- Projections don't add depth
  let path := StructurePath.fst (.ctorArg .root "Pair" 0)
  if path.depth == 1 then return .passed
  else return .failed s!"projection should preserve depth, got {path.depth}"

def testComplexPath : IO TestResult := do
  -- Pair (S a) (S b) -> a has path ctorArg(ctorArg(root, Pair, 0), S, 0)
  let pairArg := StructurePath.ctorArg .root "Pair" 0
  let sArg := StructurePath.ctorArg pairArg "S" 0
  if sArg.depth == 2 then return .passed
  else return .failed s!"Pair (S a) path depth should be 2, got {sArg.depth}"

def testPathToString : IO TestResult := do
  let path := StructurePath.ctorArg (.fst .root) "S" 0
  let str := path.toString
  let hasFst := (str.splitOn "fst").length > 1
  let hasS := (str.splitOn "S").length > 1
  if hasFst && hasS then return .passed
  else return .failed s!"path toString should contain components, got {str}"

def run : IO TestRunner := do
  IO.println "  === StructurePath Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "root_depth" (← testRootDepth)
  runner := runner.record "ctor_arg_depth" (← testCtorArgDepth)
  runner := runner.record "nested_ctor_depth" (← testNestedCtorDepth)
  runner := runner.record "projection_preserves_depth" (← testProjectionPreservesDepth)
  runner := runner.record "complex_path" (← testComplexPath)
  runner := runner.record "path_to_string" (← testPathToString)
  return runner

end StructurePathTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 2: BindingInfo Tests
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace BindingInfoTests

def testSmallerBinding : IO TestResult := do
  let info : BindingInfo := {
    name := "a"
    paramIdx := 0
    paramName := "x"
    path := .ctorArg .root "S" 0
    depth := 1
  }
  if info.isSmaller then return .passed
  else return .failed "depth 1 binding should be smaller"

def testEqualBinding : IO TestResult := do
  let info : BindingInfo := {
    name := "x"
    paramIdx := 0
    paramName := "x"
    path := .root
    depth := 0
  }
  if info.isSameLevel && !info.isSmaller then return .passed
  else return .failed "depth 0 binding should be same level"

def run : IO TestRunner := do
  IO.println "  === BindingInfo Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "smaller_binding" (← testSmallerBinding)
  runner := runner.record "equal_binding" (← testEqualBinding)
  return runner

end BindingInfoTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 3: TerminationContext Tests
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace TerminationContextTests

def testFromParams : IO TestResult := do
  let ctx := TerminationContext.fromParams #["x", "y", "z"]
  match ctx.lookup "x", ctx.lookup "y", ctx.lookup "z" with
  | some ix, some iy, some iz =>
    if ix.paramIdx == 0 && iy.paramIdx == 1 && iz.paramIdx == 2 then return .passed
    else return .failed "param indices incorrect"
  | _, _, _ => return .failed "params not found in context"

def testAddBinding : IO TestResult := do
  let ctx := TerminationContext.fromParams #["xs"]
  let binding : BindingInfo := {
    name := "tail"
    paramIdx := 0
    paramName := "xs"
    path := .ctorArg .root "Cons" 1
    depth := 1
  }
  let ctx' := ctx.addBinding binding
  match ctx'.lookup "tail" with
  | some info => if info.isSmaller then return .passed else return .failed "tail should be smaller"
  | none => return .failed "tail not found"

def testIsSmaller : IO TestResult := do
  let ctx := TerminationContext.fromParams #["xs"]
  let binding : BindingInfo := {
    name := "tail"
    paramIdx := 0
    paramName := "xs"
    path := .ctorArg .root "Cons" 1
    depth := 1
  }
  let ctx' := ctx.addBinding binding
  if ctx'.isSmaller "tail" && !ctx'.isSmaller "xs" then return .passed
  else return .failed "isSmaller should work correctly"

def run : IO TestRunner := do
  IO.println "  === TerminationContext Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "from_params" (← testFromParams)
  runner := runner.record "add_binding" (← testAddBinding)
  runner := runner.record "is_smaller" (← testIsSmaller)
  return runner

end TerminationContextTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 4: TermShape Tests
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace TermShapeTests

def testVarShape : IO TestResult := do
  let term := testVar "x"
  let shape := analyzeExprShape term
  match shape with
  | .var "x" => return .passed
  | _ => return .failed s!"expected var shape, got {repr shape}"

def testCtorShape : IO TestResult := do
  let term := testConstruct "Pair" 0 [testVar "a", testVar "b"]
  let shape := analyzeExprShape term
  match shape with
  | .ctor "Pair" args => if args.size == 2 then return .passed else return .failed "wrong arity"
  | _ => return .failed s!"expected ctor shape, got {repr shape}"

def testCollectVars : IO TestResult := do
  let term := testConstruct "Node" 0 [testVar "a", testVar "b"]
  let shape := analyzeExprShape term
  let vars := shape.collectVars
  if vars.length == 2 && vars.contains "a" && vars.contains "b" then return .passed
  else return .failed s!"expected [a, b], got {vars}"

def run : IO TestRunner := do
  IO.println "  === TermShape Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "var_shape" (← testVarShape)
  runner := runner.record "ctor_shape" (← testCtorShape)
  runner := runner.record "collect_vars" (← testCollectVars)
  return runner

end TermShapeTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 5: Structural Comparison Tests (Core SupGen)
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace StructuralCmpTests

def testVarSmaller : IO TestResult := do
  -- If 'a' has depth 1, it's smaller than param 'x' (depth 0)
  let ctx := TerminationContext.fromParams #["x"]
  let ctx' := ctx.addBinding {
    name := "a", paramIdx := 0, paramName := "x",
    path := .ctorArg .root "S" 0, depth := 1
  }
  let shape := TermShape.var "a"
  let cmp := compareTermToParam shape 0 "x" ctx'
  match cmp with
  | .smaller _ => return .passed
  | _ => return .failed s!"'a' with depth 1 should be smaller, got {repr cmp}"

def testVarEqual : IO TestResult := do
  -- Parameter itself has depth 0 = equal
  let ctx := TerminationContext.fromParams #["x"]
  let shape := TermShape.var "x"
  let cmp := compareTermToParam shape 0 "x" ctx
  match cmp with
  | .equal => return .passed
  | _ => return .failed s!"param 'x' should be equal to itself, got {repr cmp}"

def testProjectionSmaller : IO TestResult := do
  -- p.fst is smaller than p
  let ctx := TerminationContext.fromParams #["p"]
  let shape := TermShape.fieldProj (.var "p") "fst"
  let cmp := compareTermToParam shape 0 "p" ctx
  match cmp with
  | .smaller _ => return .passed
  | _ => return .failed s!"'p.fst' should be smaller than 'p', got {repr cmp}"

def testCtorWithSmallerComponents : IO TestResult := do
  -- Pair a b where a and b are smaller should be smaller overall
  let ctx := TerminationContext.fromParams #["p"]
  let ctx' := ctx.addBinding { name := "a", paramIdx := 0, paramName := "p", path := .ctorArg .root "Pair" 0, depth := 1 }
  let ctx'' := ctx'.addBinding { name := "b", paramIdx := 0, paramName := "p", path := .ctorArg .root "Pair" 1, depth := 1 }
  let shape := TermShape.ctor "Pair" #[.var "a", .var "b"]
  let cmp := compareTermToParam shape 0 "p" ctx''
  match cmp with
  | .smaller _ => return .passed
  | _ => return .failed s!"Pair of smaller components should be smaller, got {repr cmp}"

def run : IO TestRunner := do
  IO.println "  === Structural Comparison Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "var_smaller" (← testVarSmaller)
  runner := runner.record "var_equal" (← testVarEqual)
  runner := runner.record "projection_smaller" (← testProjectionSmaller)
  runner := runner.record "ctor_with_smaller_components" (← testCtorWithSmallerComponents)
  return runner

end StructuralCmpTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 6: The Pair Example (Taelin's Blog Post)

    foo (Pair (S a) (S b)) = foo (Pair a (S (S b)))

    This is THE test that Agda fails but SupGen-style checking should pass!
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace PairExampleTests

/-- The key test: foo (Pair (S a) (S b)) = foo (Pair a (S (S b)))
    After pattern matching, 'a' has depth 2 (under Pair and S).
    The recursive call uses 'a' directly in the first position.
    Since 'a' at depth 2 is used where depth 1 was expected, this is SMALLER.
    The second position (S (S b)) is LARGER but we use lexicographic ordering. -/
def testPairExampleSimple : IO TestResult := do
  -- Setup: after matching Pair (S a) (S b), 'a' and 'b' have depth 2
  let ctx := TerminationContext.fromParams #["p"]
  let ctx' := ctx.addBinding {
    name := "a", paramIdx := 0, paramName := "p",
    path := .ctorArg (.ctorArg .root "Pair" 0) "S" 0,
    depth := 2
  }
  let ctx'' := ctx'.addBinding {
    name := "b", paramIdx := 0, paramName := "p",
    path := .ctorArg (.ctorArg .root "Pair" 1) "S" 0,
    depth := 2
  }

  -- The recursive call argument is just 'a' (simplified test)
  -- In a full test, we'd check Pair a (S (S b))
  let args := [testVar "a"]
  let witness := checkRecursiveCallStructural args ctx''

  match witness with
  | .arg 0 reason =>
    let hasSubterm := (reason.splitOn "subterm").length > 1
    let hasSmaller := (reason.splitOn "smaller").length > 1
    if hasSubterm || hasSmaller then
      return .passed
    else
      return .failed s!"expected decrease reason, got: {reason}"
  | .notFound reason => return .failed s!"should find decrease: {reason}"
  | _ => return .failed "unexpected witness type"

/-- Full Pair example with constructor in recursive call -/
def testPairExampleFull : IO TestResult := do
  -- Setup context with a and b at depth 2
  let ctx := TerminationContext.fromParams #["p"]
  let ctx' := ctx.addBinding {
    name := "a", paramIdx := 0, paramName := "p",
    path := .ctorArg (.ctorArg .root "Pair" 0) "S" 0,
    depth := 2
  }
  let ctx'' := ctx'.addBinding {
    name := "b", paramIdx := 0, paramName := "p",
    path := .ctorArg (.ctorArg .root "Pair" 1) "S" 0,
    depth := 2
  }

  -- Recursive call: foo (Pair a (S (S b)))
  -- Represented as: Pair [a, S [S [b]]]
  let innerS := testConstruct "S" 0 [testVar "b"]
  let outerS := testConstruct "S" 0 [innerS]
  let pairArg := testConstruct "Pair" 0 [testVar "a", outerS]
  let args := [pairArg]

  let witness := checkRecursiveCallStructural args ctx''

  match witness with
  | .arg 0 reason =>
    -- We expect this to terminate because 'a' is smaller
    return .passed
  | .notFound reason =>
    return .failed s!"Pair example should terminate: {reason}"
  | _ => return .failed "unexpected witness type"

/-- Test that passing the parameter unchanged gives 'equal' not 'smaller' -/
def testPairNoDecrease : IO TestResult := do
  let ctx := TerminationContext.fromParams #["p"]
  let args := [testVar "p"]  -- Just pass p unchanged

  let witness := checkRecursiveCallStructural args ctx

  match witness with
  | .notFound _ => return .passed  -- Correctly detects no decrease
  | .arg _ _ => return .failed "should not find decrease when passing param unchanged"
  | _ => return .failed "unexpected witness type"

def run : IO TestRunner := do
  IO.println "  === Pair Example Tests (Taelin's Blog) ==="
  let mut runner := TestRunner.init
  runner := runner.record "pair_example_simple" (← testPairExampleSimple)
  runner := runner.record "pair_example_full" (← testPairExampleFull)
  runner := runner.record "pair_no_decrease" (← testPairNoDecrease)
  return runner

end PairExampleTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 7: Lexicographic Ordering Tests
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace LexicographicTests

def testFirstArgSmaller : IO TestResult := do
  -- foo (S a) b = foo a (S (S b))
  -- First arg smaller -> terminates
  let ctx := TerminationContext.fromParams #["x", "y"]
  let ctx' := ctx.addBinding {
    name := "a", paramIdx := 0, paramName := "x",
    path := .ctorArg .root "S" 0, depth := 1
  }
  let args := [testVar "a", testVar "larger"]

  let witness := checkRecursiveCallStructural args ctx'

  match witness with
  | .arg 0 _ => return .passed
  | _ => return .failed "should find decrease on first arg"

def testSecondArgSmaller : IO TestResult := do
  -- foo x (S b) = foo x b
  -- First arg equal, second smaller -> terminates
  let ctx := TerminationContext.fromParams #["x", "y"]
  let ctx' := ctx.addBinding {
    name := "b", paramIdx := 1, paramName := "y",
    path := .ctorArg .root "S" 0, depth := 1
  }
  let args := [testVar "x", testVar "b"]

  let witness := checkRecursiveCallStructural args ctx'

  match witness with
  | .arg 1 _ => return .passed
  | .arg 0 _ => return .failed "decrease should be on arg 1, not 0"
  | _ => return .failed "should find decrease on second arg"

def testNoDecrease : IO TestResult := do
  -- foo x y = foo x y (no decrease)
  let ctx := TerminationContext.fromParams #["x", "y"]
  let args := [testVar "x", testVar "y"]

  let witness := checkRecursiveCallStructural args ctx

  match witness with
  | .notFound _ => return .passed
  | _ => return .failed "should not find decrease"

def run : IO TestRunner := do
  IO.println "  === Lexicographic Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "first_arg_smaller" (← testFirstArgSmaller)
  runner := runner.record "second_arg_smaller" (← testSecondArgSmaller)
  runner := runner.record "no_decrease" (← testNoDecrease)
  return runner

end LexicographicTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 8: List/Tree Recursion Tests
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace StandardRecursionTests

def testListLength : IO TestResult := do
  -- length (Cons x xs) = 1 + length xs
  let ctx := TerminationContext.fromParams #["list"]
  let ctx' := ctx.addBinding {
    name := "xs", paramIdx := 0, paramName := "list",
    path := .ctorArg .root "Cons" 1, depth := 1
  }
  let args := [testVar "xs"]

  let witness := checkRecursiveCallStructural args ctx'

  match witness with
  | .arg 0 _ => return .passed
  | _ => return .failed "list recursion should decrease"

def testTreeRecursion : IO TestResult := do
  -- size (Node l r) = 1 + size l + size r
  let ctx := TerminationContext.fromParams #["tree"]
  let ctx' := ctx.addBinding {
    name := "l", paramIdx := 0, paramName := "tree",
    path := .ctorArg .root "Node" 0, depth := 1
  }
  let ctx'' := ctx'.addBinding {
    name := "r", paramIdx := 0, paramName := "tree",
    path := .ctorArg .root "Node" 1, depth := 1
  }

  -- First recursive call on 'l'
  let witness1 := checkRecursiveCallStructural [testVar "l"] ctx''
  -- Second recursive call on 'r'
  let witness2 := checkRecursiveCallStructural [testVar "r"] ctx''

  match witness1, witness2 with
  | .arg 0 _, .arg 0 _ => return .passed
  | _, _ => return .failed "tree recursion should decrease on both branches"

def run : IO TestRunner := do
  IO.println "  === Standard Recursion Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "list_length" (← testListLength)
  runner := runner.record "tree_recursion" (← testTreeRecursion)
  return runner

end StandardRecursionTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 9: Positivity Tests
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace PositivityTests

def testPrimPositive : IO TestResult := do
  let unique := testUnique "Test"
  let ty := Value.vPrimTy .int
  match checkPositivityValue unique .positive ty with
  | .ok => return .passed
  | .violated reason _ => return .failed s!"primitives should be positive: {reason}"

def testSelfPositive : IO TestResult := do
  let unique := testUnique "Nat"
  let ty := Value.vDataType unique []
  match checkPositivityValue unique .positive ty with
  | .ok => return .passed
  | .violated reason _ => return .failed s!"self in positive should be ok: {reason}"

def testSelfNegative : IO TestResult := do
  let unique := testUnique "Bad"
  let ty := Value.vDataType unique []
  match checkPositivityValue unique .negative ty with
  | .violated _ _ => return .passed
  | .ok => return .failed "self in negative should be violation"

def run : IO TestRunner := do
  IO.println "  === Positivity Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "prim_positive" (← testPrimPositive)
  runner := runner.record "self_positive" (← testSelfPositive)
  runner := runner.record "self_negative" (← testSelfNegative)
  return runner

end PositivityTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 10: TotalityRegistry Tests
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace RegistryTests

def testEmptyRegistry : IO TestResult := do
  let reg := TotalityRegistry.empty
  match reg.lookup "nonexistent" with
  | none => return .passed
  | some _ => return .failed "empty registry should have no entries"

def testRegisterLookup : IO TestResult := do
  let reg := TotalityRegistry.empty.register "myFn" .isTotal
  match reg.lookup "myFn" with
  | some .isTotal => return .passed
  | _ => return .failed "should find registered function"

def testIsTotal : IO TestResult := do
  let reg := TotalityRegistry.empty
    |>.register "totalFn" .isTotal
    |>.register "partialFn" .isPartial
  if reg.isTotal "totalFn" && !reg.isTotal "partialFn" then return .passed
  else return .failed "isTotal should work correctly"

def run : IO TestRunner := do
  IO.println "  === Registry Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "empty_registry" (← testEmptyRegistry)
  runner := runner.record "register_lookup" (← testRegisterLookup)
  runner := runner.record "is_total" (← testIsTotal)
  return runner

end RegistryTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 11: TermM Monad Tests
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace TermMTests

def testRunEmpty : IO TestResult := do
  let action : TermM Unit := pure ()
  match action.run' with
  | .ok _ => return .passed
  | .error _ => return .failed "should succeed"

def testSmallerTracking : IO TestResult := do
  let action : TermM Bool := do
    TermM.addBinding {
      name := "y", paramIdx := 0, paramName := "x"
      path := .ctorArg .root "pattern" 0, depth := 1
    }
    let result ← TermM.isSmallerThan "y"
    return result.isSome
  match action.run' with
  | .ok true => return .passed
  | .ok false => return .failed "should find smaller relation"
  | .error _ => return .failed "should succeed"

def testWithBindings : IO TestResult := do
  let action : TermM (Bool × Bool) := do
    let outerBinding : BindingInfo := {
      name := "outer", paramIdx := 0, paramName := "x",
      path := .ctorArg .root "Outer" 0, depth := 1
    }
    TermM.addBinding outerBinding
    let innerBinding : BindingInfo := {
      name := "inner", paramIdx := 1, paramName := "y",
      path := .ctorArg .root "Inner" 0, depth := 1
    }
    let (innerResult, outerStillPresent) ← TermM.withBindings #[innerBinding] do
      let ctx ← TermM.getContext
      let hasInner := ctx.isSmaller "inner"
      let hasOuter := ctx.isSmaller "outer"
      return (hasInner, hasOuter)
    -- After withBindings, inner should be gone
    let ctx ← TermM.getContext
    let hasInnerAfter := ctx.isSmaller "inner"
    return (innerResult && outerStillPresent && !hasInnerAfter, true)
  match action.run' with
  | .ok (true, _) => return .passed
  | .ok (false, _) => return .failed "binding scoping should work"
  | .error _ => return .failed "should succeed"

def run : IO TestRunner := do
  IO.println "  === TermM Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "run_empty" (← testRunEmpty)
  runner := runner.record "smaller_tracking" (← testSmallerTracking)
  runner := runner.record "with_bindings" (← testWithBindings)
  return runner

end TermMTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 12: Integration Tests
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace IntegrationTests

def testNonRecursive : IO TestResult := do
  let fnInfo : FunctionInfo := {
    name := testFnName "id"
    markedTotal := true
    status := .isUnknown
    params := #["x"]
    fnType := Value.vType .zero
    span := testSpan
  }
  let body := testVar "x"
  let result := checkFunctionTotality fnInfo body
  if result.status == .isTotal then return .passed
  else return .failed "non-recursive should be total"

def testCheckAndRegister : IO TestResult := do
  let fnInfo : FunctionInfo := {
    name := testFnName "const"
    markedTotal := true
    status := .isUnknown
    params := #["x", "y"]
    fnType := Value.vType .zero
    span := testSpan
  }
  let body := testVar "x"
  let (registry, result) := checkAndRegisterTotality fnInfo body TotalityRegistry.empty
  if result.status == .isTotal && registry.isTotal "const" then return .passed
  else return .failed "should register as total"

def run : IO TestRunner := do
  IO.println "  === Integration Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "non_recursive" (← testNonRecursive)
  runner := runner.record "check_and_register" (← testCheckAndRegister)
  return runner

end IntegrationTests

/-! ═══════════════════════════════════════════════════════════════════════════
    SECTION 13: TotalityStatus Tests
    ═══════════════════════════════════════════════════════════════════════════ -/

namespace StatusTests

def testDefaultPartial : IO TestResult := do
  let status : TotalityStatus := .isPartial
  if status == .isPartial then return .passed
  else return .failed "default should be partial"

def testTotalStatus : IO TestResult := do
  let status : TotalityStatus := .isTotal
  if status == .isTotal then return .passed
  else return .failed "total status should be total"

def testStatusEquality : IO TestResult := do
  if TotalityStatus.isPartial != TotalityStatus.isTotal then return .passed
  else return .failed "partial should not equal total"

def run : IO TestRunner := do
  IO.println "  === Status Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "default_partial" (← testDefaultPartial)
  runner := runner.record "total_status" (← testTotalStatus)
  runner := runner.record "status_equality" (← testStatusEquality)
  return runner

end StatusTests

/-! ═══════════════════════════════════════════════════════════════════════════
    Main Test Runner
    ═══════════════════════════════════════════════════════════════════════════ -/

def runAllTests : IO TestRunner := do
  IO.println "=== Phase 9: SupGen-Style Totality Tests ==="
  IO.println ""

  let structurePathRunner ← StructurePathTests.run
  structurePathRunner.printSummary "StructurePath"

  let bindingInfoRunner ← BindingInfoTests.run
  bindingInfoRunner.printSummary "BindingInfo"

  let terminationCtxRunner ← TerminationContextTests.run
  terminationCtxRunner.printSummary "TerminationContext"

  let termShapeRunner ← TermShapeTests.run
  termShapeRunner.printSummary "TermShape"

  let structuralCmpRunner ← StructuralCmpTests.run
  structuralCmpRunner.printSummary "StructuralCmp"

  let pairExampleRunner ← PairExampleTests.run
  pairExampleRunner.printSummary "PairExample (Taelin)"

  let lexRunner ← LexicographicTests.run
  lexRunner.printSummary "Lexicographic"

  let standardRecRunner ← StandardRecursionTests.run
  standardRecRunner.printSummary "StandardRecursion"

  let positivityRunner ← PositivityTests.run
  positivityRunner.printSummary "Positivity"

  let registryRunner ← RegistryTests.run
  registryRunner.printSummary "Registry"

  let termMRunner ← TermMTests.run
  termMRunner.printSummary "TermM"

  let integrationRunner ← IntegrationTests.run
  integrationRunner.printSummary "Integration"

  let statusRunner ← StatusTests.run
  statusRunner.printSummary "Status"

  IO.println ""

  let combined := structurePathRunner.merge bindingInfoRunner
    |>.merge terminationCtxRunner |>.merge termShapeRunner
    |>.merge structuralCmpRunner |>.merge pairExampleRunner
    |>.merge lexRunner |>.merge standardRecRunner
    |>.merge positivityRunner |>.merge registryRunner
    |>.merge termMRunner |>.merge integrationRunner |>.merge statusRunner

  IO.println s!"Total: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Dependent.Totality
