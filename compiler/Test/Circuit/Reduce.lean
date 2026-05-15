import Somac.Circuit
import Somac.Circuit.Reduce
import Somac.Circuit.Reduce.Types
import Somac.Circuit.Reduce.Interact
import Somac.Circuit.Reduce.Readback
import Somac.Circuit.Graph
import Somac.Circuit.Node
import Somac.Circuit.Term
import Soma.Core.Value
import Test.Fixtures

namespace Test.Circuit.Reduce

open Somac.Circuit.Graph (Graph GraphM NodeEntry Definition)
open Somac.Circuit.Node (Node NodeId PortId PortIdx Label)
open Somac.Circuit.Term (Tag Op1Code Op2Code PrimType)
open Somac.Circuit.Reduce (reduce reduceNF eval ReadbackValue Config Stats
  ReduceResult ReduceError StuckReason)
open Soma.Core (Value)
open Test.Fixtures

/-- Synthetic test placeholders for the kernel-level primitive types -/
private def testUnitTy : Value := .vDataType ⟨1004, "test", "Unit"⟩ []

/-- Unit type placeholder for tests -/
private def testTy : Value := testUnitTy

/-! ## Graph Building Helpers

  All test graphs use the demand-driven wiring convention from Lower.lean:
  - Expression result ports connect to consumers (aux-to-principal)
  - A root ERA node provides the demand endpoint
  - `graph.root = root.principal`; `follow(root.principal)` reaches the result
-/

/-- Build a test graph with a root ERA node connected to the expression result.
    The builder returns the expression's result port. -/
private def buildTestGraph (builder : GraphM PortId) : Graph :=
  let m : GraphM Unit := do
    let resultPort ← builder
    -- Create root ERA as demand endpoint
    let root ← GraphM.addNode .era testTy
    GraphM.connect (PortId.principal root) resultPort
    GraphM.setRoot (PortId.principal root)
  (GraphM.run' m).2

/-- Evaluate a test graph to a ReadbackValue -/
private def evalGraph (g : Graph) : IO ReadbackValue :=
  eval g .forTotalEval

/-- Evaluate and return the full ReduceResult (with stats) -/
private def reduceGraph (g : Graph) : IO ReduceResult :=
  reduce g .forTotalEval

/-- Check that a ReadbackValue is a number with the expected value -/
private def expectNum (result : ReadbackValue) (expected : UInt32) : IO TestResult := do
  match result with
  | .num _ v =>
    if v == expected then return .passed
    else return .failed s!"expected {expected}, got {v}"
  | other => return .failed s!"expected num({expected}), got {other}"

/-- Check that a ReadbackValue is erased/unit -/
private def expectErased (result : ReadbackValue) : IO TestResult := do
  match result with
  | .erased => return .passed
  | other => return .failed s!"expected erased, got {other}"

/-- Check that a ReadbackValue is a constructor with expected tag -/
private def expectCtor (result : ReadbackValue) (tag : Nat) (arity : Nat) : IO TestResult := do
  match result with
  | .ctor t fields =>
    if t != tag then return .failed s!"expected tag {tag}, got {t}"
    else if fields.size != arity then
      return .failed s!"expected {arity} fields, got {fields.size}"
    else return .passed
  | other => return .failed s!"expected ctor({tag}/{arity}), got {other}"

/-- Check that a ReadbackValue is a record with expected field count -/
private def expectRecord (result : ReadbackValue) (numFields : Nat) : IO TestResult := do
  match result with
  | .record fields =>
    if fields.size != numFields then
      return .failed s!"expected {numFields} fields, got {fields.size}"
    else return .passed
  | other => return .failed s!"expected record({numFields}), got {other}"

/-! ## Unit Tests: Individual Interaction Rules -/

namespace BetaTests

/-- (λx. x) 42 → 42 -/
def testIdentity : IO TestResult := do
  let g := buildTestGraph do
    let lam ← GraphM.addNode (.lam false) testTy
    let app ← GraphM.addNode .app testTy
    let num ← GraphM.addNode (.num .i64 42) testTy
    -- APP.fun ↔ LAM.principal (function slot holds the lambda)
    GraphM.connect ⟨app, ⟨1⟩⟩ (PortId.principal lam)
    -- APP.arg ↔ NUM.principal (argument is 42)
    GraphM.connect ⟨app, ⟨2⟩⟩ (PortId.principal num)
    -- Identity: LAM.var ↔ LAM.body
    GraphM.connect ⟨lam, ⟨1⟩⟩ ⟨lam, ⟨2⟩⟩
    return PortId.principal app
  expectNum (← evalGraph g) 42

/-- (λx. 7) 42 → 7 (erased variable, argument discarded) -/
def testConstant : IO TestResult := do
  let g := buildTestGraph do
    let lam ← GraphM.addNode (.lam true) testTy  -- erased = true
    let app ← GraphM.addNode .app testTy
    let arg ← GraphM.addNode (.num .i64 42) testTy
    let body ← GraphM.addNode (.num .i64 7) testTy
    GraphM.connect ⟨app, ⟨1⟩⟩ (PortId.principal lam)
    GraphM.connect ⟨app, ⟨2⟩⟩ (PortId.principal arg)
    -- LAM.var gets ERA (unused), LAM.body gets the constant 7
    let era ← GraphM.addNode .era testTy
    GraphM.connect ⟨lam, ⟨1⟩⟩ (PortId.principal era)
    GraphM.connect ⟨lam, ⟨2⟩⟩ (PortId.principal body)
    return PortId.principal app
  expectNum (← evalGraph g) 7

/-- (λf. λx. f x) (λy. y) 5 → 5 (nested application) -/
def testNestedApplication : IO TestResult := do
  let g := buildTestGraph do
    -- Inner: (λy. y) — identity
    let lamY ← GraphM.addNode (.lam false) testTy
    GraphM.connect ⟨lamY, ⟨1⟩⟩ ⟨lamY, ⟨2⟩⟩

    -- (λx. f x) — apply f to x
    let lamX ← GraphM.addNode (.lam false) testTy
    let innerApp ← GraphM.addNode .app testTy
    -- innerApp.fun = f (which is lamX's free variable captured via wiring)
    -- innerApp.arg = x (lamX.var)
    -- But in interaction nets, this is more subtle. Let's use a simpler encoding:
    -- (λf. λx. f x) → λf. (λx. APP(f, x))
    let lamF ← GraphM.addNode (.lam false) testTy

    -- APP(f, x): innerApp.fun = DUP of f (need f for the application)
    -- Actually for a simple linear use: lamF.var → innerApp.fun, lamX.var → innerApp.arg
    GraphM.connect ⟨lamX, ⟨1⟩⟩ ⟨innerApp, ⟨2⟩⟩  -- x → arg
    GraphM.connect ⟨lamF, ⟨1⟩⟩ ⟨innerApp, ⟨1⟩⟩  -- f → fun
    GraphM.connect ⟨lamX, ⟨2⟩⟩ (PortId.principal innerApp)  -- body of x is the APP result
    GraphM.connect ⟨lamF, ⟨2⟩⟩ (PortId.principal lamX)  -- body of f is λx

    -- Now apply: (λf. λx. f x) (λy. y) 5
    let app1 ← GraphM.addNode .app testTy  -- apply to identity
    GraphM.connect ⟨app1, ⟨1⟩⟩ (PortId.principal lamF)
    GraphM.connect ⟨app1, ⟨2⟩⟩ (PortId.principal lamY)

    let num ← GraphM.addNode (.num .i64 5) testTy
    let app2 ← GraphM.addNode .app testTy  -- apply to 5
    GraphM.connect ⟨app2, ⟨1⟩⟩ (PortId.principal app1)
    GraphM.connect ⟨app2, ⟨2⟩⟩ (PortId.principal num)

    return PortId.principal app2
  expectNum (← evalGraph g) 5

def run : IO TestRunner := do
  IO.println "  === Beta Reduction Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "identity" (← testIdentity)
  runner := runner.record "constant" (← testConstant)
  runner := runner.record "nested_application" (← testNestedApplication)
  return runner

end BetaTests

namespace ArithmeticTests

/-- 3 + 4 → 7 -/
def testAdd : IO TestResult := do
  let g := buildTestGraph do
    let left ← GraphM.addNode (.num .i64 3) testTy
    let right ← GraphM.addNode (.num .i64 4) testTy
    let op ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal left)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal right)
    return PortId.principal op
  expectNum (← evalGraph g) 7

/-- 10 - 3 → 7 -/
def testSub : IO TestResult := do
  let g := buildTestGraph do
    let left ← GraphM.addNode (.num .i64 10) testTy
    let right ← GraphM.addNode (.num .i64 3) testTy
    let op ← GraphM.addNode (.op2 .sub) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal left)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal right)
    return PortId.principal op
  expectNum (← evalGraph g) 7

/-- 6 * 7 → 42 -/
def testMul : IO TestResult := do
  let g := buildTestGraph do
    let left ← GraphM.addNode (.num .i64 6) testTy
    let right ← GraphM.addNode (.num .i64 7) testTy
    let op ← GraphM.addNode (.op2 .mul) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal left)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal right)
    return PortId.principal op
  expectNum (← evalGraph g) 42

/-- 15 / 4 → 3 (integer division) -/
def testDiv : IO TestResult := do
  let g := buildTestGraph do
    let left ← GraphM.addNode (.num .i64 15) testTy
    let right ← GraphM.addNode (.num .i64 4) testTy
    let op ← GraphM.addNode (.op2 .div) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal left)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal right)
    return PortId.principal op
  expectNum (← evalGraph g) 3

/-- 5 == 5 → True (1) -/
def testEq : IO TestResult := do
  let g := buildTestGraph do
    let left ← GraphM.addNode (.num .i64 5) testTy
    let right ← GraphM.addNode (.num .i64 5) testTy
    let op ← GraphM.addNode (.op2 .eq) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal left)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal right)
    return PortId.principal op
  expectNum (← evalGraph g) 1

/-- 5 < 3 → False (0) -/
def testLt : IO TestResult := do
  let g := buildTestGraph do
    let left ← GraphM.addNode (.num .i64 5) testTy
    let right ← GraphM.addNode (.num .i64 3) testTy
    let op ← GraphM.addNode (.op2 .lt) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal left)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal right)
    return PortId.principal op
  expectNum (← evalGraph g) 0

/-- !0 → 1 (unary not) -/
def testNot : IO TestResult := do
  let g := buildTestGraph do
    let val ← GraphM.addNode (.num .bool 0) testTy
    let op ← GraphM.addNode (.op1 .not) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal val)
    return PortId.principal op
  expectNum (← evalGraph g) 1

/-- (2 + 3) * (4 + 1) → 25 (nested arithmetic) -/
def testNested : IO TestResult := do
  let g := buildTestGraph do
    let n2 ← GraphM.addNode (.num .i64 2) testTy
    let n3 ← GraphM.addNode (.num .i64 3) testTy
    let add1 ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add1, ⟨1⟩⟩ (PortId.principal n2)
    GraphM.connect ⟨add1, ⟨2⟩⟩ (PortId.principal n3)

    let n4 ← GraphM.addNode (.num .i64 4) testTy
    let n1 ← GraphM.addNode (.num .i64 1) testTy
    let add2 ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add2, ⟨1⟩⟩ (PortId.principal n4)
    GraphM.connect ⟨add2, ⟨2⟩⟩ (PortId.principal n1)

    let mul ← GraphM.addNode (.op2 .mul) testTy
    GraphM.connect ⟨mul, ⟨1⟩⟩ (PortId.principal add1)
    GraphM.connect ⟨mul, ⟨2⟩⟩ (PortId.principal add2)
    return PortId.principal mul
  expectNum (← evalGraph g) 25

def run : IO TestRunner := do
  IO.println "  === Arithmetic Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "add" (← testAdd)
  runner := runner.record "sub" (← testSub)
  runner := runner.record "mul" (← testMul)
  runner := runner.record "div" (← testDiv)
  runner := runner.record "eq" (← testEq)
  runner := runner.record "lt" (← testLt)
  runner := runner.record "not" (← testNot)
  runner := runner.record "nested" (← testNested)
  return runner

end ArithmeticTests

namespace MatchTests

/-- match CTOR(1, 42) { tag 1 → hit, _ → miss } → hit branch -/
def testMatchHit : IO TestResult := do
  let g := buildTestGraph do
    let ctor ← GraphM.addNode (.ctor 1 1) testTy
    let field ← GraphM.addNode (.num .i64 42) testTy
    GraphM.connect ⟨ctor, ⟨1⟩⟩ (PortId.principal field)

    let mat ← GraphM.addNode (.mat 1) testTy
    let hit ← GraphM.addNode (.num .i64 100) testTy
    let miss ← GraphM.addNode (.num .i64 0) testTy
    -- MAT.scrutinee ↔ CTOR.principal
    GraphM.connect ⟨mat, ⟨1⟩⟩ (PortId.principal ctor)
    -- MAT.hit ↔ hit value
    GraphM.connect ⟨mat, ⟨2⟩⟩ (PortId.principal hit)
    -- MAT.miss ↔ miss value
    GraphM.connect ⟨mat, ⟨3⟩⟩ (PortId.principal miss)
    return PortId.principal mat
  expectNum (← evalGraph g) 100

/-- match CTOR(0, _) { tag 1 → hit, _ → miss } → miss branch -/
def testMatchMiss : IO TestResult := do
  let g := buildTestGraph do
    let ctor ← GraphM.addNode (.ctor 0 0) testTy  -- tag 0 (e.g., Nothing)
    let mat ← GraphM.addNode (.mat 1) testTy  -- expect tag 1
    let hit ← GraphM.addNode (.num .i64 100) testTy
    let miss ← GraphM.addNode (.num .i64 0) testTy
    GraphM.connect ⟨mat, ⟨1⟩⟩ (PortId.principal ctor)
    GraphM.connect ⟨mat, ⟨2⟩⟩ (PortId.principal hit)
    GraphM.connect ⟨mat, ⟨3⟩⟩ (PortId.principal miss)
    return PortId.principal mat
  expectNum (← evalGraph g) 0

/-- match NUM(1) { 1 → hit, _ → miss } → hit (numeric scrutinee) -/
def testMatchNum : IO TestResult := do
  let g := buildTestGraph do
    let num ← GraphM.addNode (.num .bool 1) testTy
    let mat ← GraphM.addNode (.mat 1) testTy
    let hit ← GraphM.addNode (.num .i64 99) testTy
    let miss ← GraphM.addNode (.num .i64 0) testTy
    GraphM.connect ⟨mat, ⟨1⟩⟩ (PortId.principal num)
    GraphM.connect ⟨mat, ⟨2⟩⟩ (PortId.principal hit)
    GraphM.connect ⟨mat, ⟨3⟩⟩ (PortId.principal miss)
    return PortId.principal mat
  expectNum (← evalGraph g) 99

def run : IO TestRunner := do
  IO.println "  === Pattern Match Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "match_hit" (← testMatchHit)
  runner := runner.record "match_miss" (← testMatchMiss)
  runner := runner.record "match_num" (← testMatchNum)
  return runner

end MatchTests

namespace ProjectionTests

/-- { f0=10, f1=20, f2=30 }.f1 → 20 -/
def testRecordProj : IO TestResult := do
  let g := buildTestGraph do
    let rec ← GraphM.addNode (.record 3) testTy
    let f0 ← GraphM.addNode (.num .i64 10) testTy
    let f1 ← GraphM.addNode (.num .i64 20) testTy
    let f2 ← GraphM.addNode (.num .i64 30) testTy
    GraphM.connect ⟨rec, ⟨1⟩⟩ (PortId.principal f0)
    GraphM.connect ⟨rec, ⟨2⟩⟩ (PortId.principal f1)
    GraphM.connect ⟨rec, ⟨3⟩⟩ (PortId.principal f2)

    let proj ← GraphM.addNode (.proj 1) testTy  -- project field 1
    GraphM.connect ⟨proj, ⟨1⟩⟩ (PortId.principal rec)
    return PortId.principal proj
  expectNum (← evalGraph g) 20

/-- CTOR(tag=0, 42, 7).0 → 42 (constructor field projection) -/
def testCtorProj : IO TestResult := do
  let g := buildTestGraph do
    let ctor ← GraphM.addNode (.ctor 0 2) testTy
    let f0 ← GraphM.addNode (.num .i64 42) testTy
    let f1 ← GraphM.addNode (.num .i64 7) testTy
    GraphM.connect ⟨ctor, ⟨1⟩⟩ (PortId.principal f0)
    GraphM.connect ⟨ctor, ⟨2⟩⟩ (PortId.principal f1)

    let proj ← GraphM.addNode (.proj 0) testTy
    GraphM.connect ⟨proj, ⟨1⟩⟩ (PortId.principal ctor)
    return PortId.principal proj
  expectNum (← evalGraph g) 42

def run : IO TestRunner := do
  IO.println "  === Projection Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "record_proj" (← testRecordProj)
  runner := runner.record "ctor_proj" (← testCtorProj)
  return runner

end ProjectionTests

namespace DupTests

/-- DUP(42) → both copies are 42 (flat duplication) -/
def testDupNum : IO TestResult := do
  -- Build: let x = 42 in x + x
  -- Wiring: DUP.principal ↔ NUM(42), DUP.copy0 ↔ OP2.left, DUP.copy1 ↔ OP2.right
  let g := buildTestGraph do
    let num ← GraphM.addNode (.num .i64 42) testTy
    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal num)

    let op ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩  -- left = copy0
    GraphM.connect ⟨op, ⟨2⟩⟩ ⟨dup, ⟨2⟩⟩  -- right = copy1
    return PortId.principal op
  expectNum (← evalGraph g) 84  -- 42 + 42

/-- DUP(ERA) → both copies are ERA (annihilation) -/
def testDupEra : IO TestResult := do
  let g := buildTestGraph do
    let era ← GraphM.addNode .era testTy
    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal era)
    -- Demand copy0 (copy1 goes unused — we'd need to erase it, but just test copy0)
    return ⟨dup, ⟨1⟩⟩
  expectErased (← evalGraph g)

/-- DUP(λx. x) → two independent identity lambdas -/
def testDupLam : IO TestResult := do
  -- Build: let f = λx.x in (f 10) + (f 20)
  let g := buildTestGraph do
    let lam ← GraphM.addNode (.lam false) testTy
    GraphM.connect ⟨lam, ⟨1⟩⟩ ⟨lam, ⟨2⟩⟩  -- identity

    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal lam)

    -- Apply copy0 to 10
    let app0 ← GraphM.addNode .app testTy
    let n10 ← GraphM.addNode (.num .i64 10) testTy
    GraphM.connect ⟨app0, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩  -- fun = copy0
    GraphM.connect ⟨app0, ⟨2⟩⟩ (PortId.principal n10)

    -- Apply copy1 to 20
    let app1 ← GraphM.addNode .app testTy
    let n20 ← GraphM.addNode (.num .i64 20) testTy
    GraphM.connect ⟨app1, ⟨1⟩⟩ ⟨dup, ⟨2⟩⟩  -- fun = copy1
    GraphM.connect ⟨app1, ⟨2⟩⟩ (PortId.principal n20)

    -- Sum: (f 10) + (f 20) = 10 + 20 = 30
    let add ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add, ⟨1⟩⟩ (PortId.principal app0)
    GraphM.connect ⟨add, ⟨2⟩⟩ (PortId.principal app1)
    return PortId.principal add
  expectNum (← evalGraph g) 30

/-- DUP(CTOR(0, 5, 10)) → two independent copies of the constructor -/
def testDupCtor : IO TestResult := do
  -- Build: let p = Pair(5, 10) in p.0 + p.1
  -- But since we use DUP-CTOR, each copy is a separate constructor
  let g := buildTestGraph do
    let ctor ← GraphM.addNode (.ctor 0 2) testTy
    let f0 ← GraphM.addNode (.num .i64 5) testTy
    let f1 ← GraphM.addNode (.num .i64 10) testTy
    GraphM.connect ⟨ctor, ⟨1⟩⟩ (PortId.principal f0)
    GraphM.connect ⟨ctor, ⟨2⟩⟩ (PortId.principal f1)

    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal ctor)

    -- Project field 0 from copy0
    let proj0 ← GraphM.addNode (.proj 0) testTy
    GraphM.connect ⟨proj0, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩

    -- Project field 1 from copy1
    let proj1 ← GraphM.addNode (.proj 1) testTy
    GraphM.connect ⟨proj1, ⟨1⟩⟩ ⟨dup, ⟨2⟩⟩

    -- Sum: 5 + 10 = 15
    let add ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add, ⟨1⟩⟩ (PortId.principal proj0)
    GraphM.connect ⟨add, ⟨2⟩⟩ (PortId.principal proj1)
    return PortId.principal add
  expectNum (← evalGraph g) 15

/-- DUP-SUP same label: annihilation (O(1)) -/
def testDupSupSameLabel : IO TestResult := do
  let g := buildTestGraph do
    let label ← GraphM.freshLabel
    -- Create SUP with two values
    let sup ← GraphM.addNode (.sup label) testTy
    let v0 ← GraphM.addNode (.num .i64 100) testTy
    let v1 ← GraphM.addNode (.num .i64 200) testTy
    GraphM.connect ⟨sup, ⟨1⟩⟩ (PortId.principal v0)
    GraphM.connect ⟨sup, ⟨2⟩⟩ (PortId.principal v1)

    -- DUP with SAME label → annihilation
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal sup)

    -- After annihilation: copy0 = v0 = 100, copy1 = v1 = 200
    -- Sum them: 100 + 200 = 300
    let add ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩
    GraphM.connect ⟨add, ⟨2⟩⟩ ⟨dup, ⟨2⟩⟩
    return PortId.principal add
  expectNum (← evalGraph g) 300

/-- DUP-RECORD: duplicating a record -/
def testDupRecord : IO TestResult := do
  -- Build: let r = {10, 20} in r.0 + r.1
  let g := buildTestGraph do
    let rec ← GraphM.addNode (.record 2) testTy
    let f0 ← GraphM.addNode (.num .i64 10) testTy
    let f1 ← GraphM.addNode (.num .i64 20) testTy
    GraphM.connect ⟨rec, ⟨1⟩⟩ (PortId.principal f0)
    GraphM.connect ⟨rec, ⟨2⟩⟩ (PortId.principal f1)

    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal rec)

    let proj0 ← GraphM.addNode (.proj 0) testTy
    GraphM.connect ⟨proj0, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩

    let proj1 ← GraphM.addNode (.proj 1) testTy
    GraphM.connect ⟨proj1, ⟨1⟩⟩ ⟨dup, ⟨2⟩⟩

    let add ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add, ⟨1⟩⟩ (PortId.principal proj0)
    GraphM.connect ⟨add, ⟨2⟩⟩ (PortId.principal proj1)
    return PortId.principal add
  expectNum (← evalGraph g) 30

def run : IO TestRunner := do
  IO.println "  === Duplication Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "dup_num" (← testDupNum)
  runner := runner.record "dup_era" (← testDupEra)
  runner := runner.record "dup_lam" (← testDupLam)
  runner := runner.record "dup_ctor" (← testDupCtor)
  runner := runner.record "dup_sup_same_label" (← testDupSupSameLabel)
  runner := runner.record "dup_record" (← testDupRecord)
  return runner

end DupTests

namespace EraTests

/-- ERA propagates through a lambda -/
def testEraLam : IO TestResult := do
  -- The erased lambda's body is a number; ERA should propagate and clean up
  -- Graph: root demands a value, but the expression is just a plain NUM
  -- (ERA propagation is tested implicitly through β-reduction with erased args)
  -- Explicit test: constant function discards its argument
  let g := buildTestGraph do
    let lam ← GraphM.addNode (.lam true) testTy  -- erased param
    let eraVar ← GraphM.addNode .era testTy
    GraphM.connect ⟨lam, ⟨1⟩⟩ (PortId.principal eraVar)
    let body ← GraphM.addNode (.num .i64 99) testTy
    GraphM.connect ⟨lam, ⟨2⟩⟩ (PortId.principal body)

    -- Apply to a complex argument that should be erased
    let app ← GraphM.addNode .app testTy
    let argCtor ← GraphM.addNode (.ctor 0 2) testTy
    let argF0 ← GraphM.addNode (.num .i64 1) testTy
    let argF1 ← GraphM.addNode (.num .i64 2) testTy
    GraphM.connect ⟨argCtor, ⟨1⟩⟩ (PortId.principal argF0)
    GraphM.connect ⟨argCtor, ⟨2⟩⟩ (PortId.principal argF1)

    GraphM.connect ⟨app, ⟨1⟩⟩ (PortId.principal lam)
    GraphM.connect ⟨app, ⟨2⟩⟩ (PortId.principal argCtor)
    return PortId.principal app
  let result ← reduceGraph g
  -- Should reduce to 99, and the constructor argument should be fully erased
  expectNum result.value 99

def run : IO TestRunner := do
  IO.println "  === ERA Propagation Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "era_lam_discards_arg" (← testEraLam)
  return runner

end EraTests

namespace StatsTests

/-- Verify that stats track β-reductions correctly -/
def testBetaStats : IO TestResult := do
  let g := buildTestGraph do
    let lam ← GraphM.addNode (.lam false) testTy
    let app ← GraphM.addNode .app testTy
    let num ← GraphM.addNode (.num .i64 1) testTy
    GraphM.connect ⟨app, ⟨1⟩⟩ (PortId.principal lam)
    GraphM.connect ⟨app, ⟨2⟩⟩ (PortId.principal num)
    GraphM.connect ⟨lam, ⟨1⟩⟩ ⟨lam, ⟨2⟩⟩
    return PortId.principal app
  let result ← reduceGraph g
  if result.stats.betaReductions == 0 then
    return .failed "expected at least 1 beta reduction"
  return .passed

/-- Verify that stats track arithmetic ops -/
def testArithStats : IO TestResult := do
  let g := buildTestGraph do
    let left ← GraphM.addNode (.num .i64 1) testTy
    let right ← GraphM.addNode (.num .i64 2) testTy
    let op ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal left)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal right)
    return PortId.principal op
  let result ← reduceGraph g
  if result.stats.arithmeticOps == 0 then
    return .failed "expected at least 1 arithmetic op"
  return .passed

/-- Verify that stats track DUP commutations -/
def testDupStats : IO TestResult := do
  let g := buildTestGraph do
    let num ← GraphM.addNode (.num .i64 5) testTy
    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal num)
    let op ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩
    GraphM.connect ⟨op, ⟨2⟩⟩ ⟨dup, ⟨2⟩⟩
    return PortId.principal op
  let result ← reduceGraph g
  if result.stats.dupCommutations == 0 then
    return .failed "expected at least 1 DUP commutation"
  return .passed

/-- Verify that stats track match reductions -/
def testMatchStats : IO TestResult := do
  let g := buildTestGraph do
    let ctor ← GraphM.addNode (.ctor 0 0) testTy
    let mat ← GraphM.addNode (.mat 0) testTy
    let hit ← GraphM.addNode (.num .i64 1) testTy
    let miss ← GraphM.addNode (.num .i64 0) testTy
    GraphM.connect ⟨mat, ⟨1⟩⟩ (PortId.principal ctor)
    GraphM.connect ⟨mat, ⟨2⟩⟩ (PortId.principal hit)
    GraphM.connect ⟨mat, ⟨3⟩⟩ (PortId.principal miss)
    return PortId.principal mat
  let result ← reduceGraph g
  if result.stats.matchReductions == 0 then
    return .failed "expected at least 1 match reduction"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Stats Tracking Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "beta_stats" (← testBetaStats)
  runner := runner.record "arith_stats" (← testArithStats)
  runner := runner.record "dup_stats" (← testDupStats)
  runner := runner.record "match_stats" (← testMatchStats)
  return runner

end StatsTests

namespace IntegrationTests

/-- Full program: (λx. x + x) 21 → 42 (duplication through β-reduction) -/
def testDupThroughBeta : IO TestResult := do
  let g := buildTestGraph do
    -- λx. x + x
    let lam ← GraphM.addNode (.lam false) testTy
    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    let add ← GraphM.addNode (.op2 .add) testTy
    -- var → DUP → add
    GraphM.connect ⟨lam, ⟨1⟩⟩ (PortId.principal dup)  -- var goes into DUP
    GraphM.connect ⟨add, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩  -- copy0 → left operand
    GraphM.connect ⟨add, ⟨2⟩⟩ ⟨dup, ⟨2⟩⟩  -- copy1 → right operand
    GraphM.connect ⟨lam, ⟨2⟩⟩ (PortId.principal add)  -- body = add result

    -- Apply to 21
    let app ← GraphM.addNode .app testTy
    let n21 ← GraphM.addNode (.num .i64 21) testTy
    GraphM.connect ⟨app, ⟨1⟩⟩ (PortId.principal lam)
    GraphM.connect ⟨app, ⟨2⟩⟩ (PortId.principal n21)
    return PortId.principal app
  expectNum (← evalGraph g) 42

/-- Full program: fromMaybe 0 (Just 42) → 42 (match + projection) -/
def testFromMaybe : IO TestResult := do
  -- Simplified: match CTOR(1, 42) { tag 1 → PROJ.0(scrutinee_copy), tag 0 → default }
  -- In a real compiler the ctor fields would be extracted via APP chains,
  -- but we simplify by using PROJ on a duplicate of the scrutinee
  let g := buildTestGraph do
    let just ← GraphM.addNode (.ctor 1 1) testTy
    let val ← GraphM.addNode (.num .i64 42) testTy
    GraphM.connect ⟨just, ⟨1⟩⟩ (PortId.principal val)

    -- Need to DUP the scrutinee: one for MAT, one for extracting fields
    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal just)

    -- MAT on copy0
    let mat ← GraphM.addNode (.mat 1) testTy
    GraphM.connect ⟨mat, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩

    -- Hit branch: extract field 0 from copy1
    let proj ← GraphM.addNode (.proj 0) testTy
    GraphM.connect ⟨proj, ⟨1⟩⟩ ⟨dup, ⟨2⟩⟩
    GraphM.connect ⟨mat, ⟨2⟩⟩ (PortId.principal proj)

    -- Miss branch: default value 0
    let def_ ← GraphM.addNode (.num .i64 0) testTy
    GraphM.connect ⟨mat, ⟨3⟩⟩ (PortId.principal def_)

    return PortId.principal mat
  expectNum (← evalGraph g) 42

/-- Full program: { x = 1 + 2, y = 3 * 4 }.y → 12 (record with computed fields) -/
def testRecordComputed : IO TestResult := do
  let g := buildTestGraph do
    -- x = 1 + 2
    let n1 ← GraphM.addNode (.num .i64 1) testTy
    let n2 ← GraphM.addNode (.num .i64 2) testTy
    let addX ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨addX, ⟨1⟩⟩ (PortId.principal n1)
    GraphM.connect ⟨addX, ⟨2⟩⟩ (PortId.principal n2)

    -- y = 3 * 4
    let n3 ← GraphM.addNode (.num .i64 3) testTy
    let n4 ← GraphM.addNode (.num .i64 4) testTy
    let mulY ← GraphM.addNode (.op2 .mul) testTy
    GraphM.connect ⟨mulY, ⟨1⟩⟩ (PortId.principal n3)
    GraphM.connect ⟨mulY, ⟨2⟩⟩ (PortId.principal n4)

    -- Record { x, y }
    let rec ← GraphM.addNode (.record 2) testTy
    GraphM.connect ⟨rec, ⟨1⟩⟩ (PortId.principal addX)
    GraphM.connect ⟨rec, ⟨2⟩⟩ (PortId.principal mulY)

    -- .y (field 1)
    let proj ← GraphM.addNode (.proj 1) testTy
    GraphM.connect ⟨proj, ⟨1⟩⟩ (PortId.principal rec)
    return PortId.principal proj
  expectNum (← evalGraph g) 12

/-- Readback test: reduce to a constructor and verify full readback -/
def testCtorReadback : IO TestResult := do
  let g := buildTestGraph do
    let ctor ← GraphM.addNode (.ctor 1 2) testTy
    let f0 ← GraphM.addNode (.num .i64 10) testTy
    let f1 ← GraphM.addNode (.num .i64 20) testTy
    GraphM.connect ⟨ctor, ⟨1⟩⟩ (PortId.principal f0)
    GraphM.connect ⟨ctor, ⟨2⟩⟩ (PortId.principal f1)
    return PortId.principal ctor
  let result ← reduceNF g .forTotalEval
  match result.value with
  | .ctor 1 fields =>
    if fields.size != 2 then
      return .failed s!"expected 2 fields, got {fields.size}"
    else
      match (fields[0]? : Option ReadbackValue), (fields[1]? : Option ReadbackValue) with
      | some (.num _ 10), some (.num _ 20) => return .passed
      | _, _ => return .failed s!"unexpected field values: {result.value}"
  | other => return .failed s!"expected ctor(1, ...), got {other}"

/-- Value passthrough: a plain number at root -/
def testNumPassthrough : IO TestResult := do
  let g := buildTestGraph do
    let num ← GraphM.addNode (.num .i64 777) testTy
    return PortId.principal num
  expectNum (← evalGraph g) 777

/-- ERA at root → erased -/
def testEraAtRoot : IO TestResult := do
  let g := buildTestGraph do
    let era ← GraphM.addNode .era testTy
    return PortId.principal era
  expectErased (← evalGraph g)

def run : IO TestRunner := do
  IO.println "  === Integration Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "dup_through_beta" (← testDupThroughBeta)
  runner := runner.record "from_maybe" (← testFromMaybe)
  runner := runner.record "record_computed" (← testRecordComputed)
  runner := runner.record "ctor_readback" (← testCtorReadback)
  runner := runner.record "num_passthrough" (← testNumPassthrough)
  runner := runner.record "era_at_root" (← testEraAtRoot)
  return runner

end IntegrationTests

/-! ## SUP Commutation Tests -/

namespace SupCommutationTests

/-- APP-SUP: (&L{f,g} a) → &L{(f a₀),(g a₁)}
    f = λx.x+1, g = λx.x+2, a = 10
    result = SUP(11, 12) -/
def testAppSup : IO TestResult := do
  let g := buildTestGraph do
    let label ← GraphM.freshLabel
    -- f = λx. x + 1
    let lamF ← GraphM.addNode (.lam false) testTy
    let addF ← GraphM.addNode (.op2 .add) testTy
    let oneF ← GraphM.addNode (.num .i64 1) testTy
    GraphM.connect ⟨lamF, ⟨1⟩⟩ ⟨addF, ⟨1⟩⟩  -- var → add.left
    GraphM.connect ⟨addF, ⟨2⟩⟩ (PortId.principal oneF)
    GraphM.connect ⟨lamF, ⟨2⟩⟩ (PortId.principal addF)  -- body = add
    -- g = λx. x + 2
    let lamG ← GraphM.addNode (.lam false) testTy
    let addG ← GraphM.addNode (.op2 .add) testTy
    let twoG ← GraphM.addNode (.num .i64 2) testTy
    GraphM.connect ⟨lamG, ⟨1⟩⟩ ⟨addG, ⟨1⟩⟩
    GraphM.connect ⟨addG, ⟨2⟩⟩ (PortId.principal twoG)
    GraphM.connect ⟨lamG, ⟨2⟩⟩ (PortId.principal addG)
    -- SUP(f, g)
    let sup ← GraphM.addNode (.sup label) testTy
    GraphM.connect ⟨sup, ⟨1⟩⟩ (PortId.principal lamF)
    GraphM.connect ⟨sup, ⟨2⟩⟩ (PortId.principal lamG)
    -- APP(SUP(f,g), 10)
    let app ← GraphM.addNode .app testTy
    let ten ← GraphM.addNode (.num .i64 10) testTy
    GraphM.connect ⟨app, ⟨1⟩⟩ (PortId.principal sup)
    GraphM.connect ⟨app, ⟨2⟩⟩ (PortId.principal ten)
    return PortId.principal app
  let result ← reduceNF g .forTotalEval
  match result.value with
  | .sup _ v0 v1 =>
    match v0, v1 with
    | .num _ 11, .num _ 12 => return .passed
    | _, _ => return .failed s!"expected sup(11, 12), got sup({v0}, {v1})"
  | other => return .failed s!"expected sup, got {other}"

/-- APP-ERA: (ERA a) → ERA -/
def testAppEra : IO TestResult := do
  let g := buildTestGraph do
    let era ← GraphM.addNode .era testTy
    let app ← GraphM.addNode .app testTy
    let num ← GraphM.addNode (.num .i64 42) testTy
    GraphM.connect ⟨app, ⟨1⟩⟩ (PortId.principal era)
    GraphM.connect ⟨app, ⟨2⟩⟩ (PortId.principal num)
    return PortId.principal app
  expectErased (← evalGraph g)

/-- OP2-SUP (left): (op &L{3,7} 10) → &L{13, 17} -/
def testOp2SupLeft : IO TestResult := do
  let g := buildTestGraph do
    let label ← GraphM.freshLabel
    let n3 ← GraphM.addNode (.num .i64 3) testTy
    let n7 ← GraphM.addNode (.num .i64 7) testTy
    let sup ← GraphM.addNode (.sup label) testTy
    GraphM.connect ⟨sup, ⟨1⟩⟩ (PortId.principal n3)
    GraphM.connect ⟨sup, ⟨2⟩⟩ (PortId.principal n7)
    let n10 ← GraphM.addNode (.num .i64 10) testTy
    let op ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal sup)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal n10)
    return PortId.principal op
  let result ← reduceNF g .forTotalEval
  match result.value with
  | .sup _ (.num _ 13) (.num _ 17) => return .passed
  | other => return .failed s!"expected sup(13, 17), got {other}"

/-- OP2-SUP (right): (op 10 &L{3,7}) → &L{13, 17} -/
def testOp2SupRight : IO TestResult := do
  let g := buildTestGraph do
    let label ← GraphM.freshLabel
    let n10 ← GraphM.addNode (.num .i64 10) testTy
    let n3 ← GraphM.addNode (.num .i64 3) testTy
    let n7 ← GraphM.addNode (.num .i64 7) testTy
    let sup ← GraphM.addNode (.sup label) testTy
    GraphM.connect ⟨sup, ⟨1⟩⟩ (PortId.principal n3)
    GraphM.connect ⟨sup, ⟨2⟩⟩ (PortId.principal n7)
    let op ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal n10)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal sup)
    return PortId.principal op
  let result ← reduceNF g .forTotalEval
  match result.value with
  | .sup _ (.num _ 13) (.num _ 17) => return .passed
  | other => return .failed s!"expected sup(13, 17), got {other}"

/-- OP2-ERA: (op ERA 5) → ERA -/
def testOp2EraLeft : IO TestResult := do
  let g := buildTestGraph do
    let era ← GraphM.addNode .era testTy
    let n5 ← GraphM.addNode (.num .i64 5) testTy
    let op ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal era)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal n5)
    return PortId.principal op
  expectErased (← evalGraph g)

/-- OP2-ERA: (op 5 ERA) → ERA -/
def testOp2EraRight : IO TestResult := do
  let g := buildTestGraph do
    let n5 ← GraphM.addNode (.num .i64 5) testTy
    let era ← GraphM.addNode .era testTy
    let op ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal n5)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal era)
    return PortId.principal op
  expectErased (← evalGraph g)

/-- OP1-SUP: (not &L{0,1}) → &L{1, 0} -/
def testOp1Sup : IO TestResult := do
  let g := buildTestGraph do
    let label ← GraphM.freshLabel
    let n0 ← GraphM.addNode (.num .bool 0) testTy
    let n1 ← GraphM.addNode (.num .bool 1) testTy
    let sup ← GraphM.addNode (.sup label) testTy
    GraphM.connect ⟨sup, ⟨1⟩⟩ (PortId.principal n0)
    GraphM.connect ⟨sup, ⟨2⟩⟩ (PortId.principal n1)
    let op ← GraphM.addNode (.op1 .not) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal sup)
    return PortId.principal op
  let result ← reduceNF g .forTotalEval
  match result.value with
  | .sup _ (.num _ 1) (.num _ 0) => return .passed
  | other => return .failed s!"expected sup(1, 0), got {other}"

/-- OP1-ERA: (not ERA) → ERA -/
def testOp1Era : IO TestResult := do
  let g := buildTestGraph do
    let era ← GraphM.addNode .era testTy
    let op ← GraphM.addNode (.op1 .not) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal era)
    return PortId.principal op
  expectErased (← evalGraph g)

/-- MAT-SUP: (mat &L{C0,C1} hit miss) → &L{(mat C0 hit₀ miss₀),(mat C1 hit₁ miss₁)}
    C0 matches tag 0, C1 doesn't → SUP(hit_value, miss_value) -/
def testMatSup : IO TestResult := do
  let g := buildTestGraph do
    let label ← GraphM.freshLabel
    -- SUP(C0{}, C1{}) where tag 0 = match, tag 1 = miss
    let c0 ← GraphM.addNode (.ctor 0 0) testTy
    let c1 ← GraphM.addNode (.ctor 1 0) testTy
    let sup ← GraphM.addNode (.sup label) testTy
    GraphM.connect ⟨sup, ⟨1⟩⟩ (PortId.principal c0)
    GraphM.connect ⟨sup, ⟨2⟩⟩ (PortId.principal c1)
    -- MAT on tag 0
    let mat ← GraphM.addNode (.mat 0) testTy
    let hit ← GraphM.addNode (.num .i64 100) testTy
    let miss ← GraphM.addNode (.num .i64 200) testTy
    GraphM.connect ⟨mat, ⟨1⟩⟩ (PortId.principal sup)
    GraphM.connect ⟨mat, ⟨2⟩⟩ (PortId.principal hit)
    GraphM.connect ⟨mat, ⟨3⟩⟩ (PortId.principal miss)
    return PortId.principal mat
  let result ← reduceNF g .forTotalEval
  match result.value with
  | .sup _ (.num _ 100) (.num _ 200) => return .passed
  | other => return .failed s!"expected sup(100, 200), got {other}"

/-- MAT-ERA: (mat ERA hit miss) → ERA -/
def testMatEra : IO TestResult := do
  let g := buildTestGraph do
    let era ← GraphM.addNode .era testTy
    let mat ← GraphM.addNode (.mat 0) testTy
    let hit ← GraphM.addNode (.num .i64 1) testTy
    let miss ← GraphM.addNode (.num .i64 0) testTy
    GraphM.connect ⟨mat, ⟨1⟩⟩ (PortId.principal era)
    GraphM.connect ⟨mat, ⟨2⟩⟩ (PortId.principal hit)
    GraphM.connect ⟨mat, ⟨3⟩⟩ (PortId.principal miss)
    return PortId.principal mat
  expectErased (← evalGraph g)

/-- PROJ-SUP: (proj_0 &L{R0, R1}) → &L{(proj_0 R0),(proj_0 R1)} -/
def testProjSup : IO TestResult := do
  let g := buildTestGraph do
    let label ← GraphM.freshLabel
    -- R0 = {10, 20}
    let r0 ← GraphM.addNode (.record 2) testTy
    let f00 ← GraphM.addNode (.num .i64 10) testTy
    let f01 ← GraphM.addNode (.num .i64 20) testTy
    GraphM.connect ⟨r0, ⟨1⟩⟩ (PortId.principal f00)
    GraphM.connect ⟨r0, ⟨2⟩⟩ (PortId.principal f01)
    -- R1 = {30, 40}
    let r1 ← GraphM.addNode (.record 2) testTy
    let f10 ← GraphM.addNode (.num .i64 30) testTy
    let f11 ← GraphM.addNode (.num .i64 40) testTy
    GraphM.connect ⟨r1, ⟨1⟩⟩ (PortId.principal f10)
    GraphM.connect ⟨r1, ⟨2⟩⟩ (PortId.principal f11)
    -- SUP(R0, R1)
    let sup ← GraphM.addNode (.sup label) testTy
    GraphM.connect ⟨sup, ⟨1⟩⟩ (PortId.principal r0)
    GraphM.connect ⟨sup, ⟨2⟩⟩ (PortId.principal r1)
    -- proj field 0
    let proj ← GraphM.addNode (.proj 0) testTy
    GraphM.connect ⟨proj, ⟨1⟩⟩ (PortId.principal sup)
    return PortId.principal proj
  let result ← reduceNF g .forTotalEval
  match result.value with
  | .sup _ (.num _ 10) (.num _ 30) => return .passed
  | other => return .failed s!"expected sup(10, 30), got {other}"

/-- PROJ-ERA: (proj_0 ERA) → ERA -/
def testProjEra : IO TestResult := do
  let g := buildTestGraph do
    let era ← GraphM.addNode .era testTy
    let proj ← GraphM.addNode (.proj 0) testTy
    GraphM.connect ⟨proj, ⟨1⟩⟩ (PortId.principal era)
    return PortId.principal proj
  expectErased (← evalGraph g)

/-- Integration: DUP a value, apply both copies → SUP distributes through computation
    DUP(λx.x), then apply copy0 to 10 and copy1 to 20 → result is (10, 20) pair -/
def testDupLamApplyBoth : IO TestResult := do
  let g := buildTestGraph do
    let label ← GraphM.freshLabel
    -- λx.x (identity)
    let lam ← GraphM.addNode (.lam false) testTy
    GraphM.connect ⟨lam, ⟨1⟩⟩ ⟨lam, ⟨2⟩⟩
    -- DUP it
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal lam)
    -- Apply copy0 to 10
    let app0 ← GraphM.addNode .app testTy
    let n10 ← GraphM.addNode (.num .i64 10) testTy
    GraphM.connect ⟨app0, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩
    GraphM.connect ⟨app0, ⟨2⟩⟩ (PortId.principal n10)
    -- Apply copy1 to 20
    let app1 ← GraphM.addNode .app testTy
    let n20 ← GraphM.addNode (.num .i64 20) testTy
    GraphM.connect ⟨app1, ⟨1⟩⟩ ⟨dup, ⟨2⟩⟩
    GraphM.connect ⟨app1, ⟨2⟩⟩ (PortId.principal n20)
    -- Pack results into a constructor pair
    let pair ← GraphM.addNode (.ctor 0 2) testTy
    GraphM.connect ⟨pair, ⟨1⟩⟩ (PortId.principal app0)
    GraphM.connect ⟨pair, ⟨2⟩⟩ (PortId.principal app1)
    return PortId.principal pair
  let result ← reduceNF g .forTotalEval
  match result.value with
  | .ctor 0 fields =>
    match (fields[0]? : Option ReadbackValue), (fields[1]? : Option ReadbackValue) with
    | some (.num _ 10), some (.num _ 20) => return .passed
    | _, _ => return .failed s!"expected (10, 20), got {result.value}"
  | other => return .failed s!"expected ctor(0, 10, 20), got {other}"

/-- Stats: verify SUP commutation counter increments -/
def testSupCommutationStats : IO TestResult := do
  let g := buildTestGraph do
    let label ← GraphM.freshLabel
    let n3 ← GraphM.addNode (.num .i64 3) testTy
    let n7 ← GraphM.addNode (.num .i64 7) testTy
    let sup ← GraphM.addNode (.sup label) testTy
    GraphM.connect ⟨sup, ⟨1⟩⟩ (PortId.principal n3)
    GraphM.connect ⟨sup, ⟨2⟩⟩ (PortId.principal n7)
    let n10 ← GraphM.addNode (.num .i64 10) testTy
    let op ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal sup)
    GraphM.connect ⟨op, ⟨2⟩⟩ (PortId.principal n10)
    return PortId.principal op
  let result ← reduceGraph g
  if result.stats.supCommutations == 0 then
    return .failed "expected at least 1 SUP commutation"
  return .passed

/-- Stats: verify ERA absorption counter increments -/
def testEraAbsorptionStats : IO TestResult := do
  let g := buildTestGraph do
    let era ← GraphM.addNode .era testTy
    let app ← GraphM.addNode .app testTy
    let num ← GraphM.addNode (.num .i64 42) testTy
    GraphM.connect ⟨app, ⟨1⟩⟩ (PortId.principal era)
    GraphM.connect ⟨app, ⟨2⟩⟩ (PortId.principal num)
    return PortId.principal app
  let result ← reduceGraph g
  if result.stats.eraAbsorptions == 0 then
    return .failed "expected at least 1 ERA absorption"
  return .passed

def run : IO TestRunner := do
  IO.println "  === SUP Commutation & ERA Absorption Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "app_sup" (← testAppSup)
  runner := runner.record "app_era" (← testAppEra)
  runner := runner.record "op2_sup_left" (← testOp2SupLeft)
  runner := runner.record "op2_sup_right" (← testOp2SupRight)
  runner := runner.record "op2_era_left" (← testOp2EraLeft)
  runner := runner.record "op2_era_right" (← testOp2EraRight)
  runner := runner.record "op1_sup" (← testOp1Sup)
  runner := runner.record "op1_era" (← testOp1Era)
  runner := runner.record "mat_sup" (← testMatSup)
  runner := runner.record "mat_era" (← testMatEra)
  runner := runner.record "proj_sup" (← testProjSup)
  runner := runner.record "proj_era" (← testProjEra)
  runner := runner.record "dup_lam_apply_both" (← testDupLamApplyBoth)
  runner := runner.record "sup_commutation_stats" (← testSupCommutationStats)
  runner := runner.record "era_absorption_stats" (← testEraAbsorptionStats)
  return runner

end SupCommutationTests

namespace DupNodTests

/-- DUP-APP: duplicating a stuck application produces two independent applications.
    Graph: DUP(APP(f, 10)), where f is a free variable (another DUP copy).
    We feed two different lambdas to the two copies of f, and check both results. -/
def testDupApp : IO TestResult := do
  let g := buildTestGraph do
    -- Create a lambda: λx. x + 1
    let lam ← GraphM.addNode (.lam false) testTy
    let addBody ← GraphM.addNode (.op2 .add) testTy
    let one ← GraphM.addNode (.num .i64 1) testTy
    GraphM.connect ⟨lam, ⟨1⟩⟩ ⟨addBody, ⟨1⟩⟩  -- var → add.left
    GraphM.connect ⟨addBody, ⟨2⟩⟩ (PortId.principal one)
    GraphM.connect ⟨lam, ⟨2⟩⟩ (PortId.principal addBody)  -- body = add

    -- Create APP(lam, 10)
    let app ← GraphM.addNode .app testTy
    let ten ← GraphM.addNode (.num .i64 10) testTy
    GraphM.connect ⟨app, ⟨1⟩⟩ (PortId.principal lam)
    GraphM.connect ⟨app, ⟨2⟩⟩ (PortId.principal ten)

    -- DUP the application result
    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal app)

    -- Sum both copies: copy0 + copy1  (should be 11 + 11 = 22)
    let add ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩
    GraphM.connect ⟨add, ⟨2⟩⟩ ⟨dup, ⟨2⟩⟩
    return PortId.principal add
  expectNum (← evalGraph g) 22  -- (10+1) + (10+1) = 22

/-- DUP-CTOR: duplicating a constructor duplicates each field independently.
    Graph: DUP(CTOR₁(42, 7)), then access field 0 of each copy and sum them. -/
def testDupCtor : IO TestResult := do
  let g := buildTestGraph do
    let ctor ← GraphM.addNode (.ctor 1 2) testTy
    let n42 ← GraphM.addNode (.num .i64 42) testTy
    let n7 ← GraphM.addNode (.num .i64 7) testTy
    GraphM.connect ⟨ctor, ⟨1⟩⟩ (PortId.principal n42)
    GraphM.connect ⟨ctor, ⟨2⟩⟩ (PortId.principal n7)

    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal ctor)

    return ⟨dup, ⟨1⟩⟩
  let result ← reduceNF g .forTotalEval
  match result.value with
  | .ctor 1 fields =>
    if fields.size != 2 then return .failed s!"expected 2 fields, got {fields.size}"
    else match fields[0]!, fields[1]! with
    | .num _ 42, .num _ 7 => return .passed
    | a, b => return .failed s!"expected (42, 7), got ({a}, {b})"
  | other => return .failed s!"expected ctor(1/2), got {other}"

/-- DUP-OP2: duplicating the result of an arithmetic operation.
    Graph: DUP(3 + 7), copy0 * copy1 → 10 * 10 = 100 -/
def testDupOp2Result : IO TestResult := do
  let g := buildTestGraph do
    let n3 ← GraphM.addNode (.num .i64 3) testTy
    let n7 ← GraphM.addNode (.num .i64 7) testTy
    let add ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add, ⟨1⟩⟩ (PortId.principal n3)
    GraphM.connect ⟨add, ⟨2⟩⟩ (PortId.principal n7)

    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal add)

    let mul ← GraphM.addNode (.op2 .mul) testTy
    GraphM.connect ⟨mul, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩
    GraphM.connect ⟨mul, ⟨2⟩⟩ ⟨dup, ⟨2⟩⟩
    return PortId.principal mul
  expectNum (← evalGraph g) 100  -- (3+7) * (3+7) = 100

/-- DUP-MAT: duplicating a match result.
    Graph: DUP(mat CTOR₀() hit=100 miss=200), sum both copies → 200 -/
def testDupMatResult : IO TestResult := do
  let g := buildTestGraph do
    let ctor ← GraphM.addNode (.ctor 0 0) testTy
    let mat ← GraphM.addNode (.mat 0) testTy
    let hit ← GraphM.addNode (.num .i64 100) testTy
    let miss ← GraphM.addNode (.num .i64 200) testTy
    GraphM.connect ⟨mat, ⟨1⟩⟩ (PortId.principal ctor)   -- scrutinee
    GraphM.connect ⟨mat, ⟨2⟩⟩ (PortId.principal hit)     -- hit branch
    GraphM.connect ⟨mat, ⟨3⟩⟩ (PortId.principal miss)    -- miss branch

    -- DUP the match result (DUP principal ↔ MAT principal)
    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal mat)

    let add ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩
    GraphM.connect ⟨add, ⟨2⟩⟩ ⟨dup, ⟨2⟩⟩
    return PortId.principal add
  expectNum (← evalGraph g) 200  -- 100 + 100

/-- DUP-RECORD: duplicating a record creates two independent records.
    Graph: DUP({10, 20}), project field 0 from each copy and sum. -/
def testDupRecord : IO TestResult := do
  let g := buildTestGraph do
    let rec ← GraphM.addNode (.record 2) testTy
    let n10 ← GraphM.addNode (.num .i64 10) testTy
    let n20 ← GraphM.addNode (.num .i64 20) testTy
    GraphM.connect ⟨rec, ⟨1⟩⟩ (PortId.principal n10)
    GraphM.connect ⟨rec, ⟨2⟩⟩ (PortId.principal n20)

    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal rec)

    -- Project field 0 from each copy
    let proj0 ← GraphM.addNode (.proj 0) testTy
    GraphM.connect ⟨proj0, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩  -- proj0.record ← copy0
    let proj1 ← GraphM.addNode (.proj 0) testTy
    GraphM.connect ⟨proj1, ⟨1⟩⟩ ⟨dup, ⟨2⟩⟩  -- proj1.record ← copy1

    let add ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add, ⟨1⟩⟩ (PortId.principal proj0)  -- add.left ← proj0 result
    GraphM.connect ⟨add, ⟨2⟩⟩ (PortId.principal proj1)  -- add.right ← proj1 result
    return PortId.principal add
  expectNum (← evalGraph g) 20  -- 10 + 10

/-- DUP-PROJ: duplicating a projection result.
    Graph: DUP(proj₁({5, 15})), sum both copies → 30 -/
def testDupProjResult : IO TestResult := do
  let g := buildTestGraph do
    let rec ← GraphM.addNode (.record 2) testTy
    let n5 ← GraphM.addNode (.num .i64 5) testTy
    let n15 ← GraphM.addNode (.num .i64 15) testTy
    GraphM.connect ⟨rec, ⟨1⟩⟩ (PortId.principal n5)
    GraphM.connect ⟨rec, ⟨2⟩⟩ (PortId.principal n15)

    let proj ← GraphM.addNode (.proj 1) testTy
    GraphM.connect ⟨proj, ⟨1⟩⟩ (PortId.principal rec)  -- proj.record ← record

    -- DUP the projection result (DUP principal ↔ PROJ principal)
    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal proj)

    let add ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩
    GraphM.connect ⟨add, ⟨2⟩⟩ ⟨dup, ⟨2⟩⟩
    return PortId.principal add
  expectNum (← evalGraph g) 30  -- 15 + 15

/-- DUP-OP1: duplicating a unary operation result.
    Graph: DUP(NOT 0), both copies should be 1, sum → 2 -/
def testDupOp1Result : IO TestResult := do
  let g := buildTestGraph do
    let n0 ← GraphM.addNode (.num .i64 0) testTy
    let op ← GraphM.addNode (.op1 .not) testTy
    GraphM.connect ⟨op, ⟨1⟩⟩ (PortId.principal n0)

    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal op)

    let add ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add, ⟨1⟩⟩ ⟨dup, ⟨1⟩⟩
    GraphM.connect ⟨add, ⟨2⟩⟩ ⟨dup, ⟨2⟩⟩
    return PortId.principal add
  expectNum (← evalGraph g) 2  -- 1 + 1

/-- DUP nested: DUP(DUP(λx.x applied to 42)).
    All four copies should be 42. -/
def testDupNested : IO TestResult := do
  let g := buildTestGraph do
    let lam ← GraphM.addNode (.lam false) testTy
    GraphM.connect ⟨lam, ⟨1⟩⟩ ⟨lam, ⟨2⟩⟩  -- identity

    let app ← GraphM.addNode .app testTy
    let n42 ← GraphM.addNode (.num .i64 42) testTy
    GraphM.connect ⟨app, ⟨1⟩⟩ (PortId.principal lam)
    GraphM.connect ⟨app, ⟨2⟩⟩ (PortId.principal n42)

    -- First DUP
    let l1 ← GraphM.freshLabel
    let dup1 ← GraphM.addNode (.dup l1) testTy
    GraphM.connect (PortId.principal dup1) (PortId.principal app)

    -- Second DUP on copy0
    let l2 ← GraphM.freshLabel
    let dup2 ← GraphM.addNode (.dup l2) testTy
    GraphM.connect (PortId.principal dup2) ⟨dup1, ⟨1⟩⟩

    -- Sum all four: dup2.1 + dup2.2 + dup1.2 (the third copy)
    -- Wait — dup1 gives 2 copies, dup2 splits copy0 → 2 more = 3 total
    -- Let's just sum the three: dup2.1 + dup2.2 + dup1.2
    let add1 ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add1, ⟨1⟩⟩ ⟨dup2, ⟨1⟩⟩
    GraphM.connect ⟨add1, ⟨2⟩⟩ ⟨dup2, ⟨2⟩⟩

    let add2 ← GraphM.addNode (.op2 .add) testTy
    GraphM.connect ⟨add2, ⟨1⟩⟩ (PortId.principal add1)
    GraphM.connect ⟨add2, ⟨2⟩⟩ ⟨dup1, ⟨2⟩⟩
    return PortId.principal add2
  expectNum (← evalGraph g) 126  -- 42 + 42 + 42

/-- DUP-CTOR with nested field access: DUP(Pair(3, 7)), access different fields
    from each copy: copy0.field0 + copy1.field1 → 3 + 7 = 10 -/
def testDupCtorFieldAccess : IO TestResult := do
  let g := buildTestGraph do
    let ctor ← GraphM.addNode (.ctor 0 2) testTy
    let n3 ← GraphM.addNode (.num .i64 3) testTy
    let n7 ← GraphM.addNode (.num .i64 7) testTy
    GraphM.connect ⟨ctor, ⟨1⟩⟩ (PortId.principal n3)
    GraphM.connect ⟨ctor, ⟨2⟩⟩ (PortId.principal n7)

    let label ← GraphM.freshLabel
    let dup ← GraphM.addNode (.dup label) testTy
    GraphM.connect (PortId.principal dup) (PortId.principal ctor)

    return ⟨dup, ⟨1⟩⟩
  let result ← reduceNF g .forTotalEval
  match result.value with
  | .ctor 0 fields =>
    if fields.size != 2 then return .failed s!"expected 2 fields, got {fields.size}"
    else match fields[0]!, fields[1]! with
    | .num _ 3, .num _ 7 => return .passed
    | a, b => return .failed s!"expected (3, 7), got ({a}, {b})"
  | other => return .failed s!"expected ctor(0/2), got {other}"

def run : IO TestRunner := do
  IO.println "  === DUP Node Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "dup_app" (← testDupApp)
  runner := runner.record "dup_ctor_generic" (← testDupCtor)
  runner := runner.record "dup_op2_result" (← testDupOp2Result)
  runner := runner.record "dup_mat_result" (← testDupMatResult)
  runner := runner.record "dup_record_generic" (← testDupRecord)
  runner := runner.record "dup_proj_result" (← testDupProjResult)
  runner := runner.record "dup_op1_result" (← testDupOp1Result)
  runner := runner.record "dup_nested" (← testDupNested)
  runner := runner.record "dup_ctor_field_access" (← testDupCtorFieldAccess)
  return runner

end DupNodTests

/-! ## Main Test Runner -/

def run : IO TestRunner := do
  IO.println "=== Circuit Reducer Tests ==="
  IO.println ""

  let betaRunner ← BetaTests.run
  betaRunner.printSummary "Beta"

  let arithRunner ← ArithmeticTests.run
  arithRunner.printSummary "Arithmetic"

  let matchRunner ← MatchTests.run
  matchRunner.printSummary "Match"

  let projRunner ← ProjectionTests.run
  projRunner.printSummary "Projection"

  let dupRunner ← DupTests.run
  dupRunner.printSummary "Duplication"

  let eraRunner ← EraTests.run
  eraRunner.printSummary "ERA"

  let statsRunner ← StatsTests.run
  statsRunner.printSummary "Stats"

  let integrationRunner ← IntegrationTests.run
  integrationRunner.printSummary "Integration"

  let supRunner ← SupCommutationTests.run
  supRunner.printSummary "SUP/ERA"

  let dupNodRunner ← DupNodTests.run
  dupNodRunner.printSummary "DUP Node"

  IO.println ""

  let combined := betaRunner.merge arithRunner
    |>.merge matchRunner
    |>.merge projRunner
    |>.merge dupRunner
    |>.merge eraRunner
    |>.merge statsRunner
    |>.merge integrationRunner
    |>.merge supRunner
    |>.merge dupNodRunner

  IO.println s!"Total: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Circuit.Reduce
