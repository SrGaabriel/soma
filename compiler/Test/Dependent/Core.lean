/-
  Test.Dependent.Core - Unit tests for the Core module (Phase 1 of dependent types)

  Tests cover:
  - Quantity semiring operations and laws
  - Level operations and simplification
  - Value construction and basic operations
  - Env and MetaState operations
-/

import Soma.Core
import Test.Fixtures

namespace Test.Dependent.Core

open Soma.Core
open Test.Fixtures

/-- Synthetic test placeholders for the kernel-level primitive types -/
def testIntTy : Soma.Core.Value := .vDataType ⟨1001, "test", "Int32"⟩ []
def testBoolTy : Soma.Core.Value := .vDataType ⟨1002, "test", "Bool"⟩ []
def testStringTy : Soma.Core.Value := .vDataType ⟨1003, "test", "String"⟩ []

/-! ## Quantity Tests -/

namespace QuantityTests

/-- Test: 0 + q = q (zero is additive identity) -/
def testAddZeroLeft : IO TestResult := do
  if Quantity.zero + Quantity.one != Quantity.one then
    return .failed "0 + 1 should be 1"
  if Quantity.zero + Quantity.omega != Quantity.omega then
    return .failed "0 + ω should be ω"
  if Quantity.zero + Quantity.zero != Quantity.zero then
    return .failed "0 + 0 should be 0"
  return .passed

/-- Test: q + 0 = q -/
def testAddZeroRight : IO TestResult := do
  if Quantity.one + Quantity.zero != Quantity.one then
    return .failed "1 + 0 should be 1"
  if Quantity.omega + Quantity.zero != Quantity.omega then
    return .failed "ω + 0 should be ω"
  return .passed

/-- Test: 1 + 1 = ω -/
def testAddOneOne : IO TestResult := do
  if Quantity.one + Quantity.one != Quantity.omega then
    return .failed "1 + 1 should be ω"
  return .passed

/-- Test: ω + q = ω -/
def testAddOmega : IO TestResult := do
  if Quantity.omega + Quantity.zero != Quantity.omega then
    return .failed "ω + 0 should be ω"
  if Quantity.omega + Quantity.one != Quantity.omega then
    return .failed "ω + 1 should be ω"
  if Quantity.omega + Quantity.omega != Quantity.omega then
    return .failed "ω + ω should be ω"
  return .passed

/-- Test: 0 * q = 0 (zero annihilates) -/
def testMulZero : IO TestResult := do
  if Quantity.zero * Quantity.one != Quantity.zero then
    return .failed "0 * 1 should be 0"
  if Quantity.zero * Quantity.omega != Quantity.zero then
    return .failed "0 * ω should be 0"
  if Quantity.one * Quantity.zero != Quantity.zero then
    return .failed "1 * 0 should be 0"
  return .passed

/-- Test: 1 * q = q (one is multiplicative identity) -/
def testMulOne : IO TestResult := do
  if Quantity.one * Quantity.one != Quantity.one then
    return .failed "1 * 1 should be 1"
  if Quantity.one * Quantity.omega != Quantity.omega then
    return .failed "1 * ω should be ω"
  if Quantity.omega * Quantity.one != Quantity.omega then
    return .failed "ω * 1 should be ω"
  return .passed

/-- Test: ω * ω = ω -/
def testMulOmegaOmega : IO TestResult := do
  if Quantity.omega * Quantity.omega != Quantity.omega then
    return .failed "ω * ω should be ω"
  return .passed

/-- Test: ordering 0 ≤ 1 ≤ ω -/
def testOrdering : IO TestResult := do
  if !(Quantity.zero ≤ Quantity.zero) then
    return .failed "0 ≤ 0 should hold"
  if !(Quantity.zero ≤ Quantity.one) then
    return .failed "0 ≤ 1 should hold"
  if !(Quantity.zero ≤ Quantity.omega) then
    return .failed "0 ≤ ω should hold"
  if !(Quantity.one ≤ Quantity.one) then
    return .failed "1 ≤ 1 should hold"
  if !(Quantity.one ≤ Quantity.omega) then
    return .failed "1 ≤ ω should hold"
  if !(Quantity.omega ≤ Quantity.omega) then
    return .failed "ω ≤ ω should hold"
  -- These should NOT hold
  if Quantity.one ≤ Quantity.zero then
    return .failed "1 ≤ 0 should NOT hold"
  if Quantity.omega ≤ Quantity.one then
    return .failed "ω ≤ 1 should NOT hold"
  return .passed

/-- Test: commutativity of addition -/
def testAddCommutative : IO TestResult := do
  let quantities := [Quantity.zero, Quantity.one, Quantity.omega]
  for q1 in quantities do
    for q2 in quantities do
      if q1 + q2 != q2 + q1 then
        return .failed s!"add not commutative: {q1} + {q2} != {q2} + {q1}"
  return .passed

/-- Test: commutativity of multiplication -/
def testMulCommutative : IO TestResult := do
  let quantities := [Quantity.zero, Quantity.one, Quantity.omega]
  for q1 in quantities do
    for q2 in quantities do
      if q1 * q2 != q2 * q1 then
        return .failed s!"mul not commutative: {q1} * {q2} != {q2} * {q1}"
  return .passed

/-- Test: utility predicates -/
def testPredicates : IO TestResult := do
  if !Quantity.zero.isErased then
    return .failed "0 should be erased"
  if Quantity.one.isErased then
    return .failed "1 should not be erased"
  if !Quantity.one.isLinear then
    return .failed "1 should be linear"
  if Quantity.omega.isLinear then
    return .failed "ω should not be linear"
  if !Quantity.omega.isUnrestricted then
    return .failed "ω should be unrestricted"
  if Quantity.zero.allowsUsage then
    return .failed "0 should not allow usage"
  if !Quantity.one.allowsUsage then
    return .failed "1 should allow usage"
  if Quantity.one.allowsDuplication then
    return .failed "1 should not allow duplication"
  if !Quantity.omega.allowsDuplication then
    return .failed "ω should allow duplication"
  return .passed

/-- Test: join (least upper bound) -/
def testJoin : IO TestResult := do
  if Quantity.join .zero .zero != .zero then
    return .failed "join(0, 0) should be 0"
  if Quantity.join .zero .one != .one then
    return .failed "join(0, 1) should be 1"
  if Quantity.join .one .omega != .omega then
    return .failed "join(1, ω) should be ω"
  if Quantity.join .omega .zero != .omega then
    return .failed "join(ω, 0) should be ω"
  return .passed

/-- Test: meet (greatest lower bound) -/
def testMeet : IO TestResult := do
  if Quantity.meet .zero .zero != .zero then
    return .failed "meet(0, 0) should be 0"
  if Quantity.meet .zero .one != .zero then
    return .failed "meet(0, 1) should be 0"
  if Quantity.meet .one .omega != .one then
    return .failed "meet(1, ω) should be 1"
  if Quantity.meet .omega .omega != .omega then
    return .failed "meet(ω, ω) should be ω"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Quantity Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "add_zero_left" (← testAddZeroLeft)
  runner := runner.record "add_zero_right" (← testAddZeroRight)
  runner := runner.record "add_one_one" (← testAddOneOne)
  runner := runner.record "add_omega" (← testAddOmega)
  runner := runner.record "mul_zero" (← testMulZero)
  runner := runner.record "mul_one" (← testMulOne)
  runner := runner.record "mul_omega_omega" (← testMulOmegaOmega)
  runner := runner.record "ordering" (← testOrdering)
  runner := runner.record "add_commutative" (← testAddCommutative)
  runner := runner.record "mul_commutative" (← testMulCommutative)
  runner := runner.record "predicates" (← testPredicates)
  runner := runner.record "join" (← testJoin)
  runner := runner.record "meet" (← testMeet)

  return runner

end QuantityTests

/-! ## Level Tests -/

namespace LevelTests

/-- Test: literal levels -/
def testLiteral : IO TestResult := do
  if Level.zero != Level.lit 0 then
    return .failed "Level.zero should be lit 0"
  if Level.one != Level.lit 1 then
    return .failed "Level.one should be lit 1"
  if Level.two != Level.lit 2 then
    return .failed "Level.two should be lit 2"
  return .passed

/-- Test: level addition -/
def testAddition : IO TestResult := do
  let l := Level.zero + 3
  match l with
  | .succ (.succ (.succ (.lit 0))) => return .passed
  | _ => return .failed s!"0 + 3 should be succ(succ(succ(0))), got {l}"

/-- Test: mkSucc simplifies literals -/
def testMkSuccSimplifies : IO TestResult := do
  let l := Level.mkSucc (Level.lit 2)
  if l != Level.lit 3 then
    return .failed s!"mkSucc(2) should be 3, got {l}"
  return .passed

/-- Test: mkMax simplifies literals -/
def testMkMaxSimplifies : IO TestResult := do
  let l := Level.mkMax (Level.lit 2) (Level.lit 5)
  if l != Level.lit 5 then
    return .failed s!"mkMax(2, 5) should be 5, got {l}"
  let l2 := Level.mkMax (Level.lit 0) (Level.var ⟨0, "u"⟩)
  if l2 != Level.var ⟨0, "u"⟩ then
    return .failed s!"mkMax(0, u) should be u, got {l2}"
  return .passed

/-- Test: simplify -/
def testSimplify : IO TestResult := do
  -- succ(succ(lit 1)) should simplify to lit 3
  let l := Level.succ (Level.succ (Level.lit 1))
  let simplified := l.simplify
  if simplified != Level.lit 3 then
    return .failed s!"simplify(succ(succ(1))) should be 3, got {simplified}"
  -- max(lit 2, lit 5) should simplify to lit 5
  let l2 := Level.max (Level.lit 2) (Level.lit 5)
  let simplified2 := l2.simplify
  if simplified2 != Level.lit 5 then
    return .failed s!"simplify(max(2, 5)) should be 5, got {simplified2}"
  return .passed

/-- Test: substitution -/
def testSubst : IO TestResult := do
  let u := LevelVarId.mk 0 "u"
  let v := LevelVarId.mk 1 "v"
  let l := Level.max (Level.var u) (Level.lit 1)
  let substituted := l.subst u (Level.lit 3)
  let simplified := substituted.simplify
  if simplified != Level.lit 3 then
    return .failed s!"subst max(u, 1)[u := 3] should be 3, got {simplified}"
  -- Substituting a different variable should have no effect
  let l2 := Level.var u
  let substituted2 := l2.subst v (Level.lit 5)
  if substituted2 != Level.var u then
    return .failed "subst u[v := 5] should still be u"
  return .passed

/-- Test: hasVars -/
def testHasVars : IO TestResult := do
  if Level.lit 5 |>.hasVars then
    return .failed "lit 5 should not have vars"
  if !(Level.var ⟨0, "u"⟩ |>.hasVars) then
    return .failed "var u should have vars"
  if !(Level.max (Level.lit 1) (Level.var ⟨0, "u"⟩) |>.hasVars) then
    return .failed "max(1, u) should have vars"
  if Level.succ (Level.lit 2) |>.hasVars then
    return .failed "succ(2) should not have vars"
  return .passed

/-- Test: freeVars -/
def testFreeVars : IO TestResult := do
  let u := LevelVarId.mk 0 "u"
  let v := LevelVarId.mk 1 "v"
  let l := Level.max (Level.var u) (Level.succ (Level.var v))
  let vars := l.freeVars
  if vars.length != 2 then
    return .failed s!"max(u, succ(v)) should have 2 free vars, got {vars.length}"
  if !vars.any (· == u) then
    return .failed "u should be in free vars"
  if !vars.any (· == v) then
    return .failed "v should be in free vars"
  return .passed

/-- Test: isLit and toLit? -/
def testLitQuery : IO TestResult := do
  if !(Level.lit 5).isLit then
    return .failed "lit 5 should be a literal"
  if (Level.var ⟨0, "u"⟩).isLit then
    return .failed "var u should not be a literal"
  match (Level.lit 5).toLit? with
  | some 5 => pure ()
  | _ => return .failed "toLit?(5) should be some 5"
  match (Level.var ⟨0, "u"⟩).toLit? with
  | none => pure ()
  | some _ => return .failed "toLit?(u) should be none"
  return .passed

/-- Test: toString -/
def testToString : IO TestResult := do
  let l := Level.lit 3
  if toString l != "3" then
    return .failed s!"toString(3) should be '3', got '{toString l}'"
  let u := Level.var ⟨0, "u"⟩
  if toString u != "u" then
    return .failed s!"toString(var u) should be 'u', got '{toString u}'"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Level Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "literal" (← testLiteral)
  runner := runner.record "addition" (← testAddition)
  runner := runner.record "mkSucc_simplifies" (← testMkSuccSimplifies)
  runner := runner.record "mkMax_simplifies" (← testMkMaxSimplifies)
  runner := runner.record "simplify" (← testSimplify)
  runner := runner.record "subst" (← testSubst)
  runner := runner.record "hasVars" (← testHasVars)
  runner := runner.record "freeVars" (← testFreeVars)
  runner := runner.record "lit_query" (← testLitQuery)
  runner := runner.record "toString" (← testToString)

  return runner

end LevelTests

/-! ## Value Tests -/

namespace ValueTests

/-- Test: Value type constructors -/
def testTypeConstructors : IO TestResult := do
  let t0 := Value.type0
  let t1 := Value.type1
  match t0, t1 with
  | .vType (.lit 0), .vType (.lit 1) => return .passed
  | _, _ => return .failed "type0 and type1 should be vType with correct levels"

/-- Test: Primitive types -/
def testPrimitives : IO TestResult := do
  let intTy := testIntTy
  let boolTy := testBoolTy
  let strTy := testStringTy
  match intTy, boolTy, strTy with
  | .vDataType ⟨1001, "test", "Int32"⟩ [],
    .vDataType ⟨1002, "test", "Bool"⟩ [],
    .vDataType ⟨1003, "test", "String"⟩ [] => return .passed
  | _, _, _ => return .failed "primitive types should be constructed correctly"

/-- Test: Literals -/
def testLiterals : IO TestResult := do
  let intLit := Value.vIntLit 42
  let strLit := Value.vStringLit "hello"
  match intLit, strLit with
  | .vIntLit 42, .vStringLit "hello" => return .passed
  | _, _ => return .failed "literals should be constructed correctly"

/-- Test: Row types -/
def testRowTypes : IO TestResult := do
  let empty := Value.vRowEmpty
  let extended := Value.vRowExtend (Value.vLabelLit "x") testIntTy empty
  match empty, extended with
  | .vRowEmpty,
    .vRowExtend (.vLabelLit "x") (.vDataType ⟨1001, "test", "Int32"⟩ []) .vRowEmpty =>
    return .passed
  | _, _ => return .failed "row types should be constructed correctly"

/-- Test: Record value -/
def testRecordVal : IO TestResult := do
  let fields := [("x", Value.vIntLit 1), ("y", Value.vIntLit 2)]
  let record := Value.vRecordVal fields
  match record with
  | .vRecordVal fs =>
    if fs.length != 2 then
      return .failed s!"record should have 2 fields, got {fs.length}"
    return .passed
  | _ => return .failed "should be a record value"

/-- Test: Equality type construction -/
def testEqualityType : IO TestResult := do
  let ty := testIntTy
  let lhs := Value.vIntLit 1
  let rhs := Value.vIntLit 1
  let eqId : Soma.Unique := ⟨2000, "test", "Eq"⟩
  let eq := Value.vDataType eqId [ty, lhs, rhs]
  match eq with
  | .vDataType ⟨2000, "test", "Eq"⟩
      [.vDataType ⟨1001, "test", "Int32"⟩ [], .vIntLit 1, .vIntLit 1] =>
    return .passed
  | _ => return .failed "equality type should be constructed correctly"

/-- Test: Refl construction -/
def testRefl : IO TestResult := do
  let ty := testIntTy
  let x := Value.vIntLit 42
  let eqId : Soma.Unique := ⟨2000, "test", "Eq"⟩
  let reflName : QualifiedName := ⟨⟨2001, "test", "refl"⟩⟩
  let resultTy : Value := .vDataType eqId [ty, x, x]
  let refl : Value := .vConstructor reflName 0 [ty, x] resultTy
  match refl with
  | .vConstructor name 0
      [.vDataType ⟨1001, "test", "Int32"⟩ [], .vIntLit 42] _ =>
    if name == reflName then return .passed
    else return .failed s!"unexpected refl name: {name.display}"
  | _ => return .failed "refl should be constructed correctly"

def run : IO TestRunner := do
  IO.println "  === Value Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "type_constructors" (← testTypeConstructors)
  runner := runner.record "primitives" (← testPrimitives)
  runner := runner.record "literals" (← testLiterals)
  runner := runner.record "row_types" (← testRowTypes)
  runner := runner.record "record_val" (← testRecordVal)
  runner := runner.record "equality_type" (← testEqualityType)
  runner := runner.record "refl" (← testRefl)

  return runner

end ValueTests

/-! ## Env Tests -/

namespace EnvTests

/-- Test: empty environment -/
def testEmpty : IO TestResult := do
  let env := Env.empty
  if env.size != 0 then
    return .failed s!"empty env should have size 0, got {env.size}"
  if env.level != ⟨0⟩ then
    return .failed "empty env should have level 0"
  return .passed

/-- Test: extend environment -/
def testExtend : IO TestResult := do
  let env := Env.empty
  let env := env.extend "x" (Value.vIntLit 1)
  if env.size != 1 then
    return .failed s!"env should have size 1 after extend, got {env.size}"
  let env := env.extend "y" (Value.vIntLit 2)
  if env.size != 2 then
    return .failed s!"env should have size 2 after second extend, got {env.size}"
  return .passed

/-- Test: lookup by level -/
def testLookup : IO TestResult := do
  let env := Env.empty
    |>.extend "x" (Value.vIntLit 1)
    |>.extend "y" (Value.vIntLit 2)
    |>.extend "z" (Value.vIntLit 3)
  -- Level 0 is x (first inserted), level 2 is z (last inserted)
  match env.lookup ⟨0⟩ with
  | some (.vIntLit 1) => pure ()
  | some v => return .failed s!"lookup level 0 should be 1, got {v}"
  | none => return .failed "lookup level 0 should be some, got none"
  match env.lookup ⟨1⟩ with
  | some (.vIntLit 2) => pure ()
  | some v => return .failed s!"lookup level 1 should be 2, got {v}"
  | none => return .failed "lookup level 1 should be some, got none"
  match env.lookup ⟨2⟩ with
  | some (.vIntLit 3) => pure ()
  | some v => return .failed s!"lookup level 2 should be 3, got {v}"
  | none => return .failed "lookup level 2 should be some, got none"
  match env.lookup ⟨3⟩ with
  | none => pure ()
  | some _ => return .failed "lookup level 3 should be none"
  return .passed

/-- Test: lookup by name -/
def testLookupByName : IO TestResult := do
  let env := Env.empty
    |>.extend "x" (Value.vIntLit 1)
    |>.extend "y" (Value.vIntLit 2)
  match env.lookupByName "x" with
  | some (.vIntLit 1) => pure ()
  | some v => return .failed s!"lookup 'x' should be 1, got {v}"
  | none => return .failed "lookup 'x' should be some, got none"
  match env.lookupByName "y" with
  | some (.vIntLit 2) => pure ()
  | some v => return .failed s!"lookup 'y' should be 2, got {v}"
  | none => return .failed "lookup 'y' should be some, got none"
  match env.lookupByName "z" with
  | none => pure ()
  | some _ => return .failed "lookup 'z' should be none"
  return .passed

/-- Test: level tracking -/
def testLevel : IO TestResult := do
  let env := Env.empty
  if env.level != ⟨0⟩ then
    return .failed "initial level should be 0"
  let env := env.extend "x" (Value.vIntLit 1)
  if env.level != ⟨1⟩ then
    return .failed "level after 1 extend should be 1"
  let env := env.extend "y" (Value.vIntLit 2)
  if env.level != ⟨2⟩ then
    return .failed "level after 2 extends should be 2"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Env Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "empty" (← testEmpty)
  runner := runner.record "extend" (← testExtend)
  runner := runner.record "lookup" (← testLookup)
  runner := runner.record "lookup_by_name" (← testLookupByName)
  runner := runner.record "level" (← testLevel)

  return runner

end EnvTests

/-! ## MetaState Tests -/

namespace MetaStateTests

/-- Test: empty state -/
def testEmpty : IO TestResult := do
  let state := MetaState.empty
  if state.nextId != 0 then
    return .failed "empty state should have nextId 0"
  return .passed

/-- Test: fresh metavariable -/
def testFresh : IO TestResult := do
  let state := MetaState.empty
  let ty := Value.vType Level.zero
  let (m1, state) := state.fresh ty []
  if m1.id != 0 then
    return .failed s!"first meta should have id 0, got {m1.id}"
  let (m2, state) := state.fresh ty []
  if m2.id != 1 then
    return .failed s!"second meta should have id 1, got {m2.id}"
  if state.nextId != 2 then
    return .failed s!"nextId should be 2 after 2 fresh, got {state.nextId}"
  return .passed

/-- Test: lookup metavariable -/
def testLookup : IO TestResult := do
  let state := MetaState.empty
  let ty := Value.vType Level.zero
  let (m, state) := state.fresh ty []
  match state.lookup m with
  | some info =>
    if info.solution.isSome then
      return .failed "fresh meta should not be solved"
    return .passed
  | none => return .failed "should find the meta we just created"

/-- Test: solve metavariable -/
def testSolve : IO TestResult := do
  let state := MetaState.empty
  let ty := Value.vType Level.zero
  let (m, state) := state.fresh ty []
  if state.isSolved m then
    return .failed "fresh meta should not be solved"
  let solution := testIntTy
  let state := state.solve m solution
  if !state.isSolved m then
    return .failed "meta should be solved after solve"
  match state.lookup m with
  | some info =>
    match info.solution with
    | some (.vDataType ⟨1001, "test", "Int32"⟩ []) => return .passed
    | some v => return .failed s!"solution should be Int, got {v}"
    | none => return .failed "solution should be some, got none"
  | none => return .failed "should find the meta"

/-- Test: isSolved -/
def testIsSolved : IO TestResult := do
  let state := MetaState.empty
  let ty := Value.vType Level.zero
  let (m1, state) := state.fresh ty []
  let (m2, state) := state.fresh ty []
  let state := state.solve m1 testIntTy
  if !state.isSolved m1 then
    return .failed "m1 should be solved"
  if state.isSolved m2 then
    return .failed "m2 should not be solved"
  -- Unknown meta should return false
  if state.isSolved ⟨999⟩ then
    return .failed "unknown meta should not be solved"
  return .passed

def run : IO TestRunner := do
  IO.println "  === MetaState Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "empty" (← testEmpty)
  runner := runner.record "fresh" (← testFresh)
  runner := runner.record "lookup" (← testLookup)
  runner := runner.record "solve" (← testSolve)
  runner := runner.record "isSolved" (← testIsSolved)

  return runner

end MetaStateTests

/-! ## DeBruijnLvl Tests -/

namespace DeBruijnLvlTests

/-- Test: zero and succ -/
def testZeroSucc : IO TestResult := do
  let l0 := DeBruijnLvl.zero
  if l0.lvl != 0 then
    return .failed "zero should be 0"
  let l1 := l0.succ
  if l1.lvl != 1 then
    return .failed "succ(0) should be 1"
  let l2 := l1.succ
  if l2.lvl != 2 then
    return .failed "succ(1) should be 2"
  return .passed

/-- Test: toNat -/
def testToNat : IO TestResult := do
  let l := DeBruijnLvl.zero.succ.succ.succ
  if l.toNat != 3 then
    return .failed s!"toNat should be 3, got {l.toNat}"
  return .passed

/-- Test: equality -/
def testEquality : IO TestResult := do
  let l1 : DeBruijnLvl := ⟨5⟩
  let l2 : DeBruijnLvl := ⟨5⟩
  let l3 : DeBruijnLvl := ⟨6⟩
  if l1 != l2 then
    return .failed "equal levels should be equal"
  if l1 == l3 then
    return .failed "different levels should not be equal"
  return .passed

def run : IO TestRunner := do
  IO.println "  === DeBruijnLvl Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "zero_succ" (← testZeroSucc)
  runner := runner.record "toNat" (← testToNat)
  runner := runner.record "equality" (← testEquality)

  return runner

end DeBruijnLvlTests

/-! ## Neutral Tests -/

namespace NeutralTests

/-- Test: variable neutral -/
def testVarNeutral : IO TestResult := do
  let n := Neutral.var "x" ⟨0⟩
  match n with
  | .nVar v =>
    if v.name != "x" then
      return .failed "variable name should be 'x'"
    if v.level != ⟨0⟩ then
      return .failed "variable level should be 0"
    return .passed
  | _ => return .failed "should be a variable neutral"

/-- Test: meta neutral -/
def testMetaNeutral : IO TestResult := do
  let n := Neutral.mkMeta 42
  match n with
  | .nMeta m =>
    if m.id != 42 then
      return .failed s!"meta id should be 42, got {m.id}"
    return .passed
  | _ => return .failed "should be a meta neutral"

/-- Test: application neutral -/
def testAppNeutral : IO TestResult := do
  let fn := Neutral.var "f" ⟨0⟩
  let arg := Value.vIntLit 1
  let app := Neutral.nApp fn arg
  match app with
  | .nApp (.nVar _) (.vIntLit 1) => return .passed
  | _ => return .failed "should be an application neutral"

def run : IO TestRunner := do
  IO.println "  === Neutral Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "var_neutral" (← testVarNeutral)
  runner := runner.record "meta_neutral" (← testMetaNeutral)
  runner := runner.record "app_neutral" (← testAppNeutral)

  return runner

end NeutralTests

/-! ## Main Test Runner -/

def run : IO TestRunner := do
  IO.println "=== Dependent Types Core Tests ==="
  IO.println ""

  let quantityRunner ← QuantityTests.run
  quantityRunner.printSummary "Quantity"

  let levelRunner ← LevelTests.run
  levelRunner.printSummary "Level"

  let valueRunner ← ValueTests.run
  valueRunner.printSummary "Value"

  let envRunner ← EnvTests.run
  envRunner.printSummary "Env"

  let metaRunner ← MetaStateTests.run
  metaRunner.printSummary "MetaState"

  let dblRunner ← DeBruijnLvlTests.run
  dblRunner.printSummary "DeBruijnLvl"

  let neutralRunner ← NeutralTests.run
  neutralRunner.printSummary "Neutral"

  IO.println ""

  let combined := quantityRunner.merge levelRunner |>.merge valueRunner
    |>.merge envRunner |>.merge metaRunner |>.merge dblRunner |>.merge neutralRunner

  IO.println s!"Total: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Dependent.Core
