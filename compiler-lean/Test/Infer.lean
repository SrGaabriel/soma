import Soma.Infer
import Test.Fixtures

namespace Test.Infer

open Soma.Infer
open Soma.Typing
open Soma.Syntax (Span SourceLoc)
open Test.Fixtures

abbrev TyConstraint := Soma.Typing.Constraint

/-- Create a dummy span for testing -/
def testSpan : Span :=
  let loc : SourceLoc := { file := ⟨0⟩, byteOffset := 0, line := 1, column := 1 }
  { start := loc, stop := loc }

/-- Create a type variable with a given name and ID -/
def mkTyVar (name : String) (id : Nat) : TyVarId :=
  ⟨name, id, .star⟩

/-- Create a MonoTy variable -/
def tyVar (name : String) (id : Nat) : MonoTy :=
  .var (mkTyVar name id)

/-- Create a test BindingId -/
def mkBindingId (id : Nat) : Soma.Metal.BindingId :=
  { id := id, module := "test", original := s!"x{id}", kind := .patternVar }

namespace SubstitutionTests

def testEmpty : IO TestResult := do
  let σ := Subst.empty
  if !σ.isEmpty then
    return .failed "empty substitution should be empty"
  if σ.size != 0 then
    return .failed "empty substitution should have size 0"
  return .passed

def testSingleton : IO TestResult := do
  let σ := Subst.singleton 0 Ty.int
  if σ.isEmpty then
    return .failed "singleton substitution should not be empty"
  if σ.size != 1 then
    return .failed s!"singleton should have size 1, got {σ.size}"
  match σ.lookup 0 with
  | some ty =>
    if ty != Ty.int then
      return .failed "lookup should return Int"
    return .passed
  | none =>
    return .failed "lookup should find the variable"

def testApplyVar : IO TestResult := do
  let v := mkTyVar "a" 0
  let σ := Subst.fromVar v Ty.int
  let result := σ.apply (.var v)
  if result != Ty.int then
    return .failed s!"applying subst to var should give Int, got {result}"
  return .passed

def testApplyUnboundVar : IO TestResult := do
  let v := mkTyVar "a" 0
  let unbound := mkTyVar "b" 1
  let σ := Subst.fromVar v Ty.int
  let result := σ.apply (.var unbound)
  if result != .var unbound then
    return .failed "unbound var should remain unchanged"
  return .passed

def testApplyArrow : IO TestResult := do
  let v := mkTyVar "a" 0
  let σ := Subst.fromVar v Ty.int
  let ty : MonoTy := .arrow (.var v) (.var v)
  let result := σ.apply ty
  let expected : MonoTy := .arrow Ty.int Ty.int
  if result != expected then
    return .failed s!"expected {expected}, got {result}"
  return .passed

def testApplyTuple : IO TestResult := do
  let a := mkTyVar "a" 0
  let b := mkTyVar "b" 1
  let σ := (Subst.fromVar a Ty.int).insert b.id Ty.string
  let ty : MonoTy := .tuple2 (.var a) (.var b)
  let result := σ.apply ty
  let expected : MonoTy := .tuple2 Ty.int Ty.string
  if result != expected then
    return .failed s!"expected {expected}, got {result}"
  return .passed

def testCompose : IO TestResult := do
  let a := mkTyVar "a" 0
  let b := mkTyVar "b" 1
  let σ1 := Subst.fromVar a (.var b)
  let σ2 := Subst.fromVar b Ty.int
  let composed := σ2.compose σ1

  let resultA := composed.apply (.var a)
  if resultA != Ty.int then
    return .failed s!"composed subst on 'a' should give Int, got {resultA}"

  let resultB := composed.apply (.var b)
  if resultB != Ty.int then
    return .failed s!"composed subst on 'b' should give Int, got {resultB}"

  return .passed

def testFromArrays : IO TestResult := do
  let vars := #[mkTyVar "a" 0, mkTyVar "b" 1, mkTyVar "c" 2]
  let types := #[Ty.int, Ty.string, Ty.bool]
  let σ := Subst.fromArrays vars types

  if σ.apply (tyVar "a" 0) != Ty.int then
    return .failed "a should map to Int"
  if σ.apply (tyVar "b" 1) != Ty.string then
    return .failed "b should map to String"
  if σ.apply (tyVar "c" 2) != Ty.bool then
    return .failed "c should map to Bool"

  return .passed

def run : IO TestRunner := do
  IO.println "  === Substitution Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "empty" (← testEmpty)
  runner := runner.record "singleton" (← testSingleton)
  runner := runner.record "apply_var" (← testApplyVar)
  runner := runner.record "apply_unbound_var" (← testApplyUnboundVar)
  runner := runner.record "apply_arrow" (← testApplyArrow)
  runner := runner.record "apply_tuple" (← testApplyTuple)
  runner := runner.record "compose" (← testCompose)
  runner := runner.record "from_arrays" (← testFromArrays)

  return runner

end SubstitutionTests

namespace UnifyTests

def unifyCtx : UnifyContext :=
  { purpose := .general, expectedSpan := testSpan, actualSpan := testSpan }

def testUnifyIdentical : IO TestResult := do
  match Unify.unifyMono Ty.int Ty.int unifyCtx with
  | .ok σ =>
    if !σ.isEmpty then
      return .failed "unifying identical types should give empty subst"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

def testUnifyVarLeft : IO TestResult := do
  let v := mkTyVar "a" 0
  match Unify.unifyMono (.var v) Ty.int unifyCtx with
  | .ok σ =>
    if σ.apply (.var v) != Ty.int then
      return .failed "var should be bound to Int"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

def testUnifyVarRight : IO TestResult := do
  let v := mkTyVar "a" 0
  match Unify.unifyMono Ty.int (.var v) unifyCtx with
  | .ok σ =>
    if σ.apply (.var v) != Ty.int then
      return .failed "var should be bound to Int"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

def testUnifyTwoVars : IO TestResult := do
  let a := mkTyVar "a" 0
  let b := mkTyVar "b" 1
  match Unify.unifyMono (.var a) (.var b) unifyCtx with
  | .ok σ =>
    -- One should be bound to the other
    let resultA := σ.apply (.var a)
    let resultB := σ.apply (.var b)
    if resultA != resultB then
      return .failed "both vars should unify to same type"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

def testUnifyArrow : IO TestResult := do
  let a := mkTyVar "a" 0
  let b := mkTyVar "b" 1
  let ty1 : MonoTy := .arrow (.var a) Ty.int
  let ty2 : MonoTy := .arrow Ty.string (.var b)
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    if σ.apply (.var a) != Ty.string then
      return .failed "a should be String"
    if σ.apply (.var b) != Ty.int then
      return .failed "b should be Int"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

def testUnifyTuple2 : IO TestResult := do
  let a := mkTyVar "a" 0
  let ty1 : MonoTy := .tuple2 (.var a) Ty.int
  let ty2 : MonoTy := .tuple2 Ty.string Ty.int
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    if σ.apply (.var a) != Ty.string then
      return .failed "a should be String"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

def testUnifyMismatch : IO TestResult := do
  match Unify.unifyMono Ty.int Ty.string unifyCtx with
  | .ok _ =>
    return .failed "should fail: Int != String"
  | .error e =>
    match e with
    | .typeMismatch _ _ _ _ _ => return .passed
    | _ => return .failed "should be typeMismatch error"

def testUnifyOccursCheck : IO TestResult := do
  let a := mkTyVar "a" 0
  -- Try to unify a with (a -> Int), which would create infinite type
  let ty : MonoTy := .arrow (.var a) Ty.int
  match Unify.unifyMono (.var a) ty unifyCtx with
  | .ok _ =>
    return .failed "should fail: occurs check"
  | .error e =>
    match e with
    | .occursCheck _ _ _ => return .passed
    | _ => return .failed s!"should be occursCheck error, got {e.toDiagnostic.message}"

def testUnifyArrowMismatch : IO TestResult := do
  let ty1 : MonoTy := .arrow Ty.int Ty.int
  let ty2 : MonoTy := .arrow Ty.int Ty.string
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok _ =>
    return .failed "should fail: return types differ"
  | .error _ =>
    return .passed

def run : IO TestRunner := do
  IO.println "  === Unification Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "identical" (← testUnifyIdentical)
  runner := runner.record "var_left" (← testUnifyVarLeft)
  runner := runner.record "var_right" (← testUnifyVarRight)
  runner := runner.record "two_vars" (← testUnifyTwoVars)
  runner := runner.record "arrow" (← testUnifyArrow)
  runner := runner.record "tuple2" (← testUnifyTuple2)
  runner := runner.record "mismatch" (← testUnifyMismatch)
  runner := runner.record "occurs_check" (← testUnifyOccursCheck)
  runner := runner.record "arrow_mismatch" (← testUnifyArrowMismatch)

  return runner

end UnifyTests

namespace ConstraintTests

def testEmptyGraph : IO TestResult := do
  let g := ConstraintGraph.empty
  if g.size != 0 then
    return .failed "empty graph should have size 0"
  if g.hasUnsolved then
    return .failed "empty graph should have no unsolved constraints"
  return .passed

def testAddEquality : IO TestResult := do
  let g := ConstraintGraph.empty
  let g := g.addEquality Ty.int (tyVar "a" 0) .general testSpan testSpan
  if g.size != 1 then
    return .failed s!"graph should have 1 constraint, got {g.size}"
  if !g.hasUnsolved then
    return .failed "graph should have unsolved constraints"
  return .passed

def testAddClass : IO TestResult := do
  let eqClass := TyCon.mkUser "" "Eq" 1
  let g := ConstraintGraph.empty
  let g := g.addClass eqClass #[tyVar "a" 0] testSpan
  if g.classes.size != 1 then
    return .failed "should have 1 class constraint"
  return .passed

def testApplySubst : IO TestResult := do
  let a := mkTyVar "a" 0
  let g := ConstraintGraph.empty
  let g := g.addEquality (.var a) Ty.int .general testSpan testSpan

  let σ := Subst.fromVar a Ty.string
  let g := g.applySubst σ

  if g.equalities.isEmpty then
    return .failed "should have equalities"
  let eq := g.equalities[0]!
  if eq.lhs != Ty.string then
    return .failed s!"lhs should be String after subst, got {eq.lhs}"

  return .passed

def testRemoveTrivial : IO TestResult := do
  let g := ConstraintGraph.empty
  let g := g.addEquality Ty.int Ty.int .general testSpan testSpan  -- trivial
  let g := g.addEquality Ty.int Ty.string .general testSpan testSpan  -- non-trivial

  if g.equalities.size != 2 then
    return .failed "should have 2 constraints before removal"

  let g := g.removeTrivial
  if g.equalities.size != 1 then
    return .failed s!"should have 1 constraint after removal, got {g.equalities.size}"

  return .passed

def run : IO TestRunner := do
  IO.println "  === Constraint Graph Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "empty_graph" (← testEmptyGraph)
  runner := runner.record "add_equality" (← testAddEquality)
  runner := runner.record "add_class" (← testAddClass)
  runner := runner.record "apply_subst" (← testApplySubst)
  runner := runner.record "remove_trivial" (← testRemoveTrivial)

  return runner

end ConstraintTests

namespace InstanceTests

def eqClass : TyCon := TyCon.mkUser "" "Eq" 1
def ordClass : TyCon := TyCon.mkUser "" "Ord" 2
def showClass : TyCon := TyCon.mkUser "" "Show" 3

def testEmptyEnv : IO TestResult := do
  let env := InstanceEnv.empty
  if env.size != 0 then
    return .failed "empty env should have size 0"
  let insts := env.getInstances eqClass
  if !insts.isEmpty then
    return .failed "should have no instances for Eq"
  return .passed

def testAddInstance : IO TestResult := do
  let inst : InstanceDecl := {
    className := eqClass
    args := #[Ty.int]
    typeVars := #[]
    constraints := #[]
    id := 0
    span := testSpan
  }
  let env := InstanceEnv.empty.addInstance inst
  if env.size != 1 then
    return .failed s!"should have 1 instance, got {env.size}"

  let insts := env.getInstances eqClass
  if insts.size != 1 then
    return .failed "should have 1 Eq instance"

  return .passed

def testAddClass : IO TestResult := do
  let classDecl : TypeClassDecl := {
    name := ordClass
    params := #[mkTyVar "a" 0]
    superclasses := #[{ className := eqClass, args := #[tyVar "a" 0] }]
    span := testSpan
  }
  let env := InstanceEnv.empty.addClass classDecl

  if !env.hasClass ordClass then
    return .failed "should have Ord class"

  let supers := env.getSuperclasses ordClass
  if supers.size != 1 then
    return .failed "Ord should have 1 superclass"
  if supers[0]!.className != eqClass then
    return .failed "Ord's superclass should be Eq"

  return .passed

def testFindInstance : IO TestResult := do
  let inst : InstanceDecl := {
    className := eqClass
    args := #[Ty.int]
    typeVars := #[]
    constraints := #[]
    id := 0
    span := testSpan
  }
  let env := InstanceEnv.empty.addInstance inst

  let constraint : TyConstraint := { className := eqClass, args := #[Ty.int] }
  match env.findInstance constraint 100 with
  | some _ => return .passed
  | none => return .failed "should find Eq Int instance"

def testFindInstanceWithUnification : IO TestResult := do
  let a := mkTyVar "a" 0
  let inst : InstanceDecl := {
    className := eqClass
    args := #[.var a]
    typeVars := #[a]
    constraints := #[]
    id := 0
    span := testSpan
  }
  let env := InstanceEnv.empty.addInstance inst

  let constraint : TyConstraint := { className := eqClass, args := #[Ty.string] }
  match env.findInstance constraint 100 with
  | some (_, σ, _, _) =>
    if σ.isEmpty then
      return .failed "should have non-empty substitution"
    return .passed
  | none => return .failed "should find instance via unification"

def testFindInstanceNotFound : IO TestResult := do
  let env := InstanceEnv.empty
  let constraint : TyConstraint := { className := eqClass, args := #[Ty.int] }
  match env.findInstance constraint 100 with
  | some _ => return .failed "should not find instance in empty env"
  | none => return .passed

def testInstanceWithContext : IO TestResult := do
  -- Add instance: Eq a => Eq (Array a)
  let a := mkTyVar "a" 0
  let inst : InstanceDecl := {
    className := eqClass
    args := #[Ty.array (.var a)]
    typeVars := #[a]
    constraints := #[{ className := eqClass, args := #[.var a] }]
    id := 0
    span := testSpan
  }
  let env := InstanceEnv.empty.addInstance inst

  let constraint : TyConstraint := { className := eqClass, args := #[Ty.array Ty.int] }
  match env.findInstance constraint 100 with
  | some (_, _, subConstraints, _) =>
    if subConstraints.size != 1 then
      return .failed s!"should have 1 sub-constraint, got {subConstraints.size}"
    return .passed
  | none => return .failed "should find Eq (Array a) instance"

def run : IO TestRunner := do
  IO.println "  === Instance Environment Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "empty_env" (← testEmptyEnv)
  runner := runner.record "add_instance" (← testAddInstance)
  runner := runner.record "add_class" (← testAddClass)
  runner := runner.record "find_instance" (← testFindInstance)
  runner := runner.record "find_instance_unify" (← testFindInstanceWithUnification)
  runner := runner.record "find_instance_not_found" (← testFindInstanceNotFound)
  runner := runner.record "instance_with_context" (← testInstanceWithContext)

  return runner

end InstanceTests

namespace EntailmentTests

def eqClass : TyCon := TyCon.mkUser "" "Eq" 1
def ordClass : TyCon := TyCon.mkUser "" "Ord" 2

def testEntailsFromDeclared : IO TestResult := do
  let a := mkTyVar "a" 0
  let declared : Array TyConstraint := #[{ className := eqClass, args := #[.var a] }]
  let constraint : TyConstraint := { className := eqClass, args := #[.var a] }

  match Entailment.entails InstanceEnv.empty declared constraint testSpan with
  | .ok true => return .passed
  | .ok false => return .failed "should be entailed"
  | .error e => return .failed s!"error: {e.toDiagnostic.message}"

def testEntailsFromInstance : IO TestResult := do
  let inst : InstanceDecl := {
    className := eqClass
    args := #[Ty.int]
    typeVars := #[]
    constraints := #[]
    id := 0
    span := testSpan
  }
  let env := InstanceEnv.empty.addInstance inst
  let constraint : TyConstraint := { className := eqClass, args := #[Ty.int] }

  match Entailment.entails env #[] constraint testSpan with
  | .ok true => return .passed
  | .ok false => return .failed "should be entailed by instance"
  | .error e => return .failed s!"error: {e.toDiagnostic.message}"

def testSuperclassInstantiation : IO TestResult := do
  let a := mkTyVar "a" 0
  let ordDecl : TypeClassDecl := {
    name := ordClass
    params := #[a]
    superclasses := #[{ className := eqClass, args := #[.var a] }]
    span := testSpan
  }
  let env := InstanceEnv.empty.addClass ordDecl

  let ctx : EntailmentContext := {
    instanceEnv := env
    declaredConstraints := #[]
    subst := Subst.empty
    freshId := 100
  }

  let constraint : TyConstraint := { className := ordClass, args := #[Ty.int] }
  match Entailment.checkSuperclasses ctx constraint with
  | .ok supers =>
    if supers.size != 1 then
      return .failed s!"should have 1 superclass, got {supers.size}"
    let super := supers[0]!
    if super.className != eqClass then
      return .failed "superclass should be Eq"
    if super.args[0]? != some Ty.int then
      return .failed s!"superclass arg should be Int, got {super.args[0]?}"
    return .passed
  | .error e =>
    return .failed s!"error: {e.toDiagnostic.message}"

def run : IO TestRunner := do
  IO.println "  === Entailment Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "entails_declared" (← testEntailsFromDeclared)
  runner := runner.record "entails_instance" (← testEntailsFromInstance)
  runner := runner.record "superclass_instantiation" (← testSuperclassInstantiation)

  return runner

end EntailmentTests

namespace GenTests

def testMkTupleType0 : IO TestResult := do
  match Gen.mkTupleType #[] with
  | some ty =>
    if ty != Ty.unit then
      return .failed s!"0-tuple should be unit, got {ty}"
    return .passed
  | none => return .failed "0-tuple should succeed"

def testMkTupleType1 : IO TestResult := do
  match Gen.mkTupleType #[Ty.int] with
  | some ty =>
    if ty != Ty.int then
      return .failed s!"1-tuple should be the element, got {ty}"
    return .passed
  | none => return .failed "1-tuple should succeed"

def testMkTupleType2 : IO TestResult := do
  match Gen.mkTupleType #[Ty.int, Ty.string] with
  | some ty =>
    if ty != Ty.tuple2 Ty.int Ty.string then
      return .failed s!"2-tuple mismatch, got {ty}"
    return .passed
  | none => return .failed "2-tuple should succeed"

def testMkTupleType8 : IO TestResult := do
  let tys := #[Ty.int, Ty.int, Ty.int, Ty.int, Ty.int, Ty.int, Ty.int, Ty.int]
  match Gen.mkTupleType tys with
  | some _ => return .passed
  | none => return .failed "8-tuple should succeed"

def testMkTupleType9 : IO TestResult := do
  let tys := #[Ty.int, Ty.int, Ty.int, Ty.int, Ty.int, Ty.int, Ty.int, Ty.int, Ty.int]
  match Gen.mkTupleType tys with
  | some _ => return .failed "9-tuple should fail"
  | none => return .passed

def testFreshVars : IO TestResult := do
  let ctx := InferContext.empty
  let (vars, state) := (Gen.freshVars 3 "test").run ctx

  if vars.size != 3 then
    return .failed s!"should generate 3 vars, got {vars.size}"

  if state.freshCounter != 3 then
    return .failed s!"fresh counter should be 3, got {state.freshCounter}"

  for i in [:vars.size] do
    for j in [i+1:vars.size] do
      if vars[i]! == vars[j]! then
        return .failed "generated vars should be distinct"

  return .passed

def run : IO TestRunner := do
  IO.println "  === Gen Helper Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "mk_tuple_0" (← testMkTupleType0)
  runner := runner.record "mk_tuple_1" (← testMkTupleType1)
  runner := runner.record "mk_tuple_2" (← testMkTupleType2)
  runner := runner.record "mk_tuple_8" (← testMkTupleType8)
  runner := runner.record "mk_tuple_9_fails" (← testMkTupleType9)
  runner := runner.record "fresh_vars" (← testFreshVars)

  return runner

end GenTests

namespace MonadTests

def testFreshVar : IO TestResult := do
  let ctx := InferContext.empty
  let m : InferM (MonoTy × MonoTy) := do
    let v1 ← InferM.freshVar "a"
    let v2 ← InferM.freshVar "b"
    return (v1, v2)
  let ((v1, v2), state) := m.run ctx

  if v1 == v2 then
    return .failed "fresh vars should be distinct"
  if state.freshCounter != 2 then
    return .failed s!"counter should be 2, got {state.freshCounter}"

  return .passed

def testErrorAccumulation : IO TestResult := do
  let ctx := InferContext.empty
  let m : InferM Unit := do
    InferM.reportError (.unknownVariable "x" testSpan)
    InferM.reportError (.unknownVariable "y" testSpan)
    InferM.reportError (.unknownVariable "z" testSpan)
  let (_, state) := m.run ctx

  if state.errors.size != 3 then
    return .failed s!"should have 3 errors, got {state.errors.size}"

  return .passed

def testWithLocal : IO TestResult := do
  let ctx := InferContext.empty
  let m : InferM (Option VarInfo × Option VarInfo) := do
    let info : VarInfo := { ty := Ty.int, bindingId := mkBindingId 0, name := "x" }
    let inner ← InferM.withLocal "x" info do
      InferM.lookupLocal "x"
    let outer ← InferM.lookupLocal "x"
    return (inner, outer)
  let ((inner, outer), _) := m.run ctx

  if inner.isNone then
    return .failed "should find 'x' inside withLocal"
  if outer.isSome then
    return .failed "should not find 'x' outside withLocal"

  return .passed

def testInstantiate : IO TestResult := do
  let a := mkTyVar "a" 0
  let qt : QualifiedType := {
    vars := #[a]
    constraints := #[{ className := TyCon.mkUser "" "Eq" 1, args := #[.var a] }]
    body := .arrow (.var a) (.var a)
  }

  let ctx := InferContext.empty
  let m : InferM (MonoTy × Array TyConstraint) := InferM.instantiate qt
  let ((ty, constraints), state) := m.run ctx

  if state.freshCounter != 1 then
    return .failed s!"should have 1 fresh var, got {state.freshCounter}"

  match ty with
  | .arrow from_ to =>
    if from_ != to then
      return .failed "instantiated type should have same from/to"
  | _ => return .failed "should be arrow type"

  if constraints.size != 1 then
    return .failed s!"should have 1 constraint, got {constraints.size}"

  return .passed

def run : IO TestRunner := do
  IO.println "  === InferM Monad Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "fresh_var" (← testFreshVar)
  runner := runner.record "error_accumulation" (← testErrorAccumulation)
  runner := runner.record "with_local" (← testWithLocal)
  runner := runner.record "instantiate" (← testInstantiate)

  return runner

end MonadTests

def run : IO Unit := do
  IO.println "=== Type Inference Tests ==="
  IO.println ""

  let mut totalPassed := 0
  let mut totalFailed := 0

  let substRunner ← SubstitutionTests.run
  totalPassed := totalPassed + substRunner.passed
  totalFailed := totalFailed + substRunner.failed

  let unifyRunner ← UnifyTests.run
  totalPassed := totalPassed + unifyRunner.passed
  totalFailed := totalFailed + unifyRunner.failed

  let constraintRunner ← ConstraintTests.run
  totalPassed := totalPassed + constraintRunner.passed
  totalFailed := totalFailed + constraintRunner.failed

  let instanceRunner ← InstanceTests.run
  totalPassed := totalPassed + instanceRunner.passed
  totalFailed := totalFailed + instanceRunner.failed

  let entailmentRunner ← EntailmentTests.run
  totalPassed := totalPassed + entailmentRunner.passed
  totalFailed := totalFailed + entailmentRunner.failed

  let genRunner ← GenTests.run
  totalPassed := totalPassed + genRunner.passed
  totalFailed := totalFailed + genRunner.failed

  let monadRunner ← MonadTests.run
  totalPassed := totalPassed + monadRunner.passed
  totalFailed := totalFailed + monadRunner.failed

  IO.println ""
  IO.println "=== Inference Test Summary ==="
  IO.println s!"  Total Passed: {totalPassed}"
  IO.println s!"  Total Failed: {totalFailed}"

  if totalFailed > 0 then
    IO.println "  SOME TESTS FAILED"
  else
    IO.println "  ALL TESTS PASSED"

end Test.Infer
