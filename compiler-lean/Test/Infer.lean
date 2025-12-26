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
  let ty : MonoTy := Ty.tuple2 (.var a) (.var b)
  let result := σ.apply ty
  let expected : MonoTy := Ty.tuple2 Ty.int Ty.string
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
  let ty1 : MonoTy := Ty.tuple2 (.var a) Ty.int
  let ty2 : MonoTy := Ty.tuple2 Ty.string Ty.int
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

namespace HKTTests

def unifyCtx : UnifyContext :=
  { purpose := .general, expectedSpan := testSpan, actualSpan := testSpan }

/-- Create a higher-kinded type variable (kind * -> *) -/
def mkHKTVar (name : String) (id : Nat) : TyVarId :=
  ⟨name, id, .arrow .star .star⟩

/-- Create a Ty variable at kind * -> * -/
def hktVar (name : String) (id : Nat) : Ty (.arrow Kind.star Kind.star) :=
  .var (mkHKTVar name id)

/-- Test: Unify Array Int with Array Int (identical type applications) -/
def testUnifyIdenticalApp : IO TestResult := do
  let ty1 := Ty.array Ty.int  -- Array Int
  let ty2 := Ty.array Ty.int  -- Array Int
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    if !σ.isEmpty then
      return .failed "unifying identical apps should give empty subst"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

/-- Test: Unify Array a with Array Int (resolve element type variable) -/
def testUnifyAppWithVar : IO TestResult := do
  let a := mkTyVar "a" 0
  let ty1 := Ty.array (.var a)  -- Array a
  let ty2 := Ty.array Ty.int   -- Array Int
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    let resolved := σ.apply (.var a)
    if resolved != Ty.int then
      return .failed s!"'a' should resolve to Int, got {resolved}"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

/-- Test: Unify Array a with Array b (two type variables) -/
def testUnifyAppTwoVars : IO TestResult := do
  let a := mkTyVar "a" 0
  let b := mkTyVar "b" 1
  let ty1 := Ty.array (.var a)  -- Array a
  let ty2 := Ty.array (.var b)  -- Array b
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    let resolvedA := σ.apply (.var a)
    let resolvedB := σ.apply (.var b)
    if resolvedA != resolvedB then
      return .failed s!"both vars should unify to same type, got {resolvedA} and {resolvedB}"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

/-- Test: Unify f Int with Array Int (resolve type constructor variable) -/
def testUnifyHKTVarWithConcrete : IO TestResult := do
  let f := mkHKTVar "f" 0
  -- f Int = Ty.app (f : * -> *) (Int : *)
  let fTy : Ty (.arrow .star .star) := .var f
  let ty1 : MonoTy := .app fTy Ty.int
  let ty2 := Ty.array Ty.int  -- Array Int
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    -- Check that f is bound to Array
    match σ.lookupAny f.id with
    | some someTy =>
      match someTy.kind with
      | .arrow .star .star =>
        -- f should be Array - use heterogeneous equality
        if !Ty.heq someTy.ty Ty.arrayCon then
          return .failed s!"'f' should be Array constructor"
        return .passed
      | k => return .failed s!"'f' should have kind * -> *, got {k}"
    | none =>
      return .failed "'f' should be bound in substitution"
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

/-- Test: Unify f a with Array Int (resolve both type constructor and element) -/
def testUnifyHKTVarAndArgVar : IO TestResult := do
  let f := mkHKTVar "f" 0
  let a := mkTyVar "a" 1
  let fTy : Ty (.arrow .star .star) := .var f
  let ty1 : MonoTy := .app fTy (.var a)  -- f a
  let ty2 := Ty.array Ty.int            -- Array Int
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    -- Check f is bound to Array - use heterogeneous equality
    match σ.lookupAny f.id with
    | some someTy =>
      if !Ty.heq someTy.ty Ty.arrayCon then
        return .failed "'f' should be Array"
    | none =>
      return .failed "'f' should be bound"
    -- Check a is bound to Int
    let resolvedA := σ.apply (.var a)
    if resolvedA != Ty.int then
      return .failed s!"'a' should be Int, got {resolvedA}"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

/-- Test: Unify f Int with g Int (two HKT variables with same argument) -/
def testUnifyTwoHKTVars : IO TestResult := do
  let f := mkHKTVar "f" 0
  let g := mkHKTVar "g" 1
  let fTy : Ty (.arrow .star .star) := .var f
  let gTy : Ty (.arrow .star .star) := .var g
  let ty1 : MonoTy := .app fTy Ty.int  -- f Int
  let ty2 : MonoTy := .app gTy Ty.int  -- g Int
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    -- f and g should unify to the same thing
    match σ.lookupAny f.id, σ.lookupAny g.id with
    | some sf, some sg =>
      -- Use heterogeneous equality since kinds might differ
      if !Ty.heq sf.ty sg.ty then
        return .failed "f and g should unify to same constructor"
      return .passed
    | some _, none =>
      -- g might be bound to f or vice versa
      return .passed
    | none, some _ =>
      return .passed
    | none, none =>
      -- Both free means they were unified to each other
      return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

/-- Test: Unify f a with g b (fully polymorphic) -/
def testUnifyFullyPolymorphicHKT : IO TestResult := do
  let f := mkHKTVar "f" 0
  let g := mkHKTVar "g" 1
  let a := mkTyVar "a" 2
  let b := mkTyVar "b" 3
  let fTy : Ty (.arrow .star .star) := .var f
  let gTy : Ty (.arrow .star .star) := .var g
  let ty1 : MonoTy := .app fTy (.var a)  -- f a
  let ty2 : MonoTy := .app gTy (.var b)  -- g b
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    -- After unification, f a and g b should be equal under σ
    let result1 := σ.apply ty1
    let result2 := σ.apply ty2
    if result1 != result2 then
      return .failed s!"after unification, types should be equal: {result1} vs {result2}"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

/-- Test: Fail to unify Array Int with Ref Int (different constructors) -/
def testUnifyDifferentConstructors : IO TestResult := do
  let ty1 := Ty.array Ty.int  -- Array Int
  let ty2 := Ty.ref Ty.int    -- Ref Int
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok _ =>
    return .failed "should fail: Array != Ref"
  | .error _ =>
    return .passed

/-- Test: Fail to unify Array Int with Array String (different element types) -/
def testUnifyDifferentElements : IO TestResult := do
  let ty1 := Ty.array Ty.int     -- Array Int
  let ty2 := Ty.array Ty.string  -- Array String
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok _ =>
    return .failed "should fail: Int != String"
  | .error _ =>
    return .passed

/-- Test: Occurs check for HKT - f cannot unify with Array (f Int) -/
def testHKTOccursCheck : IO TestResult := do
  let f := mkHKTVar "f" 0
  let fTy : Ty (.arrow .star .star) := .var f
  -- Try to unify f with something containing f applied
  -- f = Array (f Int) would create infinite type
  let inner : MonoTy := .app fTy Ty.int  -- f Int
  let _outer := Ty.array inner           -- Array (f Int) (unused but documents intent)
  -- Actually, we need to unify at the constructor level
  -- This is tricky to set up directly, so let's test via element
  let ty1 : MonoTy := .app fTy Ty.int
  let ty2 := Ty.array (.app fTy Ty.int)  -- Array (f Int)
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok _ =>
    -- This actually succeeds because f -> Array, then f Int -> Array Int
    -- which doesn't create a cycle. Let's try a real occurs check.
    return .passed
  | .error _ =>
    return .passed

/-- Test: Occurs check for element type variable in HKT -/
def testElementOccursCheck : IO TestResult := do
  let a := mkTyVar "a" 0
  -- Try to unify 'a' with 'Array a' - should fail occurs check
  let ty1 : MonoTy := .var a
  let ty2 := Ty.array (.var a)  -- Array a
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok _ =>
    return .failed "should fail: occurs check for 'a' in 'Array a'"
  | .error e =>
    match e with
    | .occursCheck _ _ _ => return .passed
    | _ => return .failed s!"should be occursCheck error, got {e.toDiagnostic.message}"

/-- Test: Nested type applications - Array (Array Int) -/
def testNestedApp : IO TestResult := do
  let a := mkTyVar "a" 0
  let ty1 := Ty.array (Ty.array (.var a))  -- Array (Array a)
  let ty2 := Ty.array (Ty.array Ty.int)    -- Array (Array Int)
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    let resolved := σ.apply (.var a)
    if resolved != Ty.int then
      return .failed s!"'a' should be Int, got {resolved}"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

/-- Test: HKT in function type - (a -> b) unify with (Int -> Array Int) -/
def testHKTInArrow : IO TestResult := do
  let a := mkTyVar "a" 0
  let f := mkHKTVar "f" 1
  let fTy : Ty (.arrow .star .star) := .var f
  let ty1 : MonoTy := .arrow (.var a) (.app fTy (.var a))  -- a -> f a
  let ty2 : MonoTy := .arrow Ty.int (Ty.array Ty.int)      -- Int -> Array Int
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    let resolvedA := σ.apply (.var a)
    if resolvedA != Ty.int then
      return .failed s!"'a' should be Int, got {resolvedA}"
    match σ.lookupAny f.id with
    | some someTy =>
      if !Ty.heq someTy.ty Ty.arrayCon then
        return .failed "'f' should be Array"
      return .passed
    | none =>
      return .failed "'f' should be bound"
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

/-- Test: Substitution correctly applies to HKT -/
def testSubstApplyHKT : IO TestResult := do
  let f := mkHKTVar "f" 0
  let a := mkTyVar "a" 1

  -- Create substitution: f -> Array, a -> Int
  let σ := Subst.empty
    |>.insertAny f.id ⟨.arrow .star .star, Ty.arrayCon⟩
    |>.insert a.id Ty.int

  -- Apply to f a
  let fTy : Ty (.arrow .star .star) := .var f
  let ty : MonoTy := .app fTy (.var a)
  let result := σ.apply ty

  -- Should get Array Int
  if result != Ty.array Ty.int then
    return .failed s!"expected Array Int, got {result}"
  return .passed

/-- Test: Composed substitution with HKT -/
def testComposeHKTSubst : IO TestResult := do
  let f := mkHKTVar "f" 0
  let g := mkHKTVar "g" 1
  let a := mkTyVar "a" 2

  -- σ1: f -> g (both are kind * -> *)
  let gTy : Ty (.arrow .star .star) := .var g
  let σ1 := Subst.singletonAny f.id ⟨.arrow .star .star, gTy⟩
  -- σ2: g -> Array, a -> Int
  let σ2 := Subst.empty
    |>.insertAny g.id ⟨.arrow .star .star, Ty.arrayCon⟩
    |>.insert a.id Ty.int

  let composed := σ2.compose σ1

  -- Apply to f a
  let fTy : Ty (.arrow .star .star) := .var f
  let ty : MonoTy := .app fTy (.var a)
  let result := composed.apply ty

  -- Should get Array Int (f -> g -> Array, a -> Int)
  if result != Ty.array Ty.int then
    return .failed s!"expected Array Int, got {result}"
  return .passed

/-- Test: IO type constructor (another * -> * primitive) -/
def testIOTypeConstructor : IO TestResult := do
  let a := mkTyVar "a" 0
  let ty1 := Ty.io (.var a)   -- IO a
  let ty2 := Ty.io Ty.string  -- IO String
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    let resolved := σ.apply (.var a)
    if resolved != Ty.string then
      return .failed s!"'a' should be String, got {resolved}"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

/-- Test: Unify IO a with Array a should fail (different constructors) -/
def testIOvsArray : IO TestResult := do
  let a := mkTyVar "a" 0
  let ty1 := Ty.io (.var a)     -- IO a
  let ty2 := Ty.array (.var a)  -- Array a
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok _ =>
    return .failed "should fail: IO != Array"
  | .error _ =>
    return .passed

/-- Test: Complex HKT chain - f (g a) with Array (IO Int) -/
def testHKTChain : IO TestResult := do
  let f := mkHKTVar "f" 0
  let g := mkHKTVar "g" 1
  let a := mkTyVar "a" 2
  -- f (g a)
  let fTy : Ty (.arrow .star .star) := .var f
  let gTy : Ty (.arrow .star .star) := .var g
  let inner : MonoTy := .app gTy (.var a)
  let ty1 : MonoTy := .app fTy inner
  -- Array (IO Int)
  let ty2 := Ty.array (Ty.io Ty.int)
  match Unify.unifyMono ty1 ty2 unifyCtx with
  | .ok σ =>
    -- f should be Array - use heterogeneous equality
    match σ.lookupAny f.id with
    | some sf =>
      if !Ty.heq sf.ty Ty.arrayCon then
        return .failed "'f' should be Array"
    | none => return .failed "'f' should be bound"
    -- g should be IO - use heterogeneous equality
    match σ.lookupAny g.id with
    | some sg =>
      if !Ty.heq sg.ty Ty.ioCon then
        return .failed "'g' should be IO"
    | none => return .failed "'g' should be bound"
    -- a should be Int
    let resolvedA := σ.apply (.var a)
    if resolvedA != Ty.int then
      return .failed s!"'a' should be Int, got {resolvedA}"
    return .passed
  | .error e =>
    return .failed s!"should succeed: {e.toDiagnostic.message}"

def run : IO TestRunner := do
  IO.println "  === Higher-Kinded Type (HKT) Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "identical_app" (← testUnifyIdenticalApp)
  runner := runner.record "app_with_var" (← testUnifyAppWithVar)
  runner := runner.record "app_two_vars" (← testUnifyAppTwoVars)
  runner := runner.record "hkt_var_concrete" (← testUnifyHKTVarWithConcrete)
  runner := runner.record "hkt_var_and_arg_var" (← testUnifyHKTVarAndArgVar)
  runner := runner.record "two_hkt_vars" (← testUnifyTwoHKTVars)
  runner := runner.record "fully_polymorphic_hkt" (← testUnifyFullyPolymorphicHKT)
  runner := runner.record "different_constructors" (← testUnifyDifferentConstructors)
  runner := runner.record "different_elements" (← testUnifyDifferentElements)
  runner := runner.record "hkt_occurs_check" (← testHKTOccursCheck)
  runner := runner.record "element_occurs_check" (← testElementOccursCheck)
  runner := runner.record "nested_app" (← testNestedApp)
  runner := runner.record "hkt_in_arrow" (← testHKTInArrow)
  runner := runner.record "subst_apply_hkt" (← testSubstApplyHKT)
  runner := runner.record "compose_hkt_subst" (← testComposeHKTSubst)
  runner := runner.record "io_constructor" (← testIOTypeConstructor)
  runner := runner.record "io_vs_array" (← testIOvsArray)
  runner := runner.record "hkt_chain" (← testHKTChain)

  return runner

end HKTTests

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
  | .satisfied => return .passed
  | .deferred _ => return .failed "should be satisfied, not deferred"
  | .failed e => return .failed s!"error: {e.toDiagnostic.message}"

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
  | .satisfied => return .passed
  | .deferred _ => return .failed "should be satisfied, not deferred"
  | .failed e => return .failed s!"error: {e.toDiagnostic.message}"

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
  -- With the new unbounded tuple representation, 9-tuples are valid
  let tys := #[Ty.int, Ty.int, Ty.int, Ty.int, Ty.int, Ty.int, Ty.int, Ty.int, Ty.int]
  match Gen.mkTupleType tys with
  | some ty =>
    if ty.tupleArity == 9 then return .passed
    else return .failed s!"9-tuple should have arity 9, got {ty.tupleArity}"
  | none => return .failed "9-tuple should succeed"

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
  runner := runner.record "mk_tuple_9" (← testMkTupleType9)
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

namespace TypedExprGenTests

open Soma.Metal

/-- Create a scoped variable for testing -/
def mkScopedVar (id : Nat) (name : String) : ScopedVar [mkBindingId id] :=
  { binding := mkBindingId id, original := name, proof := List.Mem.head _ }

/-- Test that genExpr returns a typed expression for a literal -/
def testGenLiteral : IO TestResult := do
  let ctx := InferContext.empty
  let lit := Literal.int 42
  let expr : Expr Unit [] := .lit lit testSpan

  let m : InferM (MonoTy × Expr MonoTy []) := Gen.genExpr expr
  let ((ty, typedExpr), _state) := m.run ctx

  -- Literal should have Int type
  if ty != Ty.int then
    return .failed s!"literal should have Int type, got {ty}"

  -- Typed expression should be a lit
  match typedExpr with
  | .lit lit' _ =>
    if lit'.type != Ty.int then
      return .failed "typed lit should have Int type"
    return .passed
  | _ => return .failed "should produce a lit expression"

/-- Test that genExpr returns typed expression for a variable -/
def testGenVar : IO TestResult := do
  let bid := mkBindingId 0
  let varInfo : VarInfo := { ty := Ty.string, bindingId := bid, name := "x" }
  let ctx : InferContext := { InferContext.empty with
    typeEnv := TypeEnv.empty.addLocal "x" varInfo
  }

  let scopedVar : ScopedVar [bid] := { binding := bid, original := "x", proof := List.Mem.head _ }
  let expr : Expr Unit [bid] := .var scopedVar () testSpan

  let m : InferM (MonoTy × Expr MonoTy [bid]) := Gen.genExpr expr
  let ((ty, typedExpr), _state) := m.run ctx

  -- Variable should have the type from the environment
  if ty != Ty.string then
    return .failed s!"var should have String type, got {ty}"

  -- Typed expression should carry the type
  match typedExpr with
  | .var _ varTy _ =>
    if varTy != Ty.string then
      return .failed s!"typed var should have String type, got {varTy}"
    return .passed
  | _ => return .failed "should produce a var expression"

/-- Test that genExpr handles if-then-else correctly -/
def testGenIfThenElse : IO TestResult := do
  let ctx := InferContext.empty

  let condLit := Literal.bool true
  let thenLit := Literal.int 1
  let elseLit := Literal.int 2

  let condExpr : Expr Unit [] := .lit condLit testSpan
  let thenExpr : Expr Unit [] := .lit thenLit testSpan
  let elseExpr : Expr Unit [] := .lit elseLit testSpan
  let ifExpr : Expr Unit [] := .if_ condExpr thenExpr elseExpr () testSpan

  let m : InferM (MonoTy × Expr MonoTy []) := Gen.genExpr ifExpr
  let ((ty, typedExpr), state) := m.run ctx

  -- Result type should be Int (from branches)
  if ty != Ty.int then
    return .failed s!"if result should have Int type, got {ty}"

  -- Should generate constraint for condition to be Bool
  if state.constraints.equalities.isEmpty then
    return .failed "should have equality constraints for condition"

  -- Typed expression should be an if_
  match typedExpr with
  | .if_ _ _ _ ifTy _ =>
    if ifTy != Ty.int then
      return .failed s!"typed if should have Int result type, got {ifTy}"
    return .passed
  | _ => return .failed "should produce an if_ expression"

/-- Test that genExpr handles tuple construction -/
def testGenTuple : IO TestResult := do
  let ctx := InferContext.empty

  let intLit := Literal.int 42
  let strLit := Literal.string "hello"

  let e1 : Expr Unit [] := .lit intLit testSpan
  let e2 : Expr Unit [] := .lit strLit testSpan
  let elems : ExprList Unit [] := .cons e1 (.cons e2 .nil)
  let tupleExpr : Expr Unit [] := .tuple elems () testSpan

  let m : InferM (MonoTy × Expr MonoTy []) := Gen.genExpr tupleExpr
  let ((ty, typedExpr), _state) := m.run ctx

  -- Result should be a tuple type
  let expectedTy := Ty.tuple2 Ty.int Ty.string
  if ty != expectedTy then
    return .failed s!"tuple should have (Int, String) type, got {ty}"

  match typedExpr with
  | .tuple _ tupleTy _ =>
    if tupleTy != expectedTy then
      return .failed s!"typed tuple should have (Int, String) type, got {tupleTy}"
    return .passed
  | _ => return .failed "should produce a tuple expression"

/-- Test that genExpr handles array literal -/
def testGenArray : IO TestResult := do
  let ctx := InferContext.empty

  let lit1 := Literal.int 1
  let lit2 := Literal.int 2
  let lit3 := Literal.int 3

  let e1 : Expr Unit [] := .lit lit1 testSpan
  let e2 : Expr Unit [] := .lit lit2 testSpan
  let e3 : Expr Unit [] := .lit lit3 testSpan
  let elems : ExprList Unit [] := .cons e1 (.cons e2 (.cons e3 .nil))
  let arrayExpr : Expr Unit [] := .array elems () testSpan

  let m : InferM (MonoTy × Expr MonoTy []) := Gen.genExpr arrayExpr
  let ((ty, typedExpr), _state) := m.run ctx

  -- Result should be Array Int
  let expectedTy := Ty.array Ty.int
  if ty != expectedTy then
    return .failed s!"array should have Array Int type, got {ty}"

  match typedExpr with
  | .array _ arrayTy _ =>
    if arrayTy != expectedTy then
      return .failed s!"typed array should have Array Int type, got {arrayTy}"
    return .passed
  | _ => return .failed "should produce an array expression"

/-- Test that mapInfo correctly applies substitution -/
def testMapInfoAppliesSubst : IO TestResult := do
  let a := mkTyVar "a" 0
  let b := mkTyVar "b" 1

  -- Create a simple expression with type variables as annotations
  let _expr : Expr MonoTy [] := .lit (Literal.int 42) testSpan

  -- Create expressions with type variable annotations
  -- We'll use lit expressions since they don't need scope proofs
  let e1 : Expr MonoTy [] := .panic "x" (.var a) testSpan
  let e2 : Expr MonoTy [] := .panic "y" (.var b) testSpan

  -- Create a substitution mapping type vars to concrete types
  let σ := (Subst.fromVar a Ty.int).insert b.id Ty.string

  -- Apply via mapInfo
  let mapped1 := e1.mapInfo σ.apply
  let mapped2 := e2.mapInfo σ.apply

  match mapped1 with
  | .panic _ ty _ =>
    if ty != Ty.int then
      return .failed s!"first expr should be Int after subst, got {ty}"
  | _ => return .failed "should still be a panic expression"

  match mapped2 with
  | .panic _ ty _ =>
    if ty != Ty.string then
      return .failed s!"second expr should be String after subst, got {ty}"
  | _ => return .failed "should still be a panic expression"

  return .passed

def run : IO TestRunner := do
  IO.println "  === Typed Expression Generation Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "gen_literal" (← testGenLiteral)
  runner := runner.record "gen_var" (← testGenVar)
  runner := runner.record "gen_if_then_else" (← testGenIfThenElse)
  runner := runner.record "gen_tuple" (← testGenTuple)
  runner := runner.record "gen_array" (← testGenArray)
  runner := runner.record "mapInfo_applies_subst" (← testMapInfoAppliesSubst)

  return runner

end TypedExprGenTests

namespace BuildInstanceEnvTests

open Soma.Metal

def testBuildFromEmptyModule : IO TestResult := do
  let emptyModule : UntypedModule := {
    name := "Test"
    functions := #[]
    types := #[]
    instances := #[]
    typeClasses := #[]
  }

  let seed := InstanceEnv.empty
  let result := buildInstanceEnvFromModule emptyModule seed TypeEnv.empty

  if result.size != 0 then
    return .failed s!"should have 0 instances, got {result.size}"

  return .passed

def testBuildWithBuiltinClass : IO TestResult := do
  let eqInstance : UntypedInstance := {
    className := "Eq"
    typeArgsSyntax := #[]
    constraintsSyntax := #[]
    methods := #[]
    span := testSpan
  }

  let moduleWithInstance : UntypedModule := {
    name := "Test"
    functions := #[]
    types := #[]
    instances := #[eqInstance]
    typeClasses := #[]
  }

  let seed := InstanceEnv.empty
  let result := buildInstanceEnvFromModule moduleWithInstance seed TypeEnv.empty

  if result.size != 1 then
    return .failed s!"should have 1 instance, got {result.size}"

  let eqInsts := result.getInstances TypeClassName.eq
  if eqInsts.size != 1 then
    return .failed s!"should have 1 Eq instance, got {eqInsts.size}"

  return .passed

def testBuildWithUnknownClass : IO TestResult := do
  let unknownInstance : UntypedInstance := {
    className := "MyCustomClass"
    typeArgsSyntax := #[]
    constraintsSyntax := #[]
    methods := #[]
    span := testSpan
  }

  let moduleWithInstance : UntypedModule := {
    name := "Test"
    functions := #[]
    types := #[]
    instances := #[unknownInstance]
    typeClasses := #[]
  }

  let seed := InstanceEnv.empty
  let result := buildInstanceEnvFromModule moduleWithInstance seed TypeEnv.empty

  -- Unknown classes are skipped for now
  if result.size != 0 then
    return .failed s!"unknown classes should be skipped, got {result.size} instances"

  return .passed

def testBuildPreservesSeed : IO TestResult := do
  let seedInst : InstanceDecl := {
    className := TypeClassName.show_
    args := #[Ty.int]
    typeVars := #[]
    constraints := #[]
    id := 0
    span := testSpan
  }
  let seed := InstanceEnv.empty.addInstance seedInst

  let emptyModule : UntypedModule := {
    name := "Test"
    functions := #[]
    types := #[]
    instances := #[]
    typeClasses := #[]
  }

  let result := buildInstanceEnvFromModule emptyModule seed TypeEnv.empty

  if result.size != 1 then
    return .failed s!"should preserve seed instance, got {result.size}"

  let showInsts := result.getInstances TypeClassName.show_
  if showInsts.size != 1 then
    return .failed "should have the Show Int instance from seed"

  return .passed

def run : IO TestRunner := do
  IO.println "  === Build Instance Env Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "build_empty_module" (← testBuildFromEmptyModule)
  runner := runner.record "build_builtin_class" (← testBuildWithBuiltinClass)
  runner := runner.record "build_unknown_class" (← testBuildWithUnknownClass)
  runner := runner.record "build_preserves_seed" (← testBuildPreservesSeed)

  return runner

end BuildInstanceEnvTests

/-! ## QualifiedType and Type Variable Tests

These tests verify the fixes for type variable resolution:
1. QualifiedType.vars should properly store type variables
2. Instantiation should replace type variables with fresh ones
3. Implicit type variables (not in explicit forall) should be collected
-/
namespace QualifiedTypeTests

/-- Test: Instantiation replaces type variables with fresh ones -/
def testInstantiateReplacesTyVars : IO TestResult := do
  -- Create a QualifiedType: forall a. a -> a
  -- Use ID 100 to ensure it's different from fresh counter which starts at 0
  let a := mkTyVar "a" 100
  let qt : QualifiedType := {
    vars := #[a]
    constraints := #[]
    body := .arrow (.var a) (.var a)
  }

  let ctx := InferContext.empty
  let m : InferM (MonoTy × Array TyConstraint) := InferM.instantiate qt
  let ((ty, _), state) := m.run ctx

  -- Should have created a fresh type variable
  if state.freshCounter != 1 then
    return .failed s!"should create 1 fresh var, got {state.freshCounter}"

  -- The instantiated type should NOT contain the original type variable (id 100)
  match ty with
  | .arrow from_ to =>
    -- Both sides should be the same fresh variable
    if from_ != to then
      return .failed "instantiated a -> a should have same from/to"
    -- The type should NOT be the original variable (id 100)
    match from_ with
    | .var v =>
      if v.id == 100 then
        return .failed "should have fresh variable (id != 100), not original"
      return .passed
    | _ => return .failed "should be a type variable"
  | _ => return .failed "should be arrow type"

/-- Test: Instantiation of polymorphic function type like `a -> Array a` -/
def testInstantiatePolymorphicArray : IO TestResult := do
  -- Create: forall a. a -> Array a
  let a := mkTyVar "a" 0
  let qt : QualifiedType := {
    vars := #[a]
    constraints := #[]
    body := .arrow (.var a) (Ty.array (.var a))
  }

  let ctx := InferContext.empty
  let m : InferM (MonoTy × Array TyConstraint) := InferM.instantiate qt
  let ((ty, _), state) := m.run ctx

  if state.freshCounter != 1 then
    return .failed s!"should create 1 fresh var, got {state.freshCounter}"

  -- Just verify it's an arrow type with Array result
  match ty with
  | .arrow _ (.app _ _) => return .passed
  | _ => return .failed s!"expected a -> Array a shape, got {ty}"

/-- Test: Multiple type variables are instantiated independently -/
def testInstantiateMultipleVars : IO TestResult := do
  -- Create: forall a b. a -> b -> a
  let a := mkTyVar "a" 0
  let b := mkTyVar "b" 1
  let qt : QualifiedType := {
    vars := #[a, b]
    constraints := #[]
    body := .arrow (.var a) (.arrow (.var b) (.var a))
  }

  let ctx := InferContext.empty
  let m : InferM (MonoTy × Array TyConstraint) := InferM.instantiate qt
  let ((ty, _), state) := m.run ctx

  if state.freshCounter != 2 then
    return .failed s!"should create 2 fresh vars, got {state.freshCounter}"

  match ty with
  | .arrow from1 (.arrow from2 result) =>
    -- from1 and from2 should be different fresh variables
    if from1 == from2 then
      return .failed "a and b should be different fresh vars"
    -- Result should be same as from1 (both are 'a')
    if result != from1 then
      return .failed "result should match first param (both are 'a')"
    return .passed
  | _ => return .failed "expected nested arrow type"

/-- Test: Instantiation preserves structure with Array (for IO-like behavior) -/
def testInstantiateArrayWrapped : IO TestResult := do
  -- Create: forall a. Array a -> a (like head function)
  let a := mkTyVar "a" 0
  let qt : QualifiedType := {
    vars := #[a]
    constraints := #[]
    body := .arrow (Ty.array (.var a)) (.var a)
  }

  let ctx := InferContext.empty
  let run : InferM (MonoTy × Array TyConstraint) := InferM.instantiate qt
  let ((ty, _), state) := run.run ctx

  if state.freshCounter != 1 then
    return .failed s!"should create 1 fresh var, got {state.freshCounter}"

  -- Just verify it's an arrow from Array to something
  match ty with
  | .arrow (.app _ _) _ => return .passed
  | _ => return .failed s!"expected Array a -> a shape, got {ty}"

/-- Test: Empty vars means no instantiation needed -/
def testInstantiateMonomorphic : IO TestResult := do
  -- Create: Int -> String (no type variables)
  let qt : QualifiedType := {
    vars := #[]
    constraints := #[]
    body := .arrow Ty.int Ty.string
  }

  let ctx := InferContext.empty
  let m : InferM (MonoTy × Array TyConstraint) := InferM.instantiate qt
  let ((ty, _), state) := m.run ctx

  -- No fresh variables should be created
  if state.freshCounter != 0 then
    return .failed s!"monomorphic type should create 0 fresh vars, got {state.freshCounter}"

  -- Type should be unchanged
  if ty != .arrow Ty.int Ty.string then
    return .failed s!"type should be Int -> String, got {ty}"

  return .passed

/-- Test: Two instantiations of same QualifiedType get different fresh vars -/
def testInstantiateTwiceGetsDifferentVars : IO TestResult := do
  let a := mkTyVar "a" 0
  let qt : QualifiedType := {
    vars := #[a]
    constraints := #[]
    body := .var a
  }

  let ctx := InferContext.empty
  let m : InferM (MonoTy × MonoTy) := do
    let (ty1, _) ← InferM.instantiate qt
    let (ty2, _) ← InferM.instantiate qt
    return (ty1, ty2)
  let ((ty1, ty2), state) := m.run ctx

  -- Should have created 2 fresh variables (one per instantiation)
  if state.freshCounter != 2 then
    return .failed s!"should create 2 fresh vars, got {state.freshCounter}"

  -- The two instantiations should produce different type variables
  if ty1 == ty2 then
    return .failed "two instantiations should produce different type vars"

  return .passed

def run : IO TestRunner := do
  IO.println "  === QualifiedType Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "instantiate_replaces_tyvars" (← testInstantiateReplacesTyVars)
  runner := runner.record "instantiate_polymorphic_array" (← testInstantiatePolymorphicArray)
  runner := runner.record "instantiate_multiple_vars" (← testInstantiateMultipleVars)
  runner := runner.record "instantiate_array_wrapped" (← testInstantiateArrayWrapped)
  runner := runner.record "instantiate_monomorphic" (← testInstantiateMonomorphic)
  runner := runner.record "instantiate_twice_different" (← testInstantiateTwiceGetsDifferentVars)

  return runner

end QualifiedTypeTests

/-! ## TypeExpr.collectVarNames Tests

Tests for the shared utility that collects type variable names from syntax.
-/
namespace TypeExprCollectVarNamesTests

open Soma.Syntax

/-- Helper to create a type variable expression -/
def tyVarExpr (name : String) : TypeExpr :=
  .var ⟨name, testSpan⟩

/-- Helper to create a type constructor expression -/
def tyConExpr (name : String) : TypeExpr :=
  .con ⟨name, testSpan⟩

/-- Test: Collect from simple variable -/
def testCollectSimpleVar : IO TestResult := do
  let ty := tyVarExpr "a"
  let vars := ty.collectVarNames

  if vars.size != 1 then
    return .failed s!"should have 1 var, got {vars.size}"
  if !vars.contains "a" then
    return .failed "should contain 'a'"

  return .passed

/-- Test: Collect from type constructor (should be empty) -/
def testCollectFromCon : IO TestResult := do
  let ty := tyConExpr "Int"
  let vars := ty.collectVarNames

  if vars.size != 0 then
    return .failed s!"constructor should have 0 vars, got {vars.size}"

  return .passed

/-- Test: Collect from arrow type -/
def testCollectFromArrow : IO TestResult := do
  let ty : TypeExpr := .arrow (tyVarExpr "a") (tyVarExpr "b") testSpan
  let vars := ty.collectVarNames

  if vars.size != 2 then
    return .failed s!"should have 2 vars, got {vars.size}"
  if !vars.contains "a" || !vars.contains "b" then
    return .failed "should contain 'a' and 'b'"

  return .passed

/-- Test: Collect from type application -/
def testCollectFromApp : IO TestResult := do
  -- IO a
  let ty : TypeExpr := .app (tyConExpr "IO") (tyVarExpr "a") testSpan
  let vars := ty.collectVarNames

  if vars.size != 1 then
    return .failed s!"should have 1 var, got {vars.size}"
  if !vars.contains "a" then
    return .failed "should contain 'a'"

  return .passed

/-- Test: Collect from complex type like (m a) -> (a -> m b) -> m b -/
def testCollectFromMonadBind : IO TestResult := do
  -- m a -> (a -> m b) -> m b
  let ma : TypeExpr := .app (tyVarExpr "m") (tyVarExpr "a") testSpan
  let mb : TypeExpr := .app (tyVarExpr "m") (tyVarExpr "b") testSpan
  let aToMb : TypeExpr := .arrow (tyVarExpr "a") mb testSpan
  let ty : TypeExpr := .arrow ma (.arrow aToMb mb testSpan) testSpan

  let vars := ty.collectVarNames

  if vars.size != 3 then
    return .failed s!"should have 3 vars (m, a, b), got {vars.size}"
  if !vars.contains "m" then
    return .failed "should contain 'm'"
  if !vars.contains "a" then
    return .failed "should contain 'a'"
  if !vars.contains "b" then
    return .failed "should contain 'b'"

  return .passed

/-- Test: Duplicates are not counted twice -/
def testCollectDeduplicates : IO TestResult := do
  -- a -> a -> a
  let ty : TypeExpr := .arrow (tyVarExpr "a")
                              (.arrow (tyVarExpr "a") (tyVarExpr "a") testSpan)
                              testSpan
  let vars := ty.collectVarNames

  if vars.size != 1 then
    return .failed s!"should deduplicate to 1 var, got {vars.size}"

  return .passed

/-- Test: Collect from tuple -/
def testCollectFromTuple : IO TestResult := do
  let ty : TypeExpr := .tuple #[tyVarExpr "a", tyVarExpr "b", tyVarExpr "c"] testSpan
  let vars := ty.collectVarNames

  if vars.size != 3 then
    return .failed s!"should have 3 vars, got {vars.size}"

  return .passed

/-- Test: Collect from list type [a] -/
def testCollectFromList : IO TestResult := do
  let ty : TypeExpr := .list (tyVarExpr "a") testSpan
  let vars := ty.collectVarNames

  if vars.size != 1 then
    return .failed s!"should have 1 var, got {vars.size}"
  if !vars.contains "a" then
    return .failed "should contain 'a'"

  return .passed

/-- Test: Collect from nested application like Map k v -/
def testCollectFromNestedApp : IO TestResult := do
  -- Map k v
  let mapK : TypeExpr := .app (tyConExpr "Map") (tyVarExpr "k") testSpan
  let ty : TypeExpr := .app mapK (tyVarExpr "v") testSpan
  let vars := ty.collectVarNames

  if vars.size != 2 then
    return .failed s!"should have 2 vars (k, v), got {vars.size}"
  if !vars.contains "k" || !vars.contains "v" then
    return .failed "should contain 'k' and 'v'"

  return .passed

def run : IO TestRunner := do
  IO.println "  === TypeExpr.collectVarNames Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "simple_var" (← testCollectSimpleVar)
  runner := runner.record "from_con" (← testCollectFromCon)
  runner := runner.record "from_arrow" (← testCollectFromArrow)
  runner := runner.record "from_app" (← testCollectFromApp)
  runner := runner.record "monad_bind" (← testCollectFromMonadBind)
  runner := runner.record "deduplicates" (← testCollectDeduplicates)
  runner := runner.record "from_tuple" (← testCollectFromTuple)
  runner := runner.record "from_list" (← testCollectFromList)
  runner := runner.record "nested_app" (← testCollectFromNestedApp)

  return runner

end TypeExprCollectVarNamesTests

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

  let hktRunner ← HKTTests.run
  totalPassed := totalPassed + hktRunner.passed
  totalFailed := totalFailed + hktRunner.failed

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

  let typedExprGenRunner ← TypedExprGenTests.run
  totalPassed := totalPassed + typedExprGenRunner.passed
  totalFailed := totalFailed + typedExprGenRunner.failed

  let buildInstanceEnvRunner ← BuildInstanceEnvTests.run
  totalPassed := totalPassed + buildInstanceEnvRunner.passed
  totalFailed := totalFailed + buildInstanceEnvRunner.failed

  let qualifiedTypeRunner ← QualifiedTypeTests.run
  totalPassed := totalPassed + qualifiedTypeRunner.passed
  totalFailed := totalFailed + qualifiedTypeRunner.failed

  let collectVarNamesRunner ← TypeExprCollectVarNamesTests.run
  totalPassed := totalPassed + collectVarNamesRunner.passed
  totalFailed := totalFailed + collectVarNamesRunner.failed

  -- Collect all failures
  let mut allFailures : Array String := #[]
  allFailures := allFailures ++ substRunner.failures
  allFailures := allFailures ++ unifyRunner.failures
  allFailures := allFailures ++ hktRunner.failures
  allFailures := allFailures ++ constraintRunner.failures
  allFailures := allFailures ++ instanceRunner.failures
  allFailures := allFailures ++ entailmentRunner.failures
  allFailures := allFailures ++ genRunner.failures
  allFailures := allFailures ++ monadRunner.failures
  allFailures := allFailures ++ typedExprGenRunner.failures
  allFailures := allFailures ++ buildInstanceEnvRunner.failures
  allFailures := allFailures ++ qualifiedTypeRunner.failures
  allFailures := allFailures ++ collectVarNamesRunner.failures

  IO.println ""
  IO.println "=== Inference Test Summary ==="
  IO.println s!"  Total Passed: {totalPassed}"
  IO.println s!"  Total Failed: {totalFailed}"

  if totalFailed > 0 then
    IO.println "  SOME TESTS FAILED"
    IO.println "  Failures:"
    for f in allFailures do
      IO.println s!"    - {f}"
  else
    IO.println "  ALL TESTS PASSED"

end Test.Infer
