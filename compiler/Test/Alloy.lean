import Somac.Alloy.Types
import Test.Fixtures

namespace Test.Alloy

open Somac.Alloy
open Test.Fixtures

namespace TypeTests

def testSupportsLazySupClosure : IO TestResult := do
  let ty : ClosedTy := .closure #[] (.prim .i64)
  if ty.supportsLazySup then
    pure .passed
  else
    pure (.failed "closure types must support lazy SUP duplication")

def testSupportsLazySupStringPtr : IO TestResult := do
  let ty : ClosedTy := Ty.string
  if !ty.supportsLazySup then
    pure .passed
  else
    pure (.failed "string pointer types must not use lazy SUP until clone semantics are implemented")

def testSupportsLazySupTagged : IO TestResult := do
  let ty : ClosedTy := .tagged (.prim .u32) #[]
  if !ty.supportsLazySup then
    pure .passed
  else
    pure (.failed "tagged payload types must not use lazy SUP until type-directed clone is implemented")

def run : IO TestRunner := do
  IO.println "  === Alloy Type Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "supports_lazy_sup_closure" (← testSupportsLazySupClosure)
  runner := runner.record "supports_lazy_sup_string_ptr" (← testSupportsLazySupStringPtr)
  runner := runner.record "supports_lazy_sup_tagged" (← testSupportsLazySupTagged)
  pure runner

end TypeTests

def run : IO TestRunner :=
  TypeTests.run

end Test.Alloy
