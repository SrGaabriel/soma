import Somac.Alloy
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

namespace ClosureEscapeTests

/-- Takes an `Int32` env, returns the closure's target -/
private def mkTarget (id : Nat) : ClosedFunc :=
  let sig : ClosedSignature :=
    { name := s!"__target_{id}"
    , params := #[{ id := ⟨0⟩, name := "x", ty := .prim .i32 }]
    , retTy := .prim .i32
    }
  { id := ⟨id⟩, sig
  , body := some (CFG.withEntry (Block.entry (.ret (.const (.int 0 .i32)))))
  , nextLocalId := 1
  , localTypes := ({} : Std.HashMap Nat ClosedTy).insert 0 (.prim .i32)
  }

/-- Build a one-block function whose body is the given statement list terminated by the given terminator -/
private def buildCaller (id : Nat) (body : Array ClosedStmt) (term : Terminator)
    (extraLocals : Std.HashMap Nat ClosedTy := {})
    : ClosedFunc :=
  let sig : ClosedSignature :=
    { name := s!"__caller_{id}"
    , params := #[{ id := ⟨0⟩, name := "env", ty := .prim .i32 }]
    , retTy := .prim .i32
    }
  let blk : ClosedBlock :=
    { id := .entry, stmts := body, terminator := term }
  let baseTypes : Std.HashMap Nat ClosedTy :=
    (({} : Std.HashMap Nat ClosedTy).insert 0 (.prim .i32)).insert 1
      (.closure #[.prim .i32] (.prim .i32))
  let mergedTypes := extraLocals.fold (init := baseTypes) (fun acc k v => acc.insert k v)
  { id := ⟨id⟩, sig
  , body := some (CFG.withEntry blk)
  , nextLocalId := 2 + extraLocals.size
  , localTypes := mergedTypes
  }

/-- Count how many `makeClosure` vs `stackClosure` instructions a function has -/
private def closureCounts (f : ClosedFunc) : Nat × Nat := Id.run do
  let mut heap := 0
  let mut stack := 0
  if let some cfg := f.body then
    for block in cfg.allBlocks do
      for stmt in block.stmts do
        match stmt.inst with
        | .makeClosure _ _ | .makeClosurePoly _ _ _ =>
          heap := heap + 1
        | .stackClosure _ _ | .stackClosurePoly _ _ _ =>
          stack := stack + 1
        | _ => pure ()
  (heap, stack)

private def countErases (f : ClosedFunc) : Nat := Id.run do
  let mut n := 0
  if let some cfg := f.body then
    for block in cfg.allBlocks do
      for stmt in block.stmts do
        match stmt.inst with
        | .erase _ _ => n := n + 1
        | _ => pure ()
  n

/-- Build a one-function module for a single caller -/
private def mkModule (caller : ClosedFunc) : Module :=
  let m := Module.empty "test"
  let m := m.addMonoFunc (mkTarget 0)
  let m := m.addMonoFunc caller
  m

/-- A closure that's created, called, then erased -/
def testPromoteSimple : IO TestResult := do
  let body : Array ClosedStmt := #[
    { result := some ⟨1⟩
    , inst := .makeClosure (.local ⟨0⟩) (.local ⟨0⟩) },
    { result := some ⟨2⟩
    , inst := .callClosure (.local ⟨1⟩) #[.local ⟨0⟩] (.prim .i32) },
    { result := none
    , inst := .erase (.local ⟨1⟩) (.closure #[.prim .i32] (.prim .i32)) }
  ]
  let extra : Std.HashMap Nat ClosedTy := ({} : Std.HashMap Nat ClosedTy).insert 2 (.prim .i32)
  let caller := buildCaller 1 body (.ret (.local ⟨2⟩)) extra
  let (m, stats) := ClosureEscape.escapeModule (mkModule caller)
  let caller' := m.getMonoFunc ⟨1⟩ |>.get!
  let (heap, stack) := closureCounts caller'
  let erases := countErases caller'
  if heap != 0 then
    pure (.failed s!"expected 0 makeClosure after promotion, got {heap}")
  else if stack != 1 then
    pure (.failed s!"expected 1 stackClosure after promotion, got {stack}")
  else if erases != 0 then
    pure (.failed s!"expected 0 erases after elision, got {erases}")
  else if stats.promoted != 1 then
    pure (.failed s!"expected stats.promoted=1, got {stats.promoted}")
  else if stats.erasesEliminated != 1 then
    pure (.failed s!"expected stats.erasesEliminated=1, got {stats.erasesEliminated}")
  else
    pure .passed

/-- A closure whose result is returned from the function -/
def testEscapeViaReturn : IO TestResult := do
  let body : Array ClosedStmt := #[
    { result := some ⟨1⟩
    , inst := .makeClosure (.local ⟨0⟩) (.local ⟨0⟩) }
  ]
  let caller := buildCaller 1 body (.ret (.local ⟨1⟩))
  let (m, stats) := ClosureEscape.escapeModule (mkModule caller)
  let caller' := m.getMonoFunc ⟨1⟩ |>.get!
  let (heap, stack) := closureCounts caller'
  if heap != 1 then
    pure (.failed s!"expected closure to remain on heap (1), got heap={heap}")
  else if stack != 0 then
    pure (.failed s!"expected no stack promotion, got stack={stack}")
  else if stats.promoted != 0 then
    pure (.failed s!"expected stats.promoted=0, got {stats.promoted}")
  else
    pure .passed

/-- A closure stored into another closure's env (captured) must not be promoted -/
def testEscapeViaCapture : IO TestResult := do
  let body : Array ClosedStmt := #[
    { result := some ⟨1⟩
    , inst := .makeClosure (.local ⟨0⟩) (.local ⟨0⟩) },
    { result := some ⟨2⟩
    , inst := .makeClosure (.local ⟨0⟩) (.local ⟨1⟩) },
    { result := none
    , inst := .erase (.local ⟨1⟩) (.closure #[.prim .i32] (.prim .i32)) },
    { result := none
    , inst := .erase (.local ⟨2⟩) (.closure #[.prim .i32] (.prim .i32)) }
  ]
  let extra : Std.HashMap Nat ClosedTy := ({} : Std.HashMap Nat ClosedTy).insert 2
    (.closure #[.prim .i32] (.prim .i32))
  let caller := buildCaller 1 body (.ret (.const (.int 0 .i32))) extra
  let (m, stats) := ClosureEscape.escapeModule (mkModule caller)
  let caller' := m.getMonoFunc ⟨1⟩ |>.get!
  let (heap, stack) := closureCounts caller'
  if heap != 1 || stack != 1 then
    pure (.failed s!"expected heap=1, stack=1 (outer %1 escapes, inner %2 promoted), got heap={heap}, stack={stack}")
  else if stats.promoted != 1 then
    pure (.failed s!"expected stats.promoted=1, got {stats.promoted}")
  else
    pure .passed

/-- A closure that's passed as an argument to another call -/
def testEscapeViaCallArg : IO TestResult := do
  let body : Array ClosedStmt := #[
    { result := some ⟨1⟩
    , inst := .makeClosure (.local ⟨0⟩) (.local ⟨0⟩) },
    { result := some ⟨2⟩
    , inst := .call ⟨0⟩ #[.local ⟨1⟩] (.prim .i32) },
    { result := none
    , inst := .erase (.local ⟨1⟩) (.closure #[.prim .i32] (.prim .i32)) }
  ]
  let extra : Std.HashMap Nat ClosedTy := ({} : Std.HashMap Nat ClosedTy).insert 2 (.prim .i32)
  let caller := buildCaller 1 body (.ret (.local ⟨2⟩)) extra
  let (m, _) := ClosureEscape.escapeModule (mkModule caller)
  let caller' := m.getMonoFunc ⟨1⟩ |>.get!
  let (heap, stack) := closureCounts caller'
  if heap != 1 || stack != 0 then
    pure (.failed s!"closure passed as arg must remain on heap; got heap={heap}, stack={stack}")
  else
    pure .passed

/-- A closure that's the CALLEE of callClosure, should be promoted-/
def testInvocationIsSafe : IO TestResult := do
  let body : Array ClosedStmt := #[
    { result := some ⟨1⟩
    , inst := .makeClosure (.local ⟨0⟩) (.local ⟨0⟩) },
    { result := some ⟨2⟩
    , inst := .callClosure (.local ⟨1⟩) #[.local ⟨0⟩] (.prim .i32) },
    { result := none
    , inst := .erase (.local ⟨1⟩) (.closure #[.prim .i32] (.prim .i32)) }
  ]
  let extra : Std.HashMap Nat ClosedTy := ({} : Std.HashMap Nat ClosedTy).insert 2 (.prim .i32)
  let caller := buildCaller 1 body (.ret (.local ⟨2⟩)) extra
  let (m, _) := ClosureEscape.escapeModule (mkModule caller)
  let caller' := m.getMonoFunc ⟨1⟩ |>.get!
  let (heap, stack) := closureCounts caller'
  if heap != 0 || stack != 1 then
    pure (.failed s!"expected promotion (invocation is safe); got heap={heap}, stack={stack}")
  else
    pure .passed

/-- A closure that's both the callee and an argument to the same callClosure is escape -/
def testClosureAsArgToItself : IO TestResult := do
  let body : Array ClosedStmt := #[
    { result := some ⟨1⟩
    , inst := .makeClosure (.local ⟨0⟩) (.local ⟨0⟩) },
    -- this is ill-typed but we're testing the analysis's conservativism
    { result := some ⟨2⟩
    , inst := .callClosure (.local ⟨1⟩) #[.local ⟨1⟩] (.prim .i32) },
    { result := none
    , inst := .erase (.local ⟨1⟩) (.closure #[.prim .i32] (.prim .i32)) }
  ]
  let extra : Std.HashMap Nat ClosedTy := ({} : Std.HashMap Nat ClosedTy).insert 2 (.prim .i32)
  let caller := buildCaller 1 body (.ret (.local ⟨2⟩)) extra
  let (m, _) := ClosureEscape.escapeModule (mkModule caller)
  let caller' := m.getMonoFunc ⟨1⟩ |>.get!
  let (heap, stack) := closureCounts caller'
  if heap != 1 || stack != 0 then
    pure (.failed s!"closure in both callee and arg positions must be heap; got heap={heap}, stack={stack}")
  else
    pure .passed

/-- Each clone counts as a heap copy, but the original is read-only and original is still promotable -/
def testCloneIsSafe : IO TestResult := do
  let body : Array ClosedStmt := #[
    { result := some ⟨1⟩
    , inst := .makeClosure (.local ⟨0⟩) (.local ⟨0⟩) },
    { result := some ⟨2⟩
    , inst := .clone (.local ⟨1⟩) (.closure #[.prim .i32] (.prim .i32)) 0 },
    { result := none
    , inst := .erase (.local ⟨1⟩) (.closure #[.prim .i32] (.prim .i32)) },
    { result := none
    , inst := .erase (.local ⟨2⟩) (.closure #[.prim .i32] (.prim .i32)) }
  ]
  let extra : Std.HashMap Nat ClosedTy := ({} : Std.HashMap Nat ClosedTy).insert 2
    (.closure #[.prim .i32] (.prim .i32))
  let caller := buildCaller 1 body (.ret (.const (.int 0 .i32))) extra
  let (m, _) := ClosureEscape.escapeModule (mkModule caller)
  let caller' := m.getMonoFunc ⟨1⟩ |>.get!
  let (heap, stack) := closureCounts caller'
  if heap != 0 || stack != 1 then
    pure (.failed s!"cloned closure's original should be promoted; got heap={heap}, stack={stack}")
  else
    pure .passed

/-- In empty modules / functions with no closures, pass is a no-op -/
def testNoClosures : IO TestResult := do
  let body : Array ClosedStmt := #[]
  let caller := buildCaller 1 body (.ret (.const (.int 0 .i32)))
  let (_, stats) := ClosureEscape.escapeModule (mkModule caller)
  if stats.promoted != 0 || stats.erasesEliminated != 0 then
    pure (.failed s!"expected no-op stats on closure-free module; got {stats.promoted}/{stats.erasesEliminated}")
  else
    pure .passed

/-- A closure stored into a `lazySup` should escape -/
def testEscapeViaLazySup : IO TestResult := do
  let body : Array ClosedStmt := #[
    { result := some ⟨1⟩
    , inst := .makeClosure (.local ⟨0⟩) (.local ⟨0⟩) },
    { result := some ⟨2⟩
    , inst := .lazySup 0 (.local ⟨1⟩) (.closure #[.prim .i32] (.prim .i32)) }
  ]
  let extra : Std.HashMap Nat ClosedTy := ({} : Std.HashMap Nat ClosedTy).insert 2
    (.closure #[.prim .i32] (.prim .i32))
  let caller := buildCaller 1 body (.ret (.const (.int 0 .i32))) extra
  let (m, _) := ClosureEscape.escapeModule (mkModule caller)
  let caller' := m.getMonoFunc ⟨1⟩ |>.get!
  let (heap, stack) := closureCounts caller'
  if heap != 1 || stack != 0 then
    pure (.failed s!"closure wrapped in lazySup must stay on heap; got heap={heap}, stack={stack}")
  else
    pure .passed

def run : IO TestRunner := do
  IO.println "  === Closure Escape Tests ==="
  let mut runner := TestRunner.init
  runner := runner.record "promote_simple" (← testPromoteSimple)
  runner := runner.record "no_promotion_on_return" (← testEscapeViaReturn)
  runner := runner.record "no_promotion_on_capture" (← testEscapeViaCapture)
  runner := runner.record "no_promotion_on_call_arg" (← testEscapeViaCallArg)
  runner := runner.record "invocation_is_safe" (← testInvocationIsSafe)
  runner := runner.record "closure_as_arg_to_itself_escapes" (← testClosureAsArgToItself)
  runner := runner.record "clone_is_safe" (← testCloneIsSafe)
  runner := runner.record "no_op_on_empty" (← testNoClosures)
  runner := runner.record "no_promotion_on_lazy_sup" (← testEscapeViaLazySup)
  pure runner

end ClosureEscapeTests

def run : IO TestRunner := do
  let mut runner ← TypeTests.run
  let closureRunner ← ClosureEscapeTests.run
  runner := runner.merge closureRunner
  pure runner

end Test.Alloy
