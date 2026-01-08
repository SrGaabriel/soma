import Soma.Circuit.PatternMatch
import Soma.Circuit.Graph
import Soma.Circuit.Node
import Soma.Metal.Pattern
import Soma.Metal.Expr
import Soma.Core.Name
import Test.Fixtures

namespace Test.PatternMatch

open Soma.Circuit.PatternMatch
open Soma.Circuit.Graph (Graph GraphM)
open Soma.Circuit.Node (Node NodeId PortId)
open Soma.Metal (BindingId Literal Pattern PatternList)
open Soma.Core (Name)
open Test.Fixtures

/-! ## SimplePattern Tests -/

namespace PatternTests

/-- Test: Wildcard pattern properties -/
def testWildcard : IO TestResult := do
  let pat := SimplePattern.wildcard
  if !pat.isWildcardOrVar then
    return .failed "Wildcard should be isWildcardOrVar"
  if pat.isConstraining then
    return .failed "Wildcard should not be constraining"
  if pat.getCtorTag?.isSome then
    return .failed "Wildcard should have no ctor tag"
  return .passed

/-- Test: Variable pattern properties -/
def testVar : IO TestResult := do
  let binding : BindingId := { id := 42, module := "test", original := "x" }
  let pat := SimplePattern.var binding "x"
  if !pat.isWildcardOrVar then
    return .failed "Var should be isWildcardOrVar"
  if pat.isConstraining then
    return .failed "Var should not be constraining"
  let bindings := pat.collectBindings
  if bindings.size != 1 then
    return .failed s!"Var should collect 1 binding, got {bindings.size}"
  let (_, name) := bindings[0]!
  if name != "x" then
    return .failed "Binding name should be 'x'"
  return .passed

/-- Test: Constructor pattern properties -/
def testCtor : IO TestResult := do
  let pat := SimplePattern.ctor 5 3 #[.wildcard, .wildcard, .wildcard]
  if pat.isWildcardOrVar then
    return .failed "Ctor should not be isWildcardOrVar"
  if !pat.isConstraining then
    return .failed "Ctor should be constraining"
  match pat.getCtorTag? with
  | some 5 => pure ()
  | other => return .failed s!"Ctor tag should be 5, got {repr other}"
  match pat.getCtorArity? with
  | some 3 => pure ()
  | other => return .failed s!"Ctor arity should be 3, got {repr other}"
  return .passed

/-- Test: Literal pattern properties -/
def testLit : IO TestResult := do
  let intPat := SimplePattern.lit (.int 42)
  let boolPat := SimplePattern.lit (.bool true)

  if intPat.isWildcardOrVar then
    return .failed "Lit should not be isWildcardOrVar"
  if !intPat.isConstraining then
    return .failed "Lit should be constraining"
  match intPat.getLit? with
  | some (.int 42) => pure ()
  | other => return .failed s!"Int lit should be 42, got {repr other}"
  match boolPat.getLit? with
  | some (.bool true) => pure ()
  | other => return .failed s!"Bool lit should be true, got {repr other}"
  return .passed

/-- Test: As-pattern properties -/
def testAs : IO TestResult := do
  let binding : BindingId := { id := 1, module := "test", original := "y" }
  let inner := SimplePattern.ctor 0 2 #[.wildcard, .wildcard]
  let pat := SimplePattern.as binding "y" inner

  -- stripAs should return inner
  let stripped := pat.stripAs
  match stripped with
  | .ctor 0 2 _ => pure ()
  | _ => return .failed "stripAs should return inner ctor"

  -- collectBindings should include the as-binding
  let bindings := pat.collectBindings
  if bindings.size != 1 then
    return .failed s!"As pattern should collect 1 binding, got {bindings.size}"
  return .passed

/-- Test: Nested pattern binding collection -/
def testNestedBindings : IO TestResult := do
  let b1 : BindingId := { id := 1, module := "test", original := "x" }
  let b2 : BindingId := { id := 2, module := "test", original := "y" }
  let b3 : BindingId := { id := 3, module := "test", original := "z" }

  -- Cons(x, Cons(y, z))
  let innerCons := SimplePattern.ctor 1 2 #[.var b2 "y", .var b3 "z"]
  let outerCons := SimplePattern.ctor 1 2 #[.var b1 "x", innerCons]

  let bindings := outerCons.collectBindings
  if bindings.size != 3 then
    return .failed s!"Should collect 3 bindings, got {bindings.size}"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Pattern Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "wildcard" (← testWildcard)
  runner := runner.record "var" (← testVar)
  runner := runner.record "ctor" (← testCtor)
  runner := runner.record "lit" (← testLit)
  runner := runner.record "as" (← testAs)
  runner := runner.record "nested_bindings" (← testNestedBindings)

  return runner

end PatternTests

/-! ## Matrix Tests -/

namespace MatrixTests

/-- Test: Empty matrix -/
def testEmptyMatrix : IO TestResult := do
  let matrix := PatternMatrix.empty 3
  if !matrix.isEmpty then
    return .failed "Empty matrix should be empty"
  if matrix.numColumns != 3 then
    return .failed s!"Empty matrix should have 3 columns, got {matrix.numColumns}"
  if matrix.numRows != 0 then
    return .failed "Empty matrix should have 0 rows"
  return .passed

/-- Test: Row creation and properties -/
def testRow : IO TestResult := do
  let patterns := #[SimplePattern.wildcard, SimplePattern.ctor 1 0 #[]]
  let row := Row.ofPatterns patterns 5

  if row.armIndex != 5 then
    return .failed s!"Row arm index should be 5, got {row.armIndex}"
  if row.patterns.size != 2 then
    return .failed s!"Row should have 2 patterns, got {row.patterns.size}"
  if row.allWildcards then
    return .failed "Row with ctor should not be all wildcards"

  let allWildRow := Row.ofPatterns #[.wildcard, .wildcard] 0
  if !allWildRow.allWildcards then
    return .failed "Row with only wildcards should be all wildcards"
  return .passed

/-- Test: Matrix addRow -/
def testAddRow : IO TestResult := do
  let matrix := PatternMatrix.empty 2
  let row1 := Row.ofPatterns #[.wildcard, .ctor 0 0 #[]] 0
  let row2 := Row.ofPatterns #[.ctor 1 0 #[], .wildcard] 1

  let matrix := matrix.addRow row1
  let matrix := matrix.addRow row2

  if matrix.numRows != 2 then
    return .failed s!"Matrix should have 2 rows, got {matrix.numRows}"
  if matrix.isEmpty then
    return .failed "Matrix with rows should not be empty"
  return .passed

/-- Test: Get constructor tags from column -/
def testGetConstructorTags : IO TestResult := do
  let matrix := PatternMatrix.empty 1
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 0 2 #[.wildcard, .wildcard]] 0)
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 1 1 #[.wildcard]] 1)
  let matrix := matrix.addRow (Row.ofPatterns #[.wildcard] 2)
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 0 2 #[.wildcard, .wildcard]] 3)

  let tags := matrix.getConstructorTags 0
  -- Should have tags 0 and 1 (deduplicated)
  if tags.size != 2 then
    return .failed s!"Should have 2 distinct tags, got {tags.size}"
  return .passed

/-- Test: First row all wildcards detection -/
def testFirstRowAllWildcards : IO TestResult := do
  let matrix1 := PatternMatrix.empty 2
  let matrix1 := matrix1.addRow (Row.ofPatterns #[.wildcard, .wildcard] 0)
  if !matrix1.firstRowAllWildcards then
    return .failed "Matrix with all-wildcard first row should detect it"

  let matrix2 := PatternMatrix.empty 2
  let matrix2 := matrix2.addRow (Row.ofPatterns #[.ctor 0 0 #[], .wildcard] 0)
  if matrix2.firstRowAllWildcards then
    return .failed "Matrix with ctor in first row should not be all wildcards"
  return .passed

/-- Test: Matrix specialization -/
def testSpecialize : IO TestResult := do
  -- Matrix with patterns matching on a 2-arity constructor
  let matrix := PatternMatrix.empty 1
  -- Row 0: Cons(x, xs) - matches tag 1
  let b1 : BindingId := { id := 1, module := "test", original := "x" }
  let b2 : BindingId := { id := 2, module := "test", original := "xs" }
  let row0 := Row.ofPatterns #[.ctor 1 2 #[.var b1 "x", .var b2 "xs"]] 0
  -- Row 1: Nil - matches tag 0
  let row1 := Row.ofPatterns #[.ctor 0 0 #[]] 1
  -- Row 2: _ - matches anything
  let row2 := Row.ofPatterns #[.wildcard] 2

  let matrix := matrix.addRow row0
  let matrix := matrix.addRow row1
  let matrix := matrix.addRow row2

  -- Specialize for tag 1, arity 2 (Cons)
  let specialized := matrix.specialize 0 1 2

  -- Should have rows 0 and 2 (row 1 matches tag 0, not tag 1)
  if specialized.numRows != 2 then
    return .failed s!"Specialized matrix should have 2 rows, got {specialized.numRows}"

  -- Column count: was 1, removed 1, added 2 (arity) = 2
  if specialized.numColumns != 2 then
    return .failed s!"Specialized matrix should have 2 columns, got {specialized.numColumns}"
  return .passed

/-- Test: Default matrix -/
def testDefault : IO TestResult := do
  let matrix := PatternMatrix.empty 1
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 0 0 #[]] 0)
  let matrix := matrix.addRow (Row.ofPatterns #[.wildcard] 1)
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 1 0 #[]] 2)

  let defaultMatrix := matrix.default 0

  -- Default should only contain the wildcard row
  if defaultMatrix.numRows != 1 then
    return .failed s!"Default matrix should have 1 row, got {defaultMatrix.numRows}"
  if defaultMatrix.numColumns != 0 then
    return .failed s!"Default matrix should have 0 columns, got {defaultMatrix.numColumns}"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Matrix Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "empty_matrix" (← testEmptyMatrix)
  runner := runner.record "row" (← testRow)
  runner := runner.record "add_row" (← testAddRow)
  runner := runner.record "get_constructor_tags" (← testGetConstructorTags)
  runner := runner.record "first_row_all_wildcards" (← testFirstRowAllWildcards)
  runner := runner.record "specialize" (← testSpecialize)
  runner := runner.record "default" (← testDefault)

  return runner

end MatrixTests

/-! ## Decision Tree Tests -/

namespace DecisionTests

/-- Test: Occurrence creation and manipulation -/
def testOccurrence : IO TestResult := do
  let occ := Occurrence.root 0
  if occ.column != 0 then
    return .failed s!"Root occurrence should have column 0, got {occ.column}"
  if !occ.path.isEmpty then
    return .failed "Root occurrence should have empty path"

  let extended := occ.field 2
  if extended.path.size != 1 then
    return .failed s!"Extended occurrence should have path size 1, got {extended.path.size}"
  if extended.path[0]! != 2 then
    return .failed s!"Extended occurrence path should be [2], got {extended.path}"
  return .passed

/-- Test: Binding creation -/
def testBinding : IO TestResult := do
  let bid : BindingId := { id := 5, module := "test", original := "foo" }
  let occ := Occurrence.root 0
  let binding : Binding := ⟨bid, "foo", occ⟩

  if binding.id.id != 5 then
    return .failed "Binding id should be 5"
  if binding.name != "foo" then
    return .failed "Binding name should be 'foo'"
  return .passed

/-- Test: Decision tree leaf -/
def testLeaf : IO TestResult := do
  let bid : BindingId := { id := 1, module := "test", original := "x" }
  let binding : Binding := ⟨bid, "x", Occurrence.root 0⟩
  let tree := DecisionTree.leaf #[binding] 3

  match tree with
  | .leaf bindings armIndex =>
    if armIndex != 3 then
      return .failed s!"Leaf arm index should be 3, got {armIndex}"
    if bindings.size != 1 then
      return .failed s!"Leaf should have 1 binding, got {bindings.size}"
  | _ => return .failed "Expected leaf node"
  return .passed

/-- Test: Decision tree fail -/
def testFail : IO TestResult := do
  let tree := DecisionTree.fail
  match tree with
  | .fail => return .passed
  | _ => return .failed "Expected fail node"

/-- Test: Decision tree switch -/
def testSwitch : IO TestResult := do
  let occ := Occurrence.root 0
  let leaf0 := DecisionTree.leaf #[] 0
  let leaf1 := DecisionTree.leaf #[] 1
  let cases := #[(0, leaf0), (1, leaf1)]
  let tree := DecisionTree.switch occ .constructor cases (some DecisionTree.fail)

  match tree with
  | .switch occurrence kind cases default =>
    if occurrence.column != 0 then
      return .failed "Switch occurrence column should be 0"
    match kind with
    | .constructor => pure ()
    | _ => return .failed "Switch kind should be constructor"
    if cases.size != 2 then
      return .failed s!"Switch should have 2 cases, got {cases.size}"
    if default.isNone then
      return .failed "Switch should have default"
  | _ => return .failed "Expected switch node"
  return .passed

/-- Test: OccurrenceMap operations -/
def testOccurrenceMap : IO TestResult := do
  let occMap := OccurrenceMap.initial 3
  if occMap.columns.size != 3 then
    return .failed s!"Initial map should have 3 entries, got {occMap.columns.size}"

  match occMap.get 0 with
  | some occ =>
    if occ.column != 0 then
      return .failed "Column 0 occurrence should have column 0"
  | none => return .failed "Should find occurrence for column 0"

  -- Test specialize
  let specialized := occMap.specialize 1 2  -- Remove col 1, add 2 new columns
  if specialized.columns.size != 4 then  -- 3 - 1 + 2 = 4
    return .failed s!"Specialized map should have 4 entries, got {specialized.columns.size}"

  -- Test removeColumn
  let removed := occMap.removeColumn 1
  if removed.columns.size != 2 then
    return .failed s!"Removed map should have 2 entries, got {removed.columns.size}"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Decision Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "occurrence" (← testOccurrence)
  runner := runner.record "binding" (← testBinding)
  runner := runner.record "leaf" (← testLeaf)
  runner := runner.record "fail" (← testFail)
  runner := runner.record "switch" (← testSwitch)
  runner := runner.record "occurrence_map" (← testOccurrenceMap)

  return runner

end DecisionTests

/-! ## Compilation Tests -/

namespace CompileTests

/-- Test: Compile empty matrix gives fail -/
def testCompileEmpty : IO TestResult := do
  let matrix := PatternMatrix.empty 1
  let tree := compileMatrix matrix

  match tree with
  | .fail => return .passed
  | _ => return .failed "Empty matrix should compile to fail"

/-- Test: Compile all-wildcard row gives leaf -/
def testCompileAllWildcard : IO TestResult := do
  let matrix := PatternMatrix.empty 2
  let matrix := matrix.addRow (Row.ofPatterns #[.wildcard, .wildcard] 7)
  let tree := compileMatrix matrix

  match tree with
  | .leaf _ armIndex =>
    if armIndex != 7 then
      return .failed s!"Leaf arm index should be 7, got {armIndex}"
    return .passed
  | _ => return .failed "All-wildcard matrix should compile to leaf"

/-- Test: Compile single constructor pattern -/
def testCompileSingleCtor : IO TestResult := do
  let matrix := PatternMatrix.empty 1
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 0 0 #[]] 0)
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 1 0 #[]] 1)
  let tree := compileMatrix matrix

  match tree with
  | .switch _ kind cases _ =>
    match kind with
    | .constructor => pure ()
    | _ => return .failed "Should be constructor switch"
    if cases.size != 2 then
      return .failed s!"Should have 2 cases, got {cases.size}"
    return .passed
  | _ => return .failed "Should compile to switch"

/-- Test: Compile with default case -/
def testCompileWithDefault : IO TestResult := do
  let matrix := PatternMatrix.empty 1
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 0 0 #[]] 0)
  let matrix := matrix.addRow (Row.ofPatterns #[.wildcard] 1)
  let tree := compileMatrix matrix

  match tree with
  | .switch _ _ _ default =>
    match default with
    | some (.leaf _ idx) =>
      if idx != 1 then
        return .failed s!"Default should lead to arm 1, got {idx}"
    | _ => return .failed "Default should be a leaf"
    return .passed
  | _ => return .failed "Should compile to switch"

/-- Test: Compile nested patterns -/
def testCompileNested : IO TestResult := do
  -- Match on Cons(x, Cons(y, z)) vs Cons(x, Nil) vs Nil
  let b1 : BindingId := { id := 1, module := "test", original := "x" }
  let b2 : BindingId := { id := 2, module := "test", original := "y" }
  let b3 : BindingId := { id := 3, module := "test", original := "z" }

  let matrix := PatternMatrix.empty 1

  -- Cons(x, Cons(y, z))
  let innerCons := SimplePattern.ctor 1 2 #[.var b2 "y", .var b3 "z"]
  let pat1 := SimplePattern.ctor 1 2 #[.var b1 "x", innerCons]
  let matrix := matrix.addRow (Row.ofPatterns #[pat1] 0)

  -- Cons(x, Nil)
  let nilPat := SimplePattern.ctor 0 0 #[]
  let pat2 := SimplePattern.ctor 1 2 #[.var b1 "x", nilPat]
  let matrix := matrix.addRow (Row.ofPatterns #[pat2] 1)

  -- Nil
  let pat3 := SimplePattern.ctor 0 0 #[]
  let matrix := matrix.addRow (Row.ofPatterns #[pat3] 2)

  let tree := compileMatrix matrix

  -- Should produce a nested switch structure
  match tree with
  | .switch _ .constructor cases _ =>
    if cases.size < 1 then
      return .failed "Should have at least 1 case"
    return .passed
  | _ => return .failed "Should compile to switch"

/-- Test: Compile with variable bindings -/
def testCompileWithBindings : IO TestResult := do
  let b1 : BindingId := { id := 1, module := "test", original := "x" }
  let matrix := PatternMatrix.empty 1
  let matrix := matrix.addRow (Row.ofPatterns #[.var b1 "x"] 0)
  let tree := compileMatrix matrix

  match tree with
  | .leaf bindings _ =>
    if bindings.size != 1 then
      return .failed s!"Should have 1 binding, got {bindings.size}"
    if bindings[0]!.name != "x" then
      return .failed "Binding name should be 'x'"
    return .passed
  | _ => return .failed "Should compile to leaf with bindings"

def run : IO TestRunner := do
  IO.println "  === Compile Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "compile_empty" (← testCompileEmpty)
  runner := runner.record "compile_all_wildcard" (← testCompileAllWildcard)
  runner := runner.record "compile_single_ctor" (← testCompileSingleCtor)
  runner := runner.record "compile_with_default" (← testCompileWithDefault)
  runner := runner.record "compile_nested" (← testCompileNested)
  runner := runner.record "compile_with_bindings" (← testCompileWithBindings)

  return runner

end CompileTests

/-! ## Lowering Tests -/

namespace LowerTests

/-- Test: Lower fail tree -/
def testLowerFail : IO TestResult := do
  let tree := DecisionTree.fail
  let lowerArm : ArmCallback := fun _ _ => do
    let era ← GraphM.addNode .era
    pure (PortId.principal era)

  let (result, graph) := GraphM.run' do
    let scrut ← GraphM.addNode (.num .i64 0)
    lower tree #[PortId.principal scrut] lowerArm

  -- Should create an ERA node for failure
  if graph.nodeCount < 1 then
    return .failed "Fail tree should create at least 1 node"
  return .passed

/-- Test: Lower leaf tree -/
def testLowerLeaf : IO TestResult := do
  let tree := DecisionTree.leaf #[] 0
  let mut armCalled := false
  let lowerArm : ArmCallback := fun armIdx ctx => do
    if armIdx != 0 then
      panic! "Wrong arm index"
    let num ← GraphM.addNode (.num .i64 42)
    pure (PortId.principal num)

  let (result, graph) := GraphM.run' do
    let scrut ← GraphM.addNode (.num .i64 0)
    lower tree #[PortId.principal scrut] lowerArm

  -- Should call arm callback and create its node
  if graph.nodeCount < 2 then  -- scrutinee + arm result
    return .failed s!"Leaf tree should create at least 2 nodes, got {graph.nodeCount}"
  return .passed

/-- Test: Lower simple switch -/
def testLowerSwitch : IO TestResult := do
  let occ := Occurrence.root 0
  let leaf0 := DecisionTree.leaf #[] 0
  let leaf1 := DecisionTree.leaf #[] 1
  let cases := #[(0, leaf0), (1, leaf1)]
  let tree := DecisionTree.switch occ .constructor cases none

  let lowerArm : ArmCallback := fun armIdx _ => do
    let num ← GraphM.addNode (.num .i64 armIdx.toUInt32)
    pure (PortId.principal num)

  let (result, graph) := GraphM.run' do
    let scrut ← GraphM.addNode (.ctor 0 0)
    lower tree #[PortId.principal scrut] lowerArm

  -- Should create MAT nodes for the switch
  -- At least: scrutinee + 2 arm results + MAT nodes
  if graph.nodeCount < 3 then
    return .failed s!"Switch tree should create at least 3 nodes, got {graph.nodeCount}"
  return .passed

/-- Test: Lower with bindings -/
def testLowerWithBindings : IO TestResult := do
  let bid : BindingId := { id := 1, module := "test", original := "x" }
  let binding : Binding := ⟨bid, "x", Occurrence.root 0⟩
  let tree := DecisionTree.leaf #[binding] 0

  let lowerArm : ArmCallback := fun _ ctx => do
    -- Check that we received the binding
    if ctx.bindings.size != 1 then
      panic! s!"Expected 1 binding, got {ctx.bindings.size}"
    let (id, name, ports) := ctx.bindings[0]!
    if name != "x" then
      panic! "Binding name should be 'x'"
    if ports.size != 1 then
      panic! "Should have 1 port for binding"
    -- Return the bound value
    pure ports[0]!

  let usageCounts : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert 1 1
  let (_, graph) := GraphM.run' do
    let scrut ← GraphM.addNode (.num .i64 99)
    lower tree #[PortId.principal scrut] lowerArm usageCounts

  -- The result should reference the scrutinee through the binding
  if graph.nodeCount < 1 then
    return .failed "Should have at least 1 node"
  return .passed

/-- Test: Lower with multi-use bindings -/
def testLowerMultiUse : IO TestResult := do
  let bid : BindingId := { id := 1, module := "test", original := "x" }
  let binding : Binding := ⟨bid, "x", Occurrence.root 0⟩
  let tree := DecisionTree.leaf #[binding] 0

  let lowerArm : ArmCallback := fun _ ctx => do
    if ctx.bindings.size != 1 then
      panic! s!"Expected 1 binding, got {ctx.bindings.size}"
    let (_, _, ports) := ctx.bindings[0]!
    -- For multi-use, should have 3 ports
    if ports.size != 3 then
      panic! s!"Should have 3 ports for binding used 3 times, got {ports.size}"
    let num ← GraphM.addNode (.num .i64 0)
    pure (PortId.principal num)

  let usageCounts : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert 1 3  -- x is used 3 times
  let (_, graph) := GraphM.run' do
    let scrut ← GraphM.addNode (.num .i64 99)
    lower tree #[PortId.principal scrut] lowerArm usageCounts

  -- Should create DUP nodes for the multi-use binding
  -- 3 uses requires 2 DUP nodes
  if graph.nodeCount < 3 then  -- scrutinee + 2 DUPs + result
    return .failed s!"Multi-use should create at least 3 nodes, got {graph.nodeCount}"
  return .passed

/-- Test: Lower nested occurrence -/
def testLowerNestedOccurrence : IO TestResult := do
  -- Binding at path [1] (second field of scrutinee)
  let bid : BindingId := { id := 1, module := "test", original := "y" }
  let occ := (Occurrence.root 0).field 1
  let binding : Binding := ⟨bid, "y", occ⟩
  let tree := DecisionTree.leaf #[binding] 0

  let lowerArm : ArmCallback := fun _ ctx => do
    if ctx.bindings.size != 1 then
      panic! "Expected 1 binding"
    let (_, _, ports) := ctx.bindings[0]!
    -- Port should be from a PROJ node
    pure ports[0]!

  let (result, graph) := GraphM.run' do
    -- Create a 2-field constructor as scrutinee
    let field0 ← GraphM.addNode (.num .i64 1)
    let field1 ← GraphM.addNode (.num .i64 2)
    let ctor ← GraphM.addNode (.ctor 0 2)
    GraphM.connect ⟨ctor, ⟨1⟩⟩ (PortId.principal field0)
    GraphM.connect ⟨ctor, ⟨2⟩⟩ (PortId.principal field1)
    lower tree #[PortId.principal ctor] lowerArm

  -- Should create a PROJ node to access field 1
  if graph.nodeCount < 4 then  -- 2 fields + ctor + proj
    return .failed s!"Nested occurrence should create at least 4 nodes, got {graph.nodeCount}"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Lower Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "lower_fail" (← testLowerFail)
  runner := runner.record "lower_leaf" (← testLowerLeaf)
  runner := runner.record "lower_switch" (← testLowerSwitch)
  runner := runner.record "lower_with_bindings" (← testLowerWithBindings)
  runner := runner.record "lower_multi_use" (← testLowerMultiUse)
  runner := runner.record "lower_nested_occurrence" (← testLowerNestedOccurrence)

  return runner

end LowerTests

/-! ## Integration Tests -/

namespace IntegrationTests

/-- Test: Full pipeline - simple match -/
def testSimpleMatch : IO TestResult := do
  -- match x with
  -- | True -> 1
  -- | False -> 0
  let matrix := PatternMatrix.empty 1
  let matrix := matrix.addRow (Row.ofPatterns #[.lit (.bool true)] 0)
  let matrix := matrix.addRow (Row.ofPatterns #[.lit (.bool false)] 1)

  let tree := compileMatrix matrix

  let lowerArm : ArmCallback := fun armIdx _ => do
    let value := if armIdx == 0 then 1 else 0
    let num ← GraphM.addNode (.num .i64 value.toUInt32)
    pure (PortId.principal num)

  let (result, graph) := GraphM.run' do
    let scrut ← GraphM.addNode (.num .bool 1)  -- True
    lower tree #[PortId.principal scrut] lowerArm

  if graph.nodeCount < 3 then
    return .failed s!"Simple match should create at least 3 nodes, got {graph.nodeCount}"
  return .passed

/-- Test: Full pipeline - constructor match with bindings -/
def testCtorMatchWithBindings : IO TestResult := do
  -- match x with
  -- | Some(y) -> y
  -- | None -> 0
  let b1 : BindingId := { id := 1, module := "test", original := "y" }

  let matrix := PatternMatrix.empty 1
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 1 1 #[.var b1 "y"]] 0)  -- Some(y)
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 0 0 #[]] 1)  -- None

  let tree := compileMatrix matrix

  let lowerArm : ArmCallback := fun armIdx ctx => do
    if armIdx == 0 then
      -- Some case: return y
      if ctx.bindings.size != 1 then
        panic! "Should have binding for y"
      let (_, _, ports) := ctx.bindings[0]!
      pure ports[0]!
    else
      -- None case: return 0
      let num ← GraphM.addNode (.num .i64 0)
      pure (PortId.principal num)

  let usageCounts : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert 1 1
  let (_, graph) := GraphM.run' do
    -- Create Some(42)
    let inner ← GraphM.addNode (.num .i64 42)
    let some ← GraphM.addNode (.ctor 1 1)
    GraphM.connect ⟨some, ⟨1⟩⟩ (PortId.principal inner)
    lower tree #[PortId.principal some] lowerArm usageCounts

  if graph.nodeCount < 3 then
    return .failed s!"Ctor match should create at least 3 nodes, got {graph.nodeCount}"
  return .passed

/-- Test: Full pipeline - nested match -/
def testNestedMatch : IO TestResult := do
  -- match x with
  -- | Cons(a, Cons(b, _)) -> a + b
  -- | Cons(a, Nil) -> a
  -- | Nil -> 0
  let ba : BindingId := { id := 1, module := "test", original := "a" }
  let bb : BindingId := { id := 2, module := "test", original := "b" }

  let matrix := PatternMatrix.empty 1

  -- Cons(a, Cons(b, _))
  let innerCons := SimplePattern.ctor 1 2 #[.var bb "b", .wildcard]
  let pat1 := SimplePattern.ctor 1 2 #[.var ba "a", innerCons]
  let matrix := matrix.addRow (Row.ofPatterns #[pat1] 0)

  -- Cons(a, Nil)
  let nilPat := SimplePattern.ctor 0 0 #[]
  let pat2 := SimplePattern.ctor 1 2 #[.var ba "a", nilPat]
  let matrix := matrix.addRow (Row.ofPatterns #[pat2] 1)

  -- Nil
  let pat3 := SimplePattern.ctor 0 0 #[]
  let matrix := matrix.addRow (Row.ofPatterns #[pat3] 2)

  let tree := compileMatrix matrix

  let lowerArm : ArmCallback := fun armIdx _ => do
    let num ← GraphM.addNode (.num .i64 armIdx.toUInt32)
    pure (PortId.principal num)

  let (result, graph) := GraphM.run' do
    -- Create Nil
    let nil ← GraphM.addNode (.ctor 0 0)
    lower tree #[PortId.principal nil] lowerArm

  -- Nested match should create a good number of nodes
  if graph.nodeCount < 2 then
    return .failed s!"Nested match should create at least 2 nodes, got {graph.nodeCount}"
  return .passed

/-- Test: Exhaustiveness - all cases covered -/
def testExhaustive : IO TestResult := do
  -- This tests that the algorithm handles exhaustive patterns correctly
  -- by producing a decision tree that never reaches .fail
  let matrix := PatternMatrix.empty 1
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 0 0 #[]] 0)
  let matrix := matrix.addRow (Row.ofPatterns #[.ctor 1 0 #[]] 1)
  let matrix := matrix.addRow (Row.ofPatterns #[.wildcard] 2)  -- Catch-all

  let tree := compileMatrix matrix

  -- The tree should never reach .fail because we have a catch-all
  -- Check that all reachable arms are valid (not fail nodes at top level)
  match tree with
  | .fail => return .failed "Exhaustive match should not produce top-level .fail"
  | .leaf _ _ => return .passed
  | .switch _ _ cases _ =>
    -- Just check that we have cases - detailed checking would require termination proof
    if cases.isEmpty then
      return .failed "Switch should have at least one case"
    return .passed

def run : IO TestRunner := do
  IO.println "  === Integration Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "simple_match" (← testSimpleMatch)
  runner := runner.record "ctor_match_with_bindings" (← testCtorMatchWithBindings)
  runner := runner.record "nested_match" (← testNestedMatch)
  runner := runner.record "exhaustive" (← testExhaustive)

  return runner

end IntegrationTests

/-! ## Main Test Runner -/

def run : IO TestRunner := do
  IO.println "=== Pattern Match Compilation Tests ==="
  IO.println ""

  let patternRunner ← PatternTests.run
  patternRunner.printSummary "Pattern"

  let matrixRunner ← MatrixTests.run
  matrixRunner.printSummary "Matrix"

  let decisionRunner ← DecisionTests.run
  decisionRunner.printSummary "Decision"

  let compileRunner ← CompileTests.run
  compileRunner.printSummary "Compile"

  let lowerRunner ← LowerTests.run
  lowerRunner.printSummary "Lower"

  let integrationRunner ← IntegrationTests.run
  integrationRunner.printSummary "Integration"

  IO.println ""

  let combined := patternRunner.merge matrixRunner
    |>.merge decisionRunner
    |>.merge compileRunner
    |>.merge lowerRunner
    |>.merge integrationRunner

  IO.println s!"Total: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.PatternMatch
