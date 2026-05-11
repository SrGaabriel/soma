import Somac.Circuit
import Somac.Circuit.Term
import Somac.Circuit.Node
import Somac.Circuit.Graph
import Somac.Circuit.Pretty
import Soma.Core.Value
import Test.Fixtures

namespace Test.Circuit

open Somac.Circuit.Term (Term Tag Loc Ext Op2Code PrimType)
open Somac.Circuit.Node (Node NodeId PortId PortIdx Wire ActivePair Label)
open Somac.Circuit.Graph (Graph GraphM)
open Somac.Circuit.Pretty (ppGraph ppNode ppTerm)
open Soma.Core (Value)
open Test.Fixtures

/-- Synthetic test placeholder for the kernel-level `Unit` type -/
private def testUnitTy : Value := .vDataType ⟨1004, "test", "Unit"⟩ []

/-- Unit type used for tests where we don't care about the type annotation -/
private def testTy : Value := testUnitTy

namespace TermTests

/-- Test: Tag encoding/decoding roundtrips -/
def testTagRoundtrip : IO TestResult := do
  let tags := [Tag.var, Tag.lam, Tag.app, Tag.dup, Tag.era,
               Tag.ctor, Tag.mat, Tag.record, Tag.proj, Tag.num,
               Tag.op2, Tag.ref, Tag.use]
  for tag in tags do
    let encoded := tag.toUInt8
    match Tag.fromUInt8 encoded with
    | some decoded =>
      if decoded != tag then
        return .failed s!"Tag roundtrip failed for {tag}: got {decoded}"
    | none =>
      return .failed s!"Tag fromUInt8 failed for {tag} (encoded as {encoded})"
  return .passed

/-- Test: Term field accessors -/
def testTermFields : IO TestResult := do
  -- Create a term with known values
  let term := Term.make false Tag.lam (Ext.ofNat 42) 123
  if term.tag != Tag.lam then
    return .failed s!"Expected tag LAM, got {term.tag}"
  if term.ext.val != 42 then
    return .failed s!"Expected ext 42, got {term.ext.val}"
  if term.val != 123 then
    return .failed s!"Expected val 123, got {term.val}"
  if term.isSubstituted then
    return .failed "Term should not be substituted"
  return .passed

/-- Test: Term substitution bit -/
def testSubstitutionBit : IO TestResult := do
  let term := Term.make false Tag.var Ext.zero 100
  if term.isSubstituted then
    return .failed "Fresh term should not be substituted"

  let substituted := term.substitute (Loc.ofNat 200)
  if !substituted.isSubstituted then
    return .failed "Substituted term should have SUB bit set"
  if substituted.loc.val != 200 then
    return .failed s!"Substituted location should be 200, got {substituted.loc.val}"
  return .passed

/-- Test: mkVar creates correct term -/
def testMkVar : IO TestResult := do
  let term := Term.mkVar (Loc.ofNat 42)
  if term.tag != Tag.var then
    return .failed s!"Expected VAR tag, got {term.tag}"
  if term.loc.val != 42 then
    return .failed s!"Expected loc 42, got {term.loc.val}"
  return .passed

/-- Test: mkLam with erasure flag -/
def testMkLam : IO TestResult := do
  let normal := Term.mkLam (Loc.ofNat 10) false
  let erased := Term.mkLam (Loc.ofNat 20) true

  if normal.tag != Tag.lam then
    return .failed "Normal LAM should have LAM tag"
  if normal.isLamErased then
    return .failed "Normal LAM should not be erased"
  if !erased.isLamErased then
    return .failed "Erased LAM should be erased"
  return .passed

/-- Test: mkDup with labels -/
def testDupLabels : IO TestResult := do
  let dup := Term.mkDup 7 (Loc.ofNat 100)

  if dup.tag != Tag.dup then
    return .failed "DUP should have DUP tag"
  if dup.getLabel != 7 then
    return .failed s!"DUP label should be 7, got {dup.getLabel}"
  return .passed

/-- Test: mkCtor encodes tag and arity -/
def testMkCtor : IO TestResult := do
  let ctor := Term.mkCtor 5 3 (Loc.ofNat 100)
  if ctor.tag != Tag.ctor then
    return .failed "CTOR should have CTOR tag"
  if ctor.getCtorTag != 5 then
    return .failed s!"CTOR tag should be 5, got {ctor.getCtorTag}"
  if ctor.getCtorArity != 3 then
    return .failed s!"CTOR arity should be 3, got {ctor.getCtorArity}"
  return .passed

/-- Test: mkNum with primitive types -/
def testMkNum : IO TestResult := do
  let intNum := Term.mkNum PrimType.i64 42
  let boolNum := Term.mkNum PrimType.bool 1

  if intNum.tag != Tag.num then
    return .failed "NUM should have NUM tag"
  match intNum.getNumType with
  | some PrimType.i64 => pure ()
  | other => return .failed s!"Expected I64 type, got {repr other}"
  if intNum.val != 42 then
    return .failed s!"Value should be 42, got {intNum.val}"

  match boolNum.getNumType with
  | some PrimType.bool => pure ()
  | other => return .failed s!"Expected Bool type, got {repr other}"
  return .passed

/-- Test: mkOp2 encodes operation -/
def testMkOp2 : IO TestResult := do
  let addOp := Term.mkOp2 Op2Code.add (Loc.ofNat 50)
  let mulOp := Term.mkOp2 Op2Code.mul (Loc.ofNat 60)

  match addOp.getOp2Code with
  | some Op2Code.add => pure ()
  | other => return .failed s!"Expected ADD op, got {repr other}"

  match mulOp.getOp2Code with
  | some Op2Code.mul => pure ()
  | other => return .failed s!"Expected MUL op, got {repr other}"
  return .passed

/-- Test: isCompound predicate -/
def testIsCompound : IO TestResult := do
  let compound := [Term.mkLam (Loc.ofNat 0) false,
                   Term.mkApp (Loc.ofNat 0),
                   Term.mkDup 0 (Loc.ofNat 0)]
  let immediate := [Term.mkEra, Term.mkNum PrimType.i64 0, Term.mkRef 0]

  for term in compound do
    if !term.isCompound then
      return .failed s!"Term with tag {term.tag} should be compound"

  for term in immediate do
    if term.isCompound then
      return .failed s!"Term with tag {term.tag} should not be compound"
  return .passed

/-- Test: Loc operations -/
def testLocOperations : IO TestResult := do
  let loc := Loc.ofNat 100
  if loc.toNat != 100 then
    return .failed s!"Loc.toNat should be 100, got {loc.toNat}"

  let added := loc.add 50
  if added.toNat != 150 then
    return .failed s!"Loc.add should give 150, got {added.toNat}"

  if !Loc.null.isNull then
    return .failed "Loc.null should be null"
  if loc.isNull then
    return .failed "Non-null loc should not be null"
  return .passed

/-- Test: Ext operations -/
def testExtOperations : IO TestResult := do
  let ext := Ext.ofNat 100
  if ext.toNat != 100 then
    return .failed s!"Ext.toNat should be 100, got {ext.toNat}"

  -- Test erasure flag
  let withErasure := ext.setErased
  if !withErasure.isErased then
    return .failed "setErased should set erasure flag"

  let cleared := withErasure.clearErased
  if cleared.isErased then
    return .failed "clearErased should clear erasure flag"

  -- Test label encoding
  let labeled := Ext.fromLabel 42
  if labeled.label != 42 then
    return .failed s!"Label should be 42, got {labeled.label}"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Term Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "tag_roundtrip" (← testTagRoundtrip)
  runner := runner.record "term_fields" (← testTermFields)
  runner := runner.record "substitution_bit" (← testSubstitutionBit)
  runner := runner.record "mkVar" (← testMkVar)
  runner := runner.record "mkLam" (← testMkLam)
  runner := runner.record "dup_labels" (← testDupLabels)
  runner := runner.record "mkCtor" (← testMkCtor)
  runner := runner.record "mkNum" (← testMkNum)
  runner := runner.record "mkOp2" (← testMkOp2)
  runner := runner.record "isCompound" (← testIsCompound)
  runner := runner.record "loc_operations" (← testLocOperations)
  runner := runner.record "ext_operations" (← testExtOperations)

  return runner

end TermTests

/-! ## Node Tests

  Tests for high-level node types and port configurations.
-/

namespace NodeTests

/-- Test: Node port counts -/
def testPortCounts : IO TestResult := do
  let cases : List (Node × Nat) := [
    (.lam false, 2),   -- var, body
    (.app, 2),         -- fun, arg
    (.dup ⟨0⟩, 2),     -- copy0, copy1
    (.era, 0),         -- no aux ports
    (.ctor 0 3, 3),    -- 3 fields
    (.mat 0, 3),       -- scrutinee, hit, miss
    (.record 4, 4),    -- 4 fields
    (.proj 0, 1),      -- record
    (.num PrimType.i64 0, 0),  -- immediate
    (.op2 Op2Code.add, 2),     -- left, right
    (.ref 0, 0),       -- no aux ports
    (.use, 2)          -- term, continuation
  ]

  for (node, expectedAux) in cases do
    if node.numAuxPorts != expectedAux then
      return .failed s!"Node {node} should have {expectedAux} aux ports, got {node.numAuxPorts}"
    if node.numPorts != expectedAux + 1 then
      return .failed s!"Node {node} should have {expectedAux + 1} total ports"
  return .passed

/-- Test: Node tag conversion -/
def testToTag : IO TestResult := do
  if (Node.lam false).toTag != Tag.lam then
    return .failed "LAM node should have LAM tag"
  if (Node.app).toTag != Tag.app then
    return .failed "APP node should have APP tag"
  if (Node.dup ⟨0⟩).toTag != Tag.dup then
    return .failed "DUP node should have DUP tag"
  if (Node.era).toTag != Tag.era then
    return .failed "ERA node should have ERA tag"
  if (Node.record 2).toTag != Tag.record then
    return .failed "RECORD node should have RECORD tag"
  return .passed

/-- Test: Node isCombinator predicate -/
def testIsCombinator : IO TestResult := do
  let combinators := [Node.lam false, Node.app, Node.dup ⟨0⟩, Node.era]
  let nonCombinators := [Node.ctor 0 1, Node.mat 0, Node.num PrimType.i64 0]

  for node in combinators do
    if !node.isCombinator then
      return .failed s!"Node {node} should be a combinator"

  for node in nonCombinators do
    if node.isCombinator then
      return .failed s!"Node {node} should not be a combinator"
  return .passed

/-- Test: Node isImmediate predicate -/
def testIsImmediate : IO TestResult := do
  let immediates := [Node.num PrimType.i64 42, Node.era, Node.ref 0]
  let nonImmediates := [Node.lam false, Node.app, Node.ctor 0 1]

  for node in immediates do
    if !node.isImmediate then
      return .failed s!"Node {node} should be immediate"

  for node in nonImmediates do
    if node.isImmediate then
      return .failed s!"Node {node} should not be immediate"
  return .passed

/-- Test: NodeId operations -/
def testNodeId : IO TestResult := do
  let n0 := NodeId.zero
  if n0.id != 0 then
    return .failed "NodeId.zero should be 0"

  let n1 := n0.succ
  if n1.id != 1 then
    return .failed "NodeId.succ should increment"
  return .passed

/-- Test: PortIdx operations -/
def testPortIdx : IO TestResult := do
  if !PortIdx.principal.isPrincipal then
    return .failed "Principal port should be principal"
  if PortIdx.aux0.isPrincipal then
    return .failed "Aux0 should not be principal"
  if PortIdx.aux1.isPrincipal then
    return .failed "Aux1 should not be principal"

  if PortIdx.principal.idx != 0 then
    return .failed "Principal should be index 0"
  if PortIdx.aux0.idx != 1 then
    return .failed "Aux0 should be index 1"
  if PortIdx.aux1.idx != 2 then
    return .failed "Aux1 should be index 2"
  return .passed

/-- Test: PortId construction -/
def testPortId : IO TestResult := do
  let node := NodeId.zero
  let principal := PortId.principal node
  let aux0 := PortId.aux node 0
  let aux1 := PortId.aux node 1

  if principal.node != node then
    return .failed "PortId should reference correct node"
  if !principal.port.isPrincipal then
    return .failed "Principal port should be principal"
  if aux0.port.idx != 1 then
    return .failed "Aux 0 should have index 1"
  if aux1.port.idx != 2 then
    return .failed "Aux 1 should have index 2"
  return .passed

/-- Test: Wire construction -/
def testWire : IO TestResult := do
  let p1 := PortId.principal ⟨0⟩
  let p2 := PortId.principal ⟨1⟩
  let wire := Wire.connect p1 p2

  if wire.src != p1 then
    return .failed "Wire src should be p1"
  if wire.dst != p2 then
    return .failed "Wire dst should be p2"
  if !wire.involvesPort p1 then
    return .failed "Wire should involve p1"
  if !wire.involvesPort p2 then
    return .failed "Wire should involve p2"
  if wire.involvesPort (PortId.principal ⟨2⟩) then
    return .failed "Wire should not involve unrelated port"
  return .passed

/-- Test: ActivePair construction -/
def testActivePair : IO TestResult := do
  let n1 : NodeId := ⟨5⟩
  let n2 : NodeId := ⟨3⟩

  -- ActivePair.create should normalize order
  let ap := ActivePair.create n1 n2
  if ap.node1.id != 3 then
    return .failed "ActivePair should have smaller node first"
  if ap.node2.id != 5 then
    return .failed "ActivePair should have larger node second"

  if !ap.contains n1 then
    return .failed "ActivePair should contain n1"
  if !ap.contains n2 then
    return .failed "ActivePair should contain n2"
  if ap.contains ⟨10⟩ then
    return .failed "ActivePair should not contain unrelated node"
  return .passed

/-- Test: Label operations -/
def testLabel : IO TestResult := do
  let l0 := Label.zero
  if l0.toNat != 0 then
    return .failed "Label.zero should be 0"

  let l5 := Label.ofNat 5
  if l5.toNat != 5 then
    return .failed "Label.ofNat 5 should be 5"

  let l6 := l5.succ
  if l6.toNat != 6 then
    return .failed "Label.succ should increment"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Node Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "port_counts" (← testPortCounts)
  runner := runner.record "toTag" (← testToTag)
  runner := runner.record "isCombinator" (← testIsCombinator)
  runner := runner.record "isImmediate" (← testIsImmediate)
  runner := runner.record "nodeId" (← testNodeId)
  runner := runner.record "portIdx" (← testPortIdx)
  runner := runner.record "portId" (← testPortId)
  runner := runner.record "wire" (← testWire)
  runner := runner.record "activePair" (← testActivePair)
  runner := runner.record "label" (← testLabel)

  return runner

end NodeTests

/-! ## Graph Tests

  Tests for graph construction, wiring, and queries.
-/

namespace GraphTests

/-- Test: Empty graph -/
def testEmptyGraph : IO TestResult := do
  let g := Graph.empty
  if g.nodeCount != 0 then
    return .failed s!"Empty graph should have 0 nodes, got {g.nodeCount}"
  if g.nextId != 0 then
    return .failed "Empty graph should have nextId 0"
  if g.nextLabel != 0 then
    return .failed "Empty graph should have nextLabel 0"
  return .passed

/-- Test: Adding nodes -/
def testAddNode : IO TestResult := do
  let g := Graph.empty
  let (n1, g) := g.addNode (.lam false) testTy
  let (n2, g) := g.addNode .app testTy
  let (n3, g) := g.addNode .era testTy

  if n1.id != 0 then
    return .failed "First node should have id 0"
  if n2.id != 1 then
    return .failed "Second node should have id 1"
  if n3.id != 2 then
    return .failed "Third node should have id 2"
  if g.nodeCount != 3 then
    return .failed s!"Graph should have 3 nodes, got {g.nodeCount}"
  return .passed

/-- Test: Node lookup -/
def testNodeLookup : IO TestResult := do
  let g := Graph.empty
  let (n1, g) := g.addNode (.lam false) testTy
  let (n2, g) := g.addNode .app testTy

  match g.getNodeType n1 with
  | some (.lam false) => pure ()
  | other => return .failed s!"Expected LAM node, got {repr other}"

  match g.getNodeType n2 with
  | some .app => pure ()
  | other => return .failed s!"Expected APP node, got {repr other}"

  match g.getNodeType ⟨999⟩ with
  | none => pure ()
  | some _ => return .failed "Lookup of nonexistent node should return none"
  return .passed

/-- Test: Connecting ports -/
def testConnect : IO TestResult := do
  let g := Graph.empty
  let (n1, g) := g.addNode (.lam false) testTy
  let (n2, g) := g.addNode .app testTy

  -- Connect LAM's principal to APP's fun port
  let p1 := PortId.principal n1
  let p2 : PortId := ⟨n2, ⟨1⟩⟩  -- APP's fun port (aux0)
  let g := g.connect p1 p2

  -- Verify connection
  match g.getConnection p1 with
  | some target =>
    if target != p2 then
      return .failed "Connection from p1 should go to p2"
  | none => return .failed "p1 should be connected"

  match g.getConnection p2 with
  | some target =>
    if target != p1 then
      return .failed "Connection from p2 should go to p1"
  | none => return .failed "p2 should be connected"
  return .passed

/-- Test: Fresh labels -/
def testFreshLabels : IO TestResult := do
  let g := Graph.empty
  let (l1, g) := g.freshLabel
  let (l2, g) := g.freshLabel
  let (labels, g) := g.freshLabels 3

  if l1.toNat != 0 then
    return .failed "First label should be 0"
  if l2.toNat != 1 then
    return .failed "Second label should be 1"
  if labels.size != 3 then
    return .failed "Should get 3 labels"
  if labels[0]!.toNat != 2 then
    return .failed "Batch labels should start at 2"
  if g.nextLabel != 5 then
    return .failed s!"nextLabel should be 5, got {g.nextLabel}"
  return .passed

/-- Test: Active pairs detection -/
def testActivePairs : IO TestResult := do
  let g := Graph.empty
  let (n1, g) := g.addNode (.lam false) testTy
  let (n2, g) := g.addNode .app testTy

  -- Before connecting principals: no active pairs
  let pairs1 := g.activePairs
  if !pairs1.isEmpty then
    return .failed "Should have no active pairs before connecting"

  -- Connect principal to principal
  let g := g.connect (PortId.principal n1) (PortId.principal n2)

  let pairs2 := g.activePairs
  if pairs2.length != 1 then
    return .failed s!"Should have 1 active pair, got {pairs2.length}"
  return .passed

/-- Test: Normal form check -/
def testIsNormalForm : IO TestResult := do
  let g := Graph.empty
  if !g.isNormalForm then
    return .failed "Empty graph should be in normal form"

  let (n1, g) := g.addNode (.lam false) testTy
  let (n2, g) := g.addNode .app testTy
  let g := g.connect (PortId.principal n1) (PortId.principal n2)

  if g.isNormalForm then
    return .failed "Graph with active pair should not be in normal form"
  return .passed

/-- Test: Book (definitions) -/
def testBook : IO TestResult := do
  let g := Graph.empty
  let (root, g) := g.addNode (.lam false) testTy
  let funcName : Soma.Core.QualifiedName := ⟨{ id := 0, module := "test", original := "myFunc" }⟩
  let (idx, g) := g.addDefinition funcName root 2 testTy

  if idx != 0 then
    return .failed "First definition should have index 0"

  match g.getDefinition 0 with
  | some def_ =>
    if def_.name != funcName then
      return .failed "Definition name should be 'myFunc'"
    if def_.arity != 2 then
      return .failed "Definition arity should be 2"
    if def_.root != root then
      return .failed "Definition root should match"
  | none => return .failed "Should find definition at index 0"

  match g.findDefinition funcName with
  | some (foundIdx, _) =>
    if foundIdx != 0 then
      return .failed "findDefinition should return index 0"
  | none => return .failed "Should find definition by name"
  return .passed

/-- Test: GraphM monad -/
def testGraphM : IO TestResult := do
  let buildGraph : GraphM NodeId := do
    let n1 ← GraphM.addNode (.lam false) testTy
    let n2 ← GraphM.addNode .app testTy
    GraphM.connect (PortId.principal n1) ⟨n2, ⟨1⟩⟩
    GraphM.setRoot (PortId.principal n2)
    pure n1

  let (result, graph) := GraphM.run' buildGraph

  if result.id != 0 then
    return .failed "Result should be first node (id 0)"
  if graph.nodeCount != 2 then
    return .failed s!"Graph should have 2 nodes, got {graph.nodeCount}"
  if graph.root.node.id != 1 then
    return .failed "Root should be node 1 (the APP)"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Graph Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "empty_graph" (← testEmptyGraph)
  runner := runner.record "add_node" (← testAddNode)
  runner := runner.record "node_lookup" (← testNodeLookup)
  runner := runner.record "connect" (← testConnect)
  runner := runner.record "fresh_labels" (← testFreshLabels)
  runner := runner.record "active_pairs" (← testActivePairs)
  runner := runner.record "is_normal_form" (← testIsNormalForm)
  runner := runner.record "book" (← testBook)
  runner := runner.record "graphM" (← testGraphM)

  return runner

end GraphTests

/-! ## Pretty Printing Tests -/

namespace PrettyTests

/-- Test: ppNode produces non-empty output -/
def testPpNode : IO TestResult := do
  let cfg := Somac.Circuit.Pretty.Config.default
  let nodes := [Node.lam false, Node.lam true, Node.app, Node.era,
                Node.dup ⟨5⟩, Node.ctor 2 3,
                Node.mat 1, Node.record 2, Node.proj 0,
                Node.num PrimType.i64 42, Node.ref 0, Node.use]

  for node in nodes do
    let str := ppNode cfg node
    if str.isEmpty then
      return .failed s!"ppNode should produce non-empty output for {repr node}"
  return .passed

/-- Test: ppNode shows labels for DUP -/
def testPpNodeLabels : IO TestResult := do
  let cfg := { Somac.Circuit.Pretty.Config.default with showLabels := true }
  let dup := ppNode cfg (Node.dup ⟨7⟩)

  if !dup.toSlice.contains "7" then
    return .failed s!"DUP output should contain label 7: got '{dup}'"
  return .passed

/-- Test: ppTerm produces output -/
def testPpTerm : IO TestResult := do
  let terms := [Term.mkVar (Loc.ofNat 10),
                Term.mkLam (Loc.ofNat 20) false,
                Term.mkApp (Loc.ofNat 30),
                Term.mkEra,
                Term.mkNum PrimType.i64 42]

  for term in terms do
    let str := ppTerm term
    if str.isEmpty then
      return .failed s!"ppTerm should produce non-empty output"
  return .passed

/-- Test: ppGraph produces structured output -/
def testPpGraph : IO TestResult := do
  let buildGraph : GraphM Unit := do
    let n1 ← GraphM.addNode (.lam false) testTy
    let n2 ← GraphM.addNode .app testTy
    GraphM.connect (PortId.principal n1) ⟨n2, ⟨1⟩⟩
    GraphM.setRoot (PortId.principal n2)

  let (_, graph) := GraphM.run' buildGraph
  let output := ppGraph Somac.Circuit.Pretty.Config.default graph

  if !output.toSlice.contains "Circuit Graph" then
    return .failed "ppGraph should contain header"
  if !output.toSlice.contains "Root:" then
    return .failed "ppGraph should show root"
  if !output.toSlice.contains "nodes" then
    return .failed "ppGraph should mention nodes"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Pretty Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "ppNode" (← testPpNode)
  runner := runner.record "ppNode_labels" (← testPpNodeLabels)
  runner := runner.record "ppTerm" (← testPpTerm)
  runner := runner.record "ppGraph" (← testPpGraph)

  return runner

end PrettyTests

/-! ## Integration Tests

  Tests that combine multiple components.
-/

namespace IntegrationTests

/-- Test: Build a simple lambda application graph -/
def testLambdaAppGraph : IO TestResult := do
  -- Build: (λx. x) 42
  -- In interaction nets, APP and LAM form an active pair when their
  -- PRINCIPAL ports connect (not when APP's function slot connects to LAM).
  --
  -- APP node ports: [0]=principal (result), [1]=function, [2]=argument
  -- LAM node ports: [0]=principal, [1]=var, [2]=body
  --
  -- Active pair: APP.principal <-> LAM.principal
  let buildGraph : GraphM Unit := do
    -- Create identity lambda
    let lam ← GraphM.addNode (.lam false) testTy
    -- Create application
    let app ← GraphM.addNode .app testTy
    -- Create numeric argument
    let num ← GraphM.addNode (.num PrimType.i64 42) testTy

    -- Wire: APP.principal <-> LAM.principal (THIS creates the active pair)
    GraphM.connect (PortId.principal app) (PortId.principal lam)
    -- Wire: APP.arg -> NUM.principal
    GraphM.connect ⟨app, ⟨2⟩⟩ (PortId.principal num)
    -- Wire: LAM.var -> LAM.body (identity: var connects to body result)
    GraphM.connect ⟨lam, ⟨1⟩⟩ ⟨lam, ⟨2⟩⟩

    -- Root is APP.function port (where result goes after reduction)
    GraphM.setRoot ⟨app, ⟨1⟩⟩

  let (_, graph) := GraphM.run' buildGraph

  if graph.nodeCount != 3 then
    return .failed s!"Should have 3 nodes, got {graph.nodeCount}"

  -- Check for active pair (LAM-APP)
  let pairs := graph.activePairs
  if pairs.length != 1 then
    return .failed s!"Should have 1 active pair (APP-LAM), got {pairs.length}"
  return .passed

/-- Test: Build a DUP chain -/
def testDupChainGraph : IO TestResult := do
  -- Build a chain for duplicating a value 3 times
  let buildGraph : GraphM (Array PortId) := do
    -- Source value (a number)
    let num ← GraphM.addNode (.num PrimType.i64 100) testTy
    let sourcePort := PortId.principal num

    -- Build DUP chain: need 2 DUPs for 3 uses
    let labels ← GraphM.freshLabels 2
    let dup0 ← GraphM.addNode (.dup labels[0]!) testTy
    let dup1 ← GraphM.addNode (.dup labels[1]!) testTy

    -- Wire source to first DUP
    GraphM.connect (PortId.principal dup0) sourcePort
    -- Chain: dup0.aux1 -> dup1.principal
    GraphM.connect ⟨dup0, ⟨2⟩⟩ (PortId.principal dup1)

    -- Return the three use ports
    pure #[⟨dup0, ⟨1⟩⟩, ⟨dup1, ⟨1⟩⟩, ⟨dup1, ⟨2⟩⟩]

  let (usePorts, graph) := GraphM.run' buildGraph

  if usePorts.size != 3 then
    return .failed s!"Should have 3 use ports, got {usePorts.size}"
  if graph.nodeCount != 3 then  -- 1 NUM + 2 DUPs
    return .failed s!"Should have 3 nodes, got {graph.nodeCount}"

  -- Verify labels are distinct
  let labels := graph.usedLabels
  if labels.length != 2 then
    return .failed s!"Should have 2 distinct labels, got {labels.length}"
  return .passed

/-- Test: Constructor and pattern match -/
def testCtorMatchGraph : IO TestResult := do
  -- Build: case (Cons 1 Nil) of Cons x xs -> x
  --
  -- MAT and CTOR form an active pair when their PRINCIPAL ports connect.
  -- MAT node ports: [0]=principal (scrutinee input), [1..]=case branches
  -- CTOR node ports: [0]=principal (value), [1..]=fields
  --
  -- Active pair: MAT.principal <-> CTOR.principal
  let buildGraph : GraphM Unit := do
    -- Create Nil constructor (tag 0, arity 0)
    let nil ← GraphM.addNode (.ctor 0 0) testTy
    -- Create Cons constructor (tag 1, arity 2)
    let cons ← GraphM.addNode (.ctor 1 2) testTy
    -- Create the element "1"
    let elem ← GraphM.addNode (.num PrimType.i64 1) testTy

    -- Wire Cons fields
    GraphM.connect ⟨cons, ⟨1⟩⟩ (PortId.principal elem)
    GraphM.connect ⟨cons, ⟨2⟩⟩ (PortId.principal nil)

    -- Create MAT node for Cons (tag 1)
    let mat ← GraphM.addNode (.mat 1) testTy
    -- Wire: MAT.principal <-> CTOR.principal (THIS creates the active pair)
    GraphM.connect (PortId.principal mat) (PortId.principal cons)

    -- Root is MAT's branch port (where result goes after reduction)
    GraphM.setRoot ⟨mat, ⟨1⟩⟩

  let (_, graph) := GraphM.run' buildGraph

  if graph.nodeCount != 4 then
    return .failed s!"Should have 4 nodes, got {graph.nodeCount}"

  -- Should have active pair: MAT-CTOR
  let pairs := graph.activePairs
  if pairs.length != 1 then
    return .failed s!"Should have 1 active pair (MAT-CTOR), got {pairs.length}"
  return .passed

def run : IO TestRunner := do
  IO.println "  === Integration Tests ==="
  let mut runner := TestRunner.init

  runner := runner.record "lambda_app_graph" (← testLambdaAppGraph)
  runner := runner.record "dup_chain_graph" (← testDupChainGraph)
  runner := runner.record "ctor_match_graph" (← testCtorMatchGraph)

  return runner

end IntegrationTests

/-! ## Main Test Runner -/

def run : IO TestRunner := do
  IO.println "=== Circuit IR Tests ==="
  IO.println ""

  let termRunner ← TermTests.run
  termRunner.printSummary "Term"

  let nodeRunner ← NodeTests.run
  nodeRunner.printSummary "Node"

  let graphRunner ← GraphTests.run
  graphRunner.printSummary "Graph"

  let prettyRunner ← PrettyTests.run
  prettyRunner.printSummary "Pretty"

  let integrationRunner ← IntegrationTests.run
  integrationRunner.printSummary "Integration"

  IO.println ""

  let combined := termRunner.merge nodeRunner
    |>.merge graphRunner
    |>.merge prettyRunner
    |>.merge integrationRunner

  IO.println s!"Total: {combined.passed} passed, {combined.failed} failed"

  if combined.failed > 0 then
    IO.println ""
    IO.println "FAILURES:"
    for f in combined.failures do IO.println s!"  - {f}"

  return combined

end Test.Circuit
