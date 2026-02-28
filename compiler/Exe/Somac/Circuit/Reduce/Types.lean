import Somac.Circuit.Graph
import Somac.Circuit.Node
import Somac.Circuit.Term
import Soma.Core.Value
import Soma.Core.Intrinsic
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Circuit.Reduce

open Somac.Circuit.Graph (Graph GraphM NodeEntry Definition)
open Somac.Circuit.Node (Node NodeId PortId PortIdx Label)
open Somac.Circuit.Term (Tag Op1Code Op2Code PrimType)
open Soma.Core (Value Intrinsic FFIOp RuntimeFn)

/-- Reduction mode: determines how external/effectful operations are handled -/
inductive ReduceMode where
  /-- Partial evaluation: effectful operations are left stuck (compile-time optimization) -/
  | partialEval
  /-- Total evaluation: built-in IO primitives are executed (interpretation) -/
  | totalEval
  deriving Repr, BEq, Inhabited

/-- Classification of why reduction is stuck -/
inductive StuckReason where
  /-- External function with no handler -/
  | externalFunction (name : String) (refId : Nat)
  /-- FFI operation in partial mode -/
  | ffiOp (op : String)
  /-- Runtime function in partial mode -/
  | runtimeFn (fn : String)
  /-- Application of a non-function value -/
  | stuckApplication (fnNodeId : NodeId)
  /-- Pattern match on a non-constructor value -/
  | stuckMatch (scrutNodeId : NodeId)
  /-- Projection on a non-record value -/
  | stuckProjection (recNodeId : NodeId)
  /-- Operator applied to non-numeric operand -/
  | stuckOperator (nodeId : NodeId)
  deriving Repr, Inhabited

instance : ToString StuckReason where
  toString
    | .externalFunction name rid => s!"external function '{name}' (ref {rid})"
    | .ffiOp op => s!"FFI op '{op}'"
    | .runtimeFn fn => s!"runtime fn '{fn}'"
    | .stuckApplication nid => s!"application of non-function at {nid}"
    | .stuckMatch nid => s!"match on non-constructor at {nid}"
    | .stuckProjection nid => s!"projection on non-record at {nid}"
    | .stuckOperator nid => s!"operator on non-number at {nid}"

/-- Errors that can occur during reduction -/
inductive ReduceError where
  /-- Fuel exhausted (possible divergence) -/
  | fuelExhausted (stepsCompleted : Nat)
  /-- Malformed graph (internal invariant violation) -/
  | malformedGraph (msg : String)
  /-- Division by zero -/
  | divisionByZero
  /-- Panic node reached -/
  | panic (msgHash : UInt32) (line : UInt32)
  /-- Irreducible stuck term -/
  | stuck (reason : StuckReason)
  deriving Repr, Inhabited

instance : ToString ReduceError where
  toString
    | .fuelExhausted n => s!"fuel exhausted after {n} steps"
    | .malformedGraph msg => s!"malformed graph: {msg}"
    | .divisionByZero => "division by zero"
    | .panic h l => s!"panic (msg hash {h}, line {l})"
    | .stuck reason => s!"stuck: {reason}"

/-- Reduction statistics, broken down by interaction rule -/
structure Stats where
  /-- Total reduction steps performed -/
  totalSteps : Nat := 0
  /-- Beta reductions (APP-LAM annihilation) -/
  betaReductions : Nat := 0
  /-- DUP-value commutations (DUP-LAM, DUP-CTOR, DUP-RECORD, DUP-NUM, DUP-STRING, DUP-ARRAY) -/
  dupCommutations : Nat := 0
  /-- DUP-SUP annihilations (same label) -/
  dupSupAnnihilations : Nat := 0
  /-- DUP-SUP commutations (different label) -/
  dupSupCommutations : Nat := 0
  /-- DUP-ERA annihilations -/
  dupEraAnnihilations : Nat := 0
  /-- ERA propagations through compound nodes -/
  eraPropagations : Nat := 0
  /-- Pattern match reductions (MAT-CTOR) -/
  matchReductions : Nat := 0
  /-- Field projections (PROJ-RECORD) -/
  projections : Nat := 0
  /-- Arithmetic operations (OP1/OP2-NUM) -/
  arithmeticOps : Nat := 0
  /-- Definition instantiations (ALO expansion) -/
  instantiations : Nat := 0
  /-- Strict evaluation reductions (USE) -/
  useReductions : Nat := 0
  /-- SUP commutations through computation nodes (APP-SUP, OP2-SUP, MAT-SUP, etc.) -/
  supCommutations : Nat := 0
  /-- ERA absorptions at computation nodes (APP-ERA, OP2-ERA, MAT-ERA, etc.) -/
  eraAbsorptions : Nat := 0
  /-- Eta reductions (λx. f x → f) -/
  etaReductions : Nat := 0
  /-- Peak node count observed during reduction -/
  peakNodes : Nat := 0
  /-- Maximum WHNF evaluation stack depth reached -/
  maxStackDepth : Nat := 0
  deriving Repr, Inhabited

namespace Stats

def incBeta (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, betaReductions := s.betaReductions + 1 }

def incDupCommutation (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, dupCommutations := s.dupCommutations + 1 }

def incDupSupAnnihilation (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, dupSupAnnihilations := s.dupSupAnnihilations + 1 }

def incDupSupCommutation (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, dupSupCommutations := s.dupSupCommutations + 1 }

def incDupEraAnnihilation (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, dupEraAnnihilations := s.dupEraAnnihilations + 1 }

def incEraPropagation (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, eraPropagations := s.eraPropagations + 1 }

def incMatch (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, matchReductions := s.matchReductions + 1 }

def incProjection (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, projections := s.projections + 1 }

def incArithmetic (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, arithmeticOps := s.arithmeticOps + 1 }

def incInstantiation (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, instantiations := s.instantiations + 1 }

def incUse (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, useReductions := s.useReductions + 1 }

def incSupCommutation (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, supCommutations := s.supCommutations + 1 }

def incEraAbsorption (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, eraAbsorptions := s.eraAbsorptions + 1 }

def incEta (s : Stats) : Stats :=
  { s with totalSteps := s.totalSteps + 1, etaReductions := s.etaReductions + 1 }

def updatePeakNodes (s : Stats) (n : Nat) : Stats :=
  { s with peakNodes := max s.peakNodes n }

def updateStackDepth (s : Stats) (depth : Nat) : Stats :=
  { s with maxStackDepth := max s.maxStackDepth depth }

/-- Accumulate stats from two passes -/
def merge (a b : Stats) : Stats :=
  { totalSteps         := a.totalSteps + b.totalSteps
    betaReductions     := a.betaReductions + b.betaReductions
    dupCommutations    := a.dupCommutations + b.dupCommutations
    dupSupAnnihilations := a.dupSupAnnihilations + b.dupSupAnnihilations
    dupSupCommutations := a.dupSupCommutations + b.dupSupCommutations
    dupEraAnnihilations := a.dupEraAnnihilations + b.dupEraAnnihilations
    eraPropagations    := a.eraPropagations + b.eraPropagations
    matchReductions    := a.matchReductions + b.matchReductions
    projections        := a.projections + b.projections
    arithmeticOps      := a.arithmeticOps + b.arithmeticOps
    instantiations     := a.instantiations + b.instantiations
    useReductions      := a.useReductions + b.useReductions
    supCommutations    := a.supCommutations + b.supCommutations
    eraAbsorptions     := a.eraAbsorptions + b.eraAbsorptions
    etaReductions      := a.etaReductions + b.etaReductions
    peakNodes          := max a.peakNodes b.peakNodes
    maxStackDepth      := max a.maxStackDepth b.maxStackDepth }

instance : ToString Stats where
  toString s :=
    let lines := #[
      s!"Reduction statistics:",
      s!"  Total steps:           {s.totalSteps}",
      s!"  Beta reductions:       {s.betaReductions}",
      s!"  DUP commutations:      {s.dupCommutations}",
      s!"  DUP-SUP annihilations: {s.dupSupAnnihilations}",
      s!"  DUP-SUP commutations:  {s.dupSupCommutations}",
      s!"  DUP-ERA annihilations: {s.dupEraAnnihilations}",
      s!"  ERA propagations:      {s.eraPropagations}",
      s!"  Match reductions:      {s.matchReductions}",
      s!"  Projections:           {s.projections}",
      s!"  Arithmetic ops:        {s.arithmeticOps}",
      s!"  Instantiations:        {s.instantiations}",
      s!"  USE reductions:        {s.useReductions}",
      s!"  SUP commutations:      {s.supCommutations}",
      s!"  ERA absorptions:       {s.eraAbsorptions}",
      s!"  Eta reductions:        {s.etaReductions}",
      s!"  Peak nodes:            {s.peakNodes}",
      s!"  Max stack depth:       {s.maxStackDepth}"
    ]
    "\n".intercalate lines.toList

end Stats

/-- A continuation frame representing an eliminator awaiting a sub-evaluation -/
inductive WhnfFrame where
  /-- APP: waiting for the function to reach WHNF.
      On apply: fire APP-LAM / APP-SUP / APP-ERA based on the function value. -/
  | appFun (appId : NodeId) (appTy : Value) (demandPort : PortId)
  /-- OP2 phase 1: waiting for the left operand to reach WHNF.
      On apply: if NUM → push `op2Right` for right operand; if SUP/ERA → commute/absorb. -/
  | op2Left (op2Id : NodeId) (op : Op2Code) (op2Ty : Value) (demandPort : PortId)
  /-- OP2 phase 2: left operand resolved to NUM, waiting for right operand.
      On apply: fire OP2-NUM-NUM / OP2-NUM-SUP / OP2-NUM-ERA. -/
  | op2Right (op2Id : NodeId) (op : Op2Code) (op2Ty : Value)
      (leftId : NodeId) (leftPt : PrimType) (leftVal : UInt32) (leftTy : Value)
      (demandPort : PortId)
  /-- OP1: waiting for the operand to reach WHNF.
      On apply: fire OP1-NUM / OP1-SUP / OP1-ERA. -/
  | op1Operand (op1Id : NodeId) (op : Op1Code) (op1Ty : Value) (demandPort : PortId)
  /-- MAT: waiting for the scrutinee to reach WHNF.
      On apply: fire MAT-CTOR / MAT-NUM / MAT-SUP / MAT-ERA. -/
  | matScrutinee (matId : NodeId) (expectedTag : Nat) (matTy : Value) (demandPort : PortId)
  /-- PROJ: waiting for the record/constructor to reach WHNF.
      On apply: fire PROJ-RECORD / PROJ-CTOR / PROJ-SUP / PROJ-ERA. -/
  | projRecord (projId : NodeId) (fieldIdx : Nat) (projTy : Value) (demandPort : PortId)
  /-- DUP: waiting for the value at DUP's principal to reach WHNF.
      On apply: fire DUP-NUM / DUP-ERA / DUP-LAM / DUP-SUP / DUP-DUP / DUP-NOD. -/
  | dupValue (dupId : NodeId) (label : Label) (dupTy : Value) (demandPort : PortId)
  /-- USE: waiting for the term to reach WHNF (strict evaluation).
      On apply: link USE.principal to USE.term, erase continuation. -/
  | useTerm (useId : NodeId) (demandPort : PortId)

/-- Readback values: the result of reducing and reading back a graph -/
inductive ReadbackValue where
  /-- Numeric literal -/
  | num (primType : PrimType) (value : UInt32)
  /-- String value (resolved from string table) -/
  | string (value : String)
  /-- Constructor application with named tag and fields -/
  | ctor (tag : Nat) (fields : Array ReadbackValue)
  /-- Record with field values -/
  | record (fields : Array ReadbackValue)
  /-- Lambda abstraction (irreducible function value) -/
  | lam (erased : Bool)
  /-- Erased/unit value -/
  | erased
  /-- Stuck term that cannot be further reduced -/
  | stuck (reason : StuckReason)
  /-- Superposition node (deferred duplication) -/
  | sup (label : Label) (val0 val1 : ReadbackValue)
  /-- Array value -/
  | array (elemType : PrimType) (elements : Array ReadbackValue)
  deriving Repr, Inhabited

partial def readbackToString : ReadbackValue → String
  | .num .bool v => if v == 1 then "True" else "False"
  | .num pt v => s!"{pt}({v})"
  | .string s => s!"\"{s}\""
  | .ctor tag fields =>
    let fieldsStr := ", ".intercalate (fields.toList.map readbackToString)
    if fields.isEmpty then s!"C{tag}" else s!"C{tag}({fieldsStr})"
  | .record fields =>
    let fieldsStr := ", ".intercalate (fields.toList.map readbackToString)
    s!"\{{fieldsStr}}"
  | .lam erased => if erased then "λ_" else "λ"
  | .erased => "()"
  | .stuck reason => s!"<stuck: {reason}>"
  | .sup label v0 v1 => s!"SUP{label}({readbackToString v0}, {readbackToString v1})"
  | .array et elems =>
    let elemsStr := ", ".intercalate (elems.toList.map readbackToString)
    s!"[{et}| {elemsStr}]"

instance : ToString ReadbackValue := ⟨readbackToString⟩

/-- Determines how external operations behave during reduction
    In partial mode, all handlers return `none` (stuck)
    In total mode, built-in IO primitives are executed -/
structure EffectHandler where
  /-- Handle a runtime function call -/
  handleRuntime : RuntimeFn → Array ReadbackValue → IO (Option ReadbackValue)
  /-- Handle an FFI operation -/
  handleFFI : FFIOp → Array ReadbackValue → IO (Option ReadbackValue)

/-- Effect handler for partial evaluation: all effects are stuck -/
def EffectHandler.allStuck : EffectHandler where
  handleRuntime _ _ := pure none
  handleFFI _ _ := pure none

/-- Handle built-in runtime functions (print, trace) -/
private def builtinHandleRuntime (fn : RuntimeFn) (args : Array ReadbackValue)
    : IO (Option ReadbackValue) := do
  match fn with
  | .printInt =>
    match (args[0]? : Option ReadbackValue) with
    | some (.num _ v) => IO.println s!"{v}"; pure (some .erased)
    | _ => pure none
  | .printStr =>
    match (args[0]? : Option ReadbackValue) with
    | some (.string s) => IO.print s; pure (some .erased)
    | _ => pure none
  | .panic => pure none
  | .trace =>
    match (args[0]? : Option ReadbackValue) with
    | some v => IO.eprintln s!"[trace] {v}"; pure (some .erased)
    | _ => pure none
  | .alloc | .free => pure none

/-- Handle built-in FFI operations (string ops, pureIO) -/
private def builtinHandleFFI (op : FFIOp) (args : Array ReadbackValue)
    : IO (Option ReadbackValue) := do
  match op with
  | .pureIO => pure (args[0]? : Option ReadbackValue)
  | .strcat =>
    match (args[0]? : Option ReadbackValue), (args[1]? : Option ReadbackValue) with
    | some (.string a), some (.string b) => pure (some (.string (a ++ b)))
    | _, _ => pure none
  | .intToString =>
    match (args[0]? : Option ReadbackValue) with
    | some (.num _ v) => pure (some (.string s!"{v}"))
    | _ => pure none
  | .cstringLen =>
    match (args[0]? : Option ReadbackValue) with
    | some (.string s) => pure (some (.num .u64 s.utf8ByteSize.toUInt32))
    | _ => pure none
  | _ => pure none

/-- Effect handler for total evaluation: handles standard IO and string operations -/
def EffectHandler.builtins : EffectHandler where
  handleRuntime := builtinHandleRuntime
  handleFFI := builtinHandleFFI

instance : Inhabited EffectHandler := ⟨.allStuck⟩

/-- Reducer configuration -/
structure Config where
  /-- Maximum reduction steps before giving up -/
  fuel : Nat := 1000000
  /-- Reduction mode -/
  mode : ReduceMode := .partialEval
  /-- Effect handler -/
  effectHandler : EffectHandler := .allStuck
  /-- Intrinsic dispatch table -/
  intrinsics : Std.HashMap String Intrinsic := {}
  deriving Inhabited

/-- Configuration for compile-time partial evaluation -/
def Config.forPartialEval : Config :=
  { mode := .partialEval, effectHandler := .allStuck }

/-- Configuration for full interpretation -/
def Config.forTotalEval : Config :=
  { mode := .totalEval, effectHandler := .builtins }

/-- Reducer state -/
structure ReduceState where
  /-- The interaction net graph -/
  graph : Graph
  /-- Reduction statistics -/
  stats : Stats := {}
  /-- Remaining fuel -/
  fuel : Nat
  /-- Configuration -/
  config : Config
  /-- Definitions currently being normalized by nf (recursion guard) -/
  normalizingDefs : Std.HashSet Nat := {}
  deriving Inhabited

/-- The reduction monad -/
abbrev ReduceM := ExceptT ReduceError (StateT ReduceState IO)

namespace ReduceM

/-- Run a reduction computation -/
def run (m : ReduceM α) (graph : Graph) (config : Config := .forPartialEval)
    : IO (Except ReduceError α × ReduceState) :=
  let state : ReduceState := {
    graph, fuel := config.fuel, config
    stats := { peakNodes := graph.nodeCount }
  }
  StateT.run (ExceptT.run m) state

/-- Get the current graph -/
def getGraph : ReduceM Graph := do return (← get).graph

/-- Set the graph -/
def setGraph (g : Graph) : ReduceM Unit :=
  modify fun s => { s with graph := g }

/-- Modify the graph in place -/
def modifyGraph (f : Graph → Graph) : ReduceM Unit :=
  modify fun s => { s with graph := f s.graph }

/-- Get the statistics -/
def getStats : ReduceM Stats := do return (← get).stats

/-- Modify statistics -/
def modifyStats (f : Stats → Stats) : ReduceM Unit :=
  modify fun s => { s with stats := f s.stats }

/-- Get the configuration -/
def getConfig : ReduceM Config := do return (← get).config

/-- Consume one unit of fuel. Throws if exhausted. -/
def consumeFuel : ReduceM Unit := do
  let s ← get
  if s.fuel == 0 then
    throw (.fuelExhausted s.stats.totalSteps)
  modify fun s => { s with fuel := s.fuel - 1 }

/-- Record current node count for peak tracking -/
def trackPeakNodes : ReduceM Unit := do
  let g ← getGraph
  modifyStats (·.updatePeakNodes g.nodeCount)

/-- Look up a node, throwing on missing -/
def getNode (nid : NodeId) : ReduceM NodeEntry := do
  match (← getGraph).getNode nid with
  | some entry => pure entry
  | none => throw (.malformedGraph s!"node {nid} not found")

/-- Get what a port is connected to -/
def getConnection (p : PortId) : ReduceM (Option PortId) := do
  pure ((← getGraph).getConnection p)

/-- Get connection, throwing on disconnected -/
def follow (p : PortId) : ReduceM PortId := do
  match ← getConnection p with
  | some target => pure target
  | none => throw (.malformedGraph s!"disconnected port {p}")

/-- Add a node to the graph -/
def addNode (n : Node) (ty : Value := Value.vPrimTy .unit) : ReduceM NodeId := do
  let g ← getGraph
  let (nid, g') := g.addNode n ty
  setGraph g'
  pure nid

/-- Connect two ports bidirectionally -/
def connect (p1 p2 : PortId) : ReduceM Unit :=
  modifyGraph (·.connect p1 p2)

/-- Disconnect a port (and its partner) -/
def disconnect (p : PortId) : ReduceM Unit :=
  modifyGraph (·.disconnect p)

/-- Remove a node from the graph -/
def removeNode (nid : NodeId) : ReduceM Unit :=
  modifyGraph (·.removeNode nid)

/-- Allocate a fresh DUP/SUP label -/
def freshLabel : ReduceM Label := do
  let g ← getGraph
  let (label, g') := g.freshLabel
  setGraph g'
  pure label

/-- Link two ports through a consumed node.
    Connects whatever is on the other side of `portA` to whatever is on the other side of `portB`.
    Both ports are disconnected; their external targets are connected to each other. -/
def link (portA portB : PortId) : ReduceM Unit := do
  let targetA ← getConnection portA
  let targetB ← getConnection portB
  disconnect portA
  disconnect portB
  match targetA, targetB with
  | some a, some b => connect a b
  | _, _ => pure ()

/-- Rewire: disconnect `oldPort` from its target and connect `newPort` to that target instead.
    This replaces one endpoint of a wire. Used when inserting a fresh node in place of
    an existing connection (e.g., DUP resolution, arithmetic result). -/
def rewirePort (oldPort newPort : PortId) : ReduceM Unit := do
  match ← getConnection oldPort with
  | some target =>
    disconnect oldPort
    connect newPort target
  | none => pure ()

/-- Look up a definition from the book -/
def getDefinition (refId : Nat) : ReduceM Definition := do
  match (← getGraph).getDefinition refId with
  | some def_ => pure def_
  | none => throw (.malformedGraph s!"definition {refId} not found in book")

/-- Update a definition's root node in the book -/
def updateDefinitionRoot (idx : Nat) (newRoot : NodeId) : ReduceM Unit :=
  modifyGraph (·.updateDefinitionRoot idx newRoot)

/-- Check if a definition is currently being normalized (recursion guard) -/
def isNormalizingDef (refId : Nat) : ReduceM Bool := do
  return (← get).normalizingDefs.contains refId

/-- Mark a definition as currently being normalized -/
def addNormalizingDef (refId : Nat) : ReduceM Unit :=
  modify fun s => { s with normalizingDefs := s.normalizingDefs.insert refId }

/-- Remove a definition from the normalizing set -/
def removeNormalizingDef (refId : Nat) : ReduceM Unit :=
  modify fun s => { s with normalizingDefs := s.normalizingDefs.erase refId }

end ReduceM

end Somac.Circuit.Reduce
