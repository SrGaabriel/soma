/-
  Circuit IR to Alloy IR Lowering

  This pass transforms the interaction net representation (Circuit IR) into
  an imperative SSA representation (Alloy IR). The key transformations are:

  1. Nodes → Instructions: Each Circuit node becomes one or more Alloy instructions
  2. Wires → Values: Port connections become SSA value references
  3. DUP chains → Clone calls: Explicit duplication becomes clone operations
  4. Pattern matching → Switches: MAT chains become switch statements
  5. Closures → Struct + FnPtr: Lambda with captures becomes closure type

  The lowering traverses the Circuit graph starting from the root, generating
  Alloy instructions in evaluation order.
-/

import Soma.Alloy.Func
import Soma.Circuit.Graph
import Soma.Circuit.Node
import Std.Data.HashMap
import Std.Data.HashSet

namespace Soma.Alloy.Lower

open Soma.Alloy

-- Use qualified names for Circuit types to avoid conflicts
abbrev CGraph := Soma.Circuit.Graph.Graph
abbrev CDefinition := Soma.Circuit.Graph.Definition
abbrev CNode := Soma.Circuit.Node.Node
abbrev CNodeId := Soma.Circuit.Node.NodeId
abbrev CPortId := Soma.Circuit.Node.PortId
abbrev CPortIdx := Soma.Circuit.Node.PortIdx
abbrev CLabel := Soma.Circuit.Node.Label
abbrev CNodeEntry := Soma.Circuit.Graph.NodeEntry

open Soma.Circuit.Term (Op1Code Op2Code PrimType Tag)

/-! ## Lowering Context -/

/-- Mapping from Circuit node ports to Alloy local values -/
abbrev PortMap := Std.HashMap (Nat × Nat) LocalId

/-- Lowering state -/
structure LowerState where
  /-- Current function being built -/
  func : Func
  /-- Current block being built -/
  currentBlock : Block
  /-- All completed blocks -/
  blocks : Array Block := #[]
  /-- Port to value mapping -/
  portMap : PortMap := {}
  /-- Next block ID -/
  nextBlockId : Nat := 1
  /-- Circuit function book index to Alloy FuncId -/
  funcMap : Std.HashMap Nat FuncId := {}
  deriving Inhabited

namespace LowerState

/-- Create initial state for a function -/
def init (funcId : FuncId) (sig : Signature) : LowerState :=
  let entry : Block := {
    id := .entry
    terminator := .unreachable  -- Will be replaced
  }
  { func := Func.withBody funcId sig (CFG.withEntry entry)
  , currentBlock := entry
  }

/-- Allocate a fresh local -/
def freshLocal (s : LowerState) : LocalId × LowerState :=
  let (id, func') := s.func.freshLocal
  (id, { s with func := func' })

/-- Allocate a fresh local with type -/
def freshLocalTyped (s : LowerState) (ty : Ty) : LocalId × LowerState :=
  let (id, func') := s.func.freshLocalTyped ty
  (id, { s with func := func' })

/-- Allocate a fresh block ID -/
def freshBlockId (s : LowerState) : BlockId × LowerState :=
  (⟨s.nextBlockId⟩, { s with nextBlockId := s.nextBlockId + 1 })

/-- Add a statement to the current block -/
def emit (s : LowerState) (stmt : Stmt) : LowerState :=
  { s with currentBlock := s.currentBlock.addStmt stmt }

/-- Emit instruction with result -/
def emitWithResult (s : LowerState) (inst : Inst) (ty : Ty) : LocalId × LowerState :=
  let (id, s') := s.freshLocalTyped ty
  let stmt := Stmt.withResult id inst
  (id, s'.emit stmt)

/-- Emit void instruction -/
def emitVoid (s : LowerState) (inst : Inst) : LowerState :=
  s.emit (Stmt.void inst)

/-- Finish current block with a terminator and start a new one -/
def finishBlock (s : LowerState) (term : Terminator) (nextId : BlockId) : LowerState :=
  let finished := s.currentBlock.withTerminator term
  let newBlock : Block := { id := nextId, terminator := .unreachable }
  { s with
    currentBlock := newBlock
    blocks := s.blocks.push finished
  }

/-- Set terminator of current block (for final block) -/
def terminate (s : LowerState) (term : Terminator) : LowerState :=
  { s with currentBlock := s.currentBlock.withTerminator term }

/-- Register a port-to-value mapping -/
def bindPort (s : LowerState) (port : CPortId) (val : LocalId) : LowerState :=
  { s with portMap := s.portMap.insert (port.node.id, port.port.idx) val }

/-- Look up value for a port -/
def lookupPort (s : LowerState) (port : CPortId) : Option LocalId :=
  s.portMap.get? (port.node.id, port.port.idx)

/-- Build the final CFG -/
def finalize (s : LowerState) : Func :=
  let allBlocks := s.blocks.push s.currentBlock
  let cfg : CFG := {
    blocks := allBlocks.foldl (fun m b => m.insert b.id.id b) {}
    entry := .entry
    nextBlockId := s.nextBlockId
  }
  { s.func with body := some cfg }

end LowerState

/-- Lowering monad -/
abbrev LowerM := StateM LowerState

namespace LowerM

def run' (funcId : FuncId) (sig : Signature) (m : LowerM α) : α × Func :=
  let (result, state) := Id.run (StateT.run m (LowerState.init funcId sig))
  (result, state.finalize)

def freshLocal : LowerM LocalId := do
  let s ← get
  let (id, s') := s.freshLocal
  set s'
  pure id

def freshLocalTyped (ty : Ty) : LowerM LocalId := do
  let s ← get
  let (id, s') := s.freshLocalTyped ty
  set s'
  pure id

def freshBlockId : LowerM BlockId := do
  let s ← get
  let (id, s') := s.freshBlockId
  set s'
  pure id

def emit (stmt : Stmt) : LowerM Unit :=
  modify fun s => s.emit stmt

def emitInst (inst : Inst) (ty : Ty) : LowerM LocalId := do
  let s ← get
  let (id, s') := s.emitWithResult inst ty
  set s'
  pure id

def emitVoid (inst : Inst) : LowerM Unit :=
  modify fun s => s.emitVoid inst

def finishBlock (term : Terminator) (nextId : BlockId) : LowerM Unit :=
  modify fun s => s.finishBlock term nextId

def terminate (term : Terminator) : LowerM Unit :=
  modify fun s => s.terminate term

def bindPort (port : CPortId) (val : LocalId) : LowerM Unit :=
  modify fun s => s.bindPort port val

def lookupPort (port : CPortId) : LowerM (Option LocalId) := do
  let s ← get
  pure (s.lookupPort port)

def getPortOrFresh (port : CPortId) (ty : Ty) : LowerM LocalId := do
  match ← lookupPort port with
  | some id => pure id
  | none =>
    let id ← freshLocalTyped ty
    bindPort port id
    pure id

end LowerM

/-! ## Type Conversion -/

/-- Convert Circuit PrimType to Alloy PrimTy -/
def convertPrimType : PrimType → PrimTy
  | .u8 => .u8 | .u16 => .u16 | .u32 => .u32 | .u64 => .u64
  | .i8 => .i8 | .i16 => .i16 | .i32 => .i32 | .i64 => .i64
  | .f32 => .f32 | .f64 => .f64
  | .bool => .bool
  | .char => .u32  -- UTF-32 code point

/-- Convert Circuit Op2Code to Alloy BinOp -/
def convertBinOp : Op2Code → BinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .rem
  | .and => .and | .or => .or | .xor => .xor | .shl => .shl | .shr => .shr
  | .eq => .eq | .ne => .ne | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge

/-- Convert Circuit Op1Code to Alloy UnOp -/
def convertUnOp : Op1Code → UnOp
  | .not => .not
  | .neg => .neg

/-! ## Node Lowering -/

/-- The generic value type used at runtime (tagged pointer or immediate) -/
def valueType : Ty := .prim .i64

/-- Type for constructor tag -/
def tagType : Ty := .prim .u32

/-- Type for closure (fn ptr + env ptr) -/
def closureType : Ty := .struct #[("fn", .rawPtr), ("env", .rawPtr)]

/-- Lower a numeric literal -/
def lowerNum (primTy : PrimType) (val : UInt32) : LowerM LocalId := do
  let ty := Ty.prim (convertPrimType primTy)
  -- Handle signed integer conversion
  let intVal : Int :=
    if primTy.toUInt8 >= 4 && primTy.toUInt8 <= 7 then  -- i8, i16, i32, i64
      let v := val.toNat
      if v >= 0x80000000 then Int.negOfNat (0x100000000 - v) else Int.ofNat v
    else
      Int.ofNat val.toNat
  LowerM.emitInst (.copy (.const (.int intVal (convertPrimType primTy)))) ty

/-- Lower a binary operation -/
def lowerBinOp (op : Op2Code) (lhs rhs : LocalId) : LowerM LocalId := do
  let binOp := convertBinOp op
  let resTy := if binOp.isComparison then Ty.bool else valueType
  LowerM.emitInst (.binOp binOp (.local lhs) (.local rhs) valueType) resTy

/-- Lower a unary operation -/
def lowerUnOp (op : Op1Code) (operand : LocalId) : LowerM LocalId := do
  LowerM.emitInst (.unOp (convertUnOp op) (.local operand)) valueType

/-- Lower a constructor (creates a tagged struct on the heap) -/
def lowerCtor (tag : Nat) (arity : Nat) (fieldVals : Array LocalId) : LowerM LocalId := do
  if arity == 0 then
    -- Nullary constructor: just the tag as an immediate
    LowerM.emitInst (.copy (.const (.int (Int.ofNat tag) .u32))) tagType
  else
    -- Allocate space for tag + fields
    let structSize := 4 + arity * 8  -- 4 bytes tag + 8 bytes per field
    let ptr ← LowerM.emitInst (.malloc (.const (.int (Int.ofNat structSize) .u64))) .rawPtr

    -- Store tag
    let tagPtr ← LowerM.emitInst (.copy (.local ptr)) (.ptr tagType)
    LowerM.emitVoid (.store (.local tagPtr) (.const (.int (Int.ofNat tag) .u32)))

    -- Store fields
    for i in [:arity] do
      if h : i < fieldVals.size then
        let fieldVal := fieldVals[i]
        let offset := 4 + i * 8
        -- Get pointer to field
        let baseAsI64 ← LowerM.emitInst (.unOp (.bitcast (.prim .i64)) (.local ptr)) (.prim .i64)
        let offsetVal ← LowerM.emitInst (.copy (.const (.int (Int.ofNat offset) .i64))) (.prim .i64)
        let fieldAddr ← LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offsetVal) (.prim .i64)) (.prim .i64)
        let fieldPtr ← LowerM.emitInst (.unOp (.bitcast .rawPtr) (.local fieldAddr)) .rawPtr
        LowerM.emitVoid (.store (.local fieldPtr) (.local fieldVal))

    pure ptr

/-- Lower a projection (field access) -/
def lowerProj (fieldIdx : Nat) (record : LocalId) : LowerM LocalId := do
  let offset := 4 + fieldIdx * 8  -- Skip tag, then index into fields
  let baseAsI64 ← LowerM.emitInst (.unOp (.bitcast (.prim .i64)) (.local record)) (.prim .i64)
  let offsetVal ← LowerM.emitInst (.copy (.const (.int (Int.ofNat offset) .i64))) (.prim .i64)
  let fieldAddr ← LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offsetVal) (.prim .i64)) (.prim .i64)
  let fieldPtr ← LowerM.emitInst (.unOp (.bitcast .rawPtr) (.local fieldAddr)) .rawPtr
  LowerM.emitInst (.load (.local fieldPtr) valueType) valueType

/-- Lower tag extraction for pattern matching -/
def lowerGetTag (scrutinee : LocalId) : LowerM LocalId := do
  -- Check if it's a pointer (heap-allocated) or immediate (nullary ctor)
  -- For now, assume heap-allocated and load tag from address
  let tagPtr ← LowerM.emitInst (.unOp (.bitcast (.ptr tagType)) (.local scrutinee)) (.ptr tagType)
  LowerM.emitInst (.load (.local tagPtr) tagType) tagType

/-- Lower a lambda/closure creation -/
def lowerLam (funcId : FuncId) (envVals : Array LocalId) (_erased : Bool) : LowerM LocalId := do
  if envVals.isEmpty then
    -- No captures: just return function pointer as closure with null env
    let nullEnv ← LowerM.emitInst (.copy (.const (.null .rawPtr))) .rawPtr
    LowerM.emitInst (.makeClosure funcId (.local nullEnv)) closureType
  else
    -- Allocate environment struct
    let envSize := envVals.size * 8
    let env ← LowerM.emitInst (.malloc (.const (.int (Int.ofNat envSize) .u64))) .rawPtr

    -- Store captured values
    for i in [:envVals.size] do
      if h : i < envVals.size then
        let capVal := envVals[i]
        let offset := i * 8
        let baseAsI64 ← LowerM.emitInst (.unOp (.bitcast (.prim .i64)) (.local env)) (.prim .i64)
        let offsetVal ← LowerM.emitInst (.copy (.const (.int (Int.ofNat offset) .i64))) (.prim .i64)
        let capAddr ← LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offsetVal) (.prim .i64)) (.prim .i64)
        let capPtr ← LowerM.emitInst (.unOp (.bitcast .rawPtr) (.local capAddr)) .rawPtr
        LowerM.emitVoid (.store (.local capPtr) (.local capVal))

    LowerM.emitInst (.makeClosure funcId (.local env)) closureType

/-- Lower function application -/
def lowerApp (closure : LocalId) (arg : LocalId) : LowerM LocalId := do
  LowerM.emitInst (.callClosure (.local closure) #[.local arg] valueType) valueType

/-- Lower a pattern match (MAT node) -/
def lowerMat (expectedTag : Nat) (scrutinee : LocalId) : LowerM (LocalId × BlockId × BlockId) := do
  let tag ← lowerGetTag scrutinee
  let expected ← LowerM.emitInst (.copy (.const (.int (Int.ofNat expectedTag) .u32))) tagType
  let cond ← LowerM.emitInst (.binOp .eq (.local tag) (.local expected) tagType) Ty.bool

  let thenBlock ← LowerM.freshBlockId
  let elseBlock ← LowerM.freshBlockId

  LowerM.finishBlock (.branch (.local cond) thenBlock elseBlock) thenBlock

  pure (cond, thenBlock, elseBlock)

/-- Lower an array literal -/
def lowerArray (elemTy : PrimType) (elems : Array LocalId) : LowerM LocalId := do
  let len := elems.size
  let elemSize := (convertPrimType elemTy).bitWidth / 8
  let dataSize := len * elemSize

  -- Allocate array struct: { length: u64, data: ptr }
  let arraySize := 8 + 8  -- length + data pointer
  let arrayPtr ← LowerM.emitInst (.malloc (.const (.int (Int.ofNat arraySize) .u64))) .rawPtr

  -- Store length
  let lenVal ← LowerM.emitInst (.copy (.const (.int (Int.ofNat len) .u64))) (.prim .u64)
  LowerM.emitVoid (.store (.local arrayPtr) (.local lenVal))

  -- Allocate data
  let dataPtr ← LowerM.emitInst (.malloc (.const (.int (Int.ofNat dataSize) .u64))) .rawPtr

  -- Store data pointer at offset 8
  let baseAsI64 ← LowerM.emitInst (.unOp (.bitcast (.prim .i64)) (.local arrayPtr)) (.prim .i64)
  let offset8 ← LowerM.emitInst (.copy (.const (.int 8 .i64))) (.prim .i64)
  let dataPtrAddr ← LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offset8) (.prim .i64)) (.prim .i64)
  let dataPtrSlot ← LowerM.emitInst (.unOp (.bitcast .rawPtr) (.local dataPtrAddr)) .rawPtr
  LowerM.emitVoid (.store (.local dataPtrSlot) (.local dataPtr))

  -- Store elements
  for i in [:len] do
    if h : i < elems.size then
      let elem := elems[i]
      let offset := i * elemSize
      let dataAsI64 ← LowerM.emitInst (.unOp (.bitcast (.prim .i64)) (.local dataPtr)) (.prim .i64)
      let offsetVal ← LowerM.emitInst (.copy (.const (.int (Int.ofNat offset) .i64))) (.prim .i64)
      let elemAddr ← LowerM.emitInst (.binOp .add (.local dataAsI64) (.local offsetVal) (.prim .i64)) (.prim .i64)
      let elemPtr ← LowerM.emitInst (.unOp (.bitcast .rawPtr) (.local elemAddr)) .rawPtr
      LowerM.emitVoid (.store (.local elemPtr) (.local elem))

  pure arrayPtr

/-- Lower a string literal -/
def lowerString (len : UInt32) (dataHash : UInt32) : LowerM LocalId := do
  -- String struct: { length: u64, data: ptr }
  let stringSize := 8 + 8
  let stringPtr ← LowerM.emitInst (.malloc (.const (.int (Int.ofNat stringSize) .u64))) .rawPtr

  -- Store length
  let lenVal ← LowerM.emitInst (.copy (.const (.int (Int.ofNat len.toNat) .u64))) (.prim .u64)
  LowerM.emitVoid (.store (.local stringPtr) (.local lenVal))

  -- Store data pointer (using hash as string table index for now)
  let baseAsI64 ← LowerM.emitInst (.unOp (.bitcast (.prim .i64)) (.local stringPtr)) (.prim .i64)
  let offset8 ← LowerM.emitInst (.copy (.const (.int 8 .i64))) (.prim .i64)
  let dataPtrAddr ← LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offset8) (.prim .i64)) (.prim .i64)
  let dataPtrSlot ← LowerM.emitInst (.unOp (.bitcast .rawPtr) (.local dataPtrAddr)) .rawPtr

  -- Use intrinsic to get string data from table
  let dataPtr ← LowerM.emitInst
    (.intrinsic "soma_string_lookup" #[.const (.int (Int.ofNat dataHash.toNat) .u32)] .rawPtr)
    .rawPtr
  LowerM.emitVoid (.store (.local dataPtrSlot) (.local dataPtr))

  pure stringPtr

/-- Lower a panic -/
def lowerPanic (msgIdx : Nat) (line : Nat) : LowerM Unit := do
  LowerM.emitVoid (.panic msgIdx line)
  LowerM.terminate .unreachable

/-- Lower a clone operation (for DUP) -/
def lowerClone (src : LocalId) : LowerM LocalId := do
  LowerM.emitInst (.clone (.local src) valueType) valueType

/-- Lower an erase operation (for ERA) -/
def lowerErase (val : LocalId) : LowerM Unit := do
  LowerM.emitVoid (.erase (.local val) valueType)

/-! ## Graph Traversal -/

/-- Node processing state -/
structure NodeState where
  /-- Nodes already processed -/
  visited : Std.HashSet Nat := {}
  /-- Node results (principal port values) -/
  results : Std.HashMap Nat LocalId := {}
  deriving Inhabited

/-- Lower a single node, returning the value at its principal port -/
partial def lowerNode (graph : CGraph) (nodeId : CNodeId) : StateT NodeState LowerM LocalId := do
  let ns ← get

  -- Check if already processed
  if let some result := ns.results.get? nodeId.id then
    return result

  -- Mark as being processed
  set { ns with visited := ns.visited.insert nodeId.id }

  -- Get the node
  let some entry := graph.getNode nodeId
    | do
      -- Node not found - return undefined
      let undef ← StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
      return undef

  -- Process based on node type
  let result ← match entry.node with
  | .num primTy val => do
    StateT.lift (lowerNum primTy val)

  | .era => do
    -- ERA consumes its input and produces nothing
    -- Find what's connected to the principal port and erase it
    if let some inputPort := entry.getPort ⟨0⟩ then  -- Principal port
      let inputVal ← lowerNode graph inputPort.node
      StateT.lift (lowerErase inputVal)
    StateT.lift (LowerM.emitInst (.copy (.const .unit)) Ty.unit)

  | .lam erased => do
    -- Lambda creates a closure
    -- aux0 = var port, aux1 = body port
    if erased then
      StateT.lift (LowerM.emitInst (.copy (.const .unit)) Ty.unit)
    else
      -- For now, lambdas are lowered separately as functions
      -- This node represents a reference to the closure
      -- We need the lifted function ID and captured values
      StateT.lift (LowerM.emitInst (.copy (.const (.undef closureType))) closureType)

  | .app => do
    -- Application: call closure with argument
    -- aux0 = function, aux1 = argument
    let fnVal ← match entry.getPort ⟨1⟩ with
      | some fnPort => lowerNode graph fnPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef closureType))) closureType)

    let argVal ← match entry.getPort ⟨2⟩ with
      | some argPort => lowerNode graph argPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const .unit)) Ty.unit)

    StateT.lift (lowerApp fnVal argVal)

  | .ctor tag arity => do
    -- Constructor: build tagged struct
    let mut fieldVals : Array LocalId := #[]
    for i in [:arity] do
      let fieldVal ← match entry.getPort ⟨i + 1⟩ with
        | some fieldPort => lowerNode graph fieldPort.node
        | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
      fieldVals := fieldVals.push fieldVal
    StateT.lift (lowerCtor tag arity fieldVals)

  | .proj fieldIdx => do
    -- Projection: extract field from struct
    let recordVal ← match entry.getPort ⟨1⟩ with
      | some recordPort => lowerNode graph recordPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
    StateT.lift (lowerProj fieldIdx recordVal)

  | .record numFields => do
    -- Record: same as ctor with tag 0
    let mut fieldVals : Array LocalId := #[]
    for i in [:numFields] do
      let fieldVal ← match entry.getPort ⟨i + 1⟩ with
        | some fieldPort => lowerNode graph fieldPort.node
        | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
      fieldVals := fieldVals.push fieldVal
    StateT.lift (lowerCtor 0 numFields fieldVals)

  | .mat expectedTag => do
    -- Pattern match: test tag and branch
    let scrutineeVal ← match entry.getPort ⟨1⟩ with
      | some scrutPort => lowerNode graph scrutPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)

    let (_cond, thenBlock, elseBlock) ← StateT.lift (lowerMat expectedTag scrutineeVal)

    -- Lower hit branch
    let hitVal ← match entry.getPort ⟨2⟩ with
      | some hitPort => lowerNode graph hitPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)

    -- Need a join block for phi
    let joinBlock ← StateT.lift LowerM.freshBlockId
    StateT.lift (LowerM.finishBlock (.jump joinBlock) elseBlock)

    -- Lower miss branch
    let missVal ← match entry.getPort ⟨3⟩ with
      | some missPort => lowerNode graph missPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)

    StateT.lift (LowerM.finishBlock (.jump joinBlock) joinBlock)

    -- Phi to merge results
    StateT.lift (LowerM.emitInst
      (.phi #[(Operand.local hitVal, thenBlock), (Operand.local missVal, elseBlock)] valueType)
      valueType)

  | .op1 op => do
    let operandVal ← match entry.getPort ⟨1⟩ with
      | some opPort => lowerNode graph opPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
    StateT.lift (lowerUnOp op operandVal)

  | .op2 op => do
    let lhsVal ← match entry.getPort ⟨1⟩ with
      | some lhsPort => lowerNode graph lhsPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
    let rhsVal ← match entry.getPort ⟨2⟩ with
      | some rhsPort => lowerNode graph rhsPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
    StateT.lift (lowerBinOp op lhsVal rhsVal)

  | .dup _label => do
    -- DUP: clone the input value
    let inputVal ← match entry.getPort ⟨0⟩ with  -- Principal port
      | some inputPort => lowerNode graph inputPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)

    -- Clone for aux0
    let copy0 ← StateT.lift (lowerClone inputVal)
    -- Clone for aux1
    let copy1 ← StateT.lift (lowerClone inputVal)

    -- Bind copies to output ports
    let port0 : CPortId := ⟨nodeId, ⟨1⟩⟩
    let port1 : CPortId := ⟨nodeId, ⟨2⟩⟩
    StateT.lift (LowerM.bindPort port0 copy0)
    StateT.lift (LowerM.bindPort port1 copy1)

    pure inputVal  -- Return original for principal

  | .sup _label => do
    -- SUP: select between alternatives (should be resolved at compile time)
    -- For residual SUPs, emit runtime selection
    StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)

  | .ref refId => do
    -- Global reference: get function from book
    let funcId := FuncId.mk refId
    StateT.lift (LowerM.emitInst (.copy (.func funcId)) (.ptr valueType))

  | .alo refId => do
    -- Allocation/instantiation: call the referenced function
    let funcId := FuncId.mk refId
    StateT.lift (LowerM.emitInst (.call funcId #[] valueType) valueType)

  | .use => do
    -- Strict evaluation: force the term, then continue
    let termVal ← match entry.getPort ⟨1⟩ with
      | some termPort => lowerNode graph termPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
    -- In compiled code, terms are already evaluated (CBV), so this is identity
    pure termVal

  | .array _elemTy => do
    -- Array node: lower length and data
    let _lenVal ← match entry.getPort ⟨1⟩ with
      | some lenPort => lowerNode graph lenPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.int 0 .u64))) (.prim .u64))

    let dataVal ← match entry.getPort ⟨2⟩ with
      | some dataPort => lowerNode graph dataPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.null .rawPtr))) .rawPtr)

    -- For now, return the array pointer directly
    -- A more complete implementation would wrap in struct
    pure dataVal

  | .string => do
    -- String node: extract length and data hash from connected nodes
    -- This is simplified - real implementation needs more context
    StateT.lift (lowerString 0 0)

  | .index => do
    -- Array indexing: load element at runtime index
    let arrayVal ← match entry.getPort ⟨1⟩ with
      | some arrayPort => lowerNode graph arrayPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)

    let indexVal ← match entry.getPort ⟨2⟩ with
      | some indexPort => lowerNode graph indexPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.int 0 .u64))) (.prim .u64))

    -- Get data pointer (at offset 8 in array struct)
    let baseAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.bitcast (.prim .i64)) (.local arrayVal)) (.prim .i64))
    let offset8 ← StateT.lift (LowerM.emitInst (.copy (.const (.int 8 .i64))) (.prim .i64))
    let dataPtrAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offset8) (.prim .i64)) (.prim .i64))
    let dataPtrSlot ← StateT.lift (LowerM.emitInst (.unOp (.bitcast .rawPtr) (.local dataPtrAddr)) .rawPtr)
    let dataPtr ← StateT.lift (LowerM.emitInst (.load (.local dataPtrSlot) .rawPtr) .rawPtr)

    -- Calculate element address
    let elemSize ← StateT.lift (LowerM.emitInst (.copy (.const (.int 8 .i64))) (.prim .i64))
    let offset ← StateT.lift (LowerM.emitInst (.binOp .mul (.local indexVal) (.local elemSize) (.prim .i64)) (.prim .i64))
    let dataAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.bitcast (.prim .i64)) (.local dataPtr)) (.prim .i64))
    let elemAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local dataAsI64) (.local offset) (.prim .i64)) (.prim .i64))
    let elemPtr ← StateT.lift (LowerM.emitInst (.unOp (.bitcast .rawPtr) (.local elemAddr)) .rawPtr)

    StateT.lift (LowerM.emitInst (.load (.local elemPtr) valueType) valueType)

  | .slice => do
    -- Slice: create view without copying
    StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)

  -- Cache result
  modify fun ns => { ns with results := ns.results.insert nodeId.id result }
  pure result

/-! ## Function Lowering -/

/-- Lower a Circuit definition to an Alloy function -/
def lowerDefinition (graph : CGraph) (def_ : CDefinition) (funcId : FuncId) : Func :=
  let sig : Signature := {
    name := def_.name
    params := (List.range def_.arity).toArray.map fun i =>
      { id := ⟨i⟩, name := s!"arg{i}", ty := valueType }
    retTy := valueType
  }

  let (_, func) := LowerM.run' funcId sig do
    -- Lower from root node
    let (result, _) ← StateT.run (lowerNode graph def_.root) {}
    LowerM.terminate (.ret (.local result))

  func

/-! ## Module Lowering -/

/-- Lower an entire Circuit graph to an Alloy module -/
def lowerGraph (graph : CGraph) (moduleName : String := "main") : Module := Id.run do
  let mut module := Module.empty moduleName

  -- Lower each definition in the book
  for i in [:graph.book.size] do
    if let some def_ := graph.book[i]? then
      let funcId := FuncId.mk i
      let func := lowerDefinition graph def_ funcId
      module := module.addFunc func

  -- Set main function if present
  if let some (idx, _) := graph.findDefinition "main" then
    module := module.withMain (FuncId.mk idx)

  module

/-- Main entry point: lower Circuit IR to Alloy IR -/
def lower (graph : CGraph) (moduleName : String := "main") : Module :=
  lowerGraph graph moduleName

end Soma.Alloy.Lower
