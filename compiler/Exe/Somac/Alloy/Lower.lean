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

import Somac.Alloy.Func
import Somac.Circuit.Graph
import Somac.Circuit.Node
import Soma.Core.Value
import Soma.Core.Primitive
import Std.Data.HashMap
import Std.Data.HashSet

namespace Somac.Alloy.Lower

open Somac.Alloy

abbrev CGraph := Somac.Circuit.Graph.Graph
abbrev CDefinition := Somac.Circuit.Graph.Definition
abbrev CNode := Somac.Circuit.Node.Node
abbrev CNodeId := Somac.Circuit.Node.NodeId
abbrev CPortId := Somac.Circuit.Node.PortId
abbrev CPortIdx := Somac.Circuit.Node.PortIdx
abbrev CLabel := Somac.Circuit.Node.Label
abbrev CNodeEntry := Somac.Circuit.Graph.NodeEntry

open Somac.Circuit.Term (Op1Code Op2Code PrimType Tag)

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

open Soma.Core (Value StarPrimitive HigherPrimitive)

/-- Convert a StarPrimitive to Alloy PrimTy -/
def convertStarPrimitive : StarPrimitive → PrimTy
  | .int => .i32
  | .long => .i64
  | .short => .i16
  | .byte => .i8
  | .float => .f32
  | .double => .f64
  | .bool => .bool
  | .string => .i64 -- String is a pointer
  | .unit => .unit
  | .closurePtr => .i64 -- Closure pointer
  | .int8 => .i8
  | .int16 => .i16
  | .int32 => .i32
  | .int64 => .i64
  | .word8 => .u8
  | .word16 => .u16
  | .word32 => .u32
  | .word64 => .u64

/-- Convert a HigherPrimitive to Alloy Ty -/
def convertHigherPrimitive : HigherPrimitive → Ty
  | .array => .rawPtr
  | .list => .rawPtr
  | .ref => .rawPtr
  | .io => .prim .i64
  | .ptr => .rawPtr

/-- Convert a Soma Value type to an Alloy Ty -/
partial def convertValueType : Value → Ty
  -- Primitive types
  | Value.vPrimTy prim => .prim (convertStarPrimitive prim)

  -- Higher-kinded primitives
  | Value.vHigherPrim prim => convertHigherPrimitive prim

  -- Function types (Pi) become closures
  | Value.vPi _qty _binder _name dom _cod =>
    -- todo: make closure representation fancier
    -- The domain and codomain inform monomorphization later
    let domTy := convertValueType dom
    -- Codomain is a closure, we can't easily evaluate it without an argument
    -- todo: dont use i64
    .closure #[domTy] (.prim .i64)

  -- Lambda (shouldn't appear as a type, but handle gracefully)
  | Value.vLam _ _ _ _ _ => .closure #[] (.prim .i64)

  -- Sigma types (dependent pairs) become structs
  | Value.vSigma _qty _name fst _snd =>
    let fstTy := convertValueType fst
    -- Second component is dependent, use i64 as default
    .struct #[("fst", fstTy), ("snd", .prim .i64)]

  -- Pair value
  | Value.vPair fst snd =>
    let fstTy := convertValueType fst
    let sndTy := convertValueType snd
    .struct #[("fst", fstTy), ("snd", sndTy)]

  -- Data types become tagged unions
  | Value.vDataType _id _params =>
    -- todo
    .tagged (.prim .u32) #[]

  -- Constructor applied to args, same as data type
  | Value.vConstructor _name _tag _args =>
    .rawPtr -- Constructors are heap-allocated

  -- Record types
  | Value.vRecord _row =>
    -- Records are structs, but we need row info to determine fields
    .rawPtr

  -- Record value
  | Value.vRecordVal _fields =>
    .rawPtr

  -- Variant types
  | Value.vVariant _row =>
    .tagged (.prim .u32) #[]

  -- Type universe - erased at runtime
  | Value.vType _ => .prim .unit

  -- Neutral terms (variables, applications)
  | Value.vNeutral _ty neu =>
    match neu with
    | .nVar v => .tyVar ⟨v.level.lvl⟩ -- Use de Bruijn level as type var index
    | .nMeta m => .tyVar ⟨m.id⟩ -- Metavariables also become type vars
    | _ => .prim .i64 -- Other neutrals (applications) are boxed

  -- Labels (for row types) are erased
  | Value.vLabelLit _ => .prim .unit

  -- Row types are erased
  | Value.vRowEmpty => .prim .unit
  | Value.vRowExtend _ _ _ => .prim .unit

  -- Equality types are erased (proofs have no runtime content)
  | Value.vEq _ _ _ _ => .prim .unit
  | Value.vRefl _ _ => .prim .unit
  | Value.vTransport _ _ _ _ _ _ _ => .prim .i64 -- Transport carries the value

  -- Literals
  | Value.vIntLit _ => .prim .i64
  | Value.vStringLit _ => .rawPtr

/-- Extract type parameters and value parameters from a function type (Pi chain) -/
partial def extractParams (ty : Value)
    (typeAcc : Array String := #[])
    (valAcc : Array (String × Ty) := #[])
    : Array String × Array (String × Ty) :=
  match ty with
  | Value.vPi _qty binder name dom cod =>
    -- Check if this is a type parameter (implicit binder with Type domain)
    let isTypeParam := binder.isImplicit && dom.isType
    match cod with
    | .const _ nextTy =>
      if isTypeParam then
        extractParams nextTy (typeAcc.push name) valAcc
      else
        let domTy := convertValueType dom
        extractParams nextTy typeAcc (valAcc.push (name, domTy))
    | .term _ _ _ =>
      -- Dependent type - we can't extract further without evaluation
      if isTypeParam then
        (typeAcc.push name, valAcc)
      else
        let domTy := convertValueType dom
        (typeAcc, valAcc.push (name, domTy))
  | _ => (typeAcc, valAcc)

/-- Extract the return type from a function type (Pi chain) and convert to Alloy Ty -/
def extractReturnType (ty : Value) : Ty :=
  match ty.returnType? with
  | some retVal => convertValueType retVal
  | none => .prim .i64  -- Dependent return type - fall back to i64

/-- Build function signature from a Value type. -/
def buildSignatureFromType (name : String) (ty : Value) (arity : Nat) : Signature :=
  let (typeParams, paramInfos) := extractParams ty
  -- Default type for parameters we can't extract (boxed i64)
  let defaultTy : Ty := .prim .i64
  -- If we got fewer params than arity (due to dependent types), pad with defaultTy
  let params := (List.range arity).toArray.map fun i =>
    if h : i < paramInfos.size then
      let (pname, pty) := paramInfos[i]
      { id := ⟨i⟩, name := pname, ty := pty : Param }
    else
      { id := ⟨i⟩, name := s!"arg{i}", ty := defaultTy : Param }
  let retTy := extractReturnType ty
  { name := name, typeParams := typeParams, params := params, retTy := retTy }

/-- Get the Alloy type for a Circuit node entry from its type annotation -/
def getNodeType (entry : CNodeEntry) : Ty :=
  convertValueType entry.ty

/-! ## Node Lowering -/

/-- The generic value type used at runtime (tagged pointer or immediate) -/
def valueType : Ty := .prim .i64

/-- Type for constructor tag -/
def tagType : Ty := .prim .u32

/-- Type for closure (fn ptr + env ptr) -/
def closureType : Ty := .struct #[("fn", .rawPtr), ("env", .rawPtr)]

/-- Reserved tag for closure CTORs in Circuit IR -/
def closureTag : Nat := 0xFFFFFE

/-- Reserved tag for panic CTORs in Circuit IR -/
def panicTag : Nat := 0xFFFFFF

/-- Reserved tag for array backing CTORs in Circuit IR -/
def arrayBackingTag : Nat := 0xFFFFFD

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

/-- Lower tag extraction for pattern matching -/
def lowerGetTag (scrutinee : LocalId) : LowerM LocalId := do
  -- Check if it's a pointer (heap-allocated) or immediate (nullary ctor)
  -- For now, assume heap-allocated and load tag from address
  let tagPtr ← LowerM.emitInst (.unOp (.bitcast (.ptr tagType)) (.local scrutinee)) (.ptr tagType)
  LowerM.emitInst (.load (.local tagPtr) tagType) tagType

/-- Lower a pattern match (MAT node) -/
def lowerMat (expectedTag : Nat) (scrutinee : LocalId) : LowerM (LocalId × BlockId × BlockId) := do
  let tag ← lowerGetTag scrutinee
  let expected ← LowerM.emitInst (.copy (.const (.int (Int.ofNat expectedTag) .u32))) tagType
  let cond ← LowerM.emitInst (.binOp .eq (.local tag) (.local expected) tagType) Ty.bool

  let thenBlock ← LowerM.freshBlockId
  let elseBlock ← LowerM.freshBlockId

  LowerM.finishBlock (.branch (.local cond) thenBlock elseBlock) thenBlock

  pure (cond, thenBlock, elseBlock)

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

  -- Check if currently being processed (cycle detection)
  if ns.visited.contains nodeId.id then
    -- Cycle detected, return undefined to break recursion
    -- This can happen with self-referential structures
    let undef ← StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
    return undef

  -- Mark as being processed
  set { ns with visited := ns.visited.insert nodeId.id }

  -- Get the node
  let some entry := graph.getNode nodeId
    | do
      -- Node not found - return undefined
      let undef ← StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
      return undef

  -- Get the type for this node from the type annotation
  let nodeTy := getNodeType entry

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
    StateT.lift (LowerM.emitInst (.copy (.const .unit)) nodeTy)

  | .lam erased => do
    -- LAM nodes in Circuit IR represent function parameters.
    -- After lambda lifting, nested lambdas become .closure expressions
    -- which lower to CTOR nodes with closureTag.
    --
    -- When we encounter a LAM during traversal, it's part of the
    -- parameter binding chain. We lower the body and return it.
    -- The variable binding is already handled by function parameters.
    if erased then
      -- Erased lambda: just return unit
      StateT.lift (LowerM.emitInst (.copy (.const .unit)) nodeTy)
    else
      -- Lower the body (aux1 port)
      match entry.getPort ⟨2⟩ with
      | some bodyPort => lowerNode graph bodyPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

  | .app => do
    -- Application: call closure with argument
    -- aux0 = function, aux1 = argument
    let fnVal ← match entry.getPort ⟨1⟩ with
      | some fnPort => lowerNode graph fnPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef closureType))) closureType)

    let argVal ← match entry.getPort ⟨2⟩ with
      | some argPort => lowerNode graph argPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const .unit)) Ty.unit)

    -- Use the node's type annotation for the result type
    StateT.lift (LowerM.emitInst (.callClosure (.local fnVal) #[.local argVal] nodeTy) nodeTy)

  | .ctor tag arity => do
    -- Check for special closure CTOR (tag 0xFFFFFE, arity 2)
    if tag == closureTag && arity == 2 then
      -- Closure: field 0 = REF (function), field 1 = env CTOR
      -- Get the function reference - we need to find the REF node's refId
      let fnRefNodeId ← match entry.getPort ⟨1⟩ with
        | some fnPort => pure fnPort.node
        | none => do
          -- No function reference - emit error closure
          let undef ← StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)
          return undef

      -- Look up the REF node to get the function ID
      let funcId ← match graph.getNode fnRefNodeId with
        | some fnEntry =>
          match fnEntry.node with
          | .ref refId => pure (FuncId.mk refId)
          | .alo refId => pure (FuncId.mk refId)  -- ALO also references a function
          | _ =>
            -- Not a REF/ALO node - treat as indirect call, use placeholder
            pure (FuncId.mk 0)
        | none => pure (FuncId.mk 0)

      -- Lower the environment (field 1)
      let envVal ← match entry.getPort ⟨2⟩ with
        | some envPort => lowerNode graph envPort.node
        | none => StateT.lift (LowerM.emitInst (.copy (.const (.null .rawPtr))) .rawPtr)

      -- Emit makeClosure instruction
      StateT.lift (LowerM.emitInst (.makeClosure funcId (.local envVal)) nodeTy)
    else
      -- Regular constructor: build tagged struct
      let mut fieldVals : Array LocalId := #[]
      for i in [:arity] do
        let fieldVal ← match entry.getPort ⟨i + 1⟩ with
          | some fieldPort => lowerNode graph fieldPort.node
          | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)
        fieldVals := fieldVals.push fieldVal
      StateT.lift (lowerCtor tag arity fieldVals)

  | .proj fieldIdx => do
    -- Projection: extract field from struct, result type comes from node annotation
    let recordVal ← match entry.getPort ⟨1⟩ with
      | some recordPort => lowerNode graph recordPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)
    -- Use nodeTy for the projected field type
    let offset := 4 + fieldIdx * 8
    let baseAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.bitcast (.prim .i64)) (.local recordVal)) (.prim .i64))
    let offsetVal ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat offset) .i64))) (.prim .i64))
    let fieldAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offsetVal) (.prim .i64)) (.prim .i64))
    let fieldPtr ← StateT.lift (LowerM.emitInst (.unOp (.bitcast .rawPtr) (.local fieldAddr)) .rawPtr)
    StateT.lift (LowerM.emitInst (.load (.local fieldPtr) nodeTy) nodeTy)

  | .record numFields => do
    -- Record: same as ctor with tag 0
    let mut fieldVals : Array LocalId := #[]
    for i in [:numFields] do
      let fieldVal ← match entry.getPort ⟨i + 1⟩ with
        | some fieldPort => lowerNode graph fieldPort.node
        | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)
      fieldVals := fieldVals.push fieldVal
    StateT.lift (lowerCtor 0 numFields fieldVals)

  | .mat expectedTag => do
    -- Pattern match: test tag and branch, result type from node annotation
    let scrutineeVal ← match entry.getPort ⟨1⟩ with
      | some scrutPort => lowerNode graph scrutPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

    let (_cond, thenBlock, elseBlock) ← StateT.lift (lowerMat expectedTag scrutineeVal)

    -- Lower hit branch
    let hitVal ← match entry.getPort ⟨2⟩ with
      | some hitPort => lowerNode graph hitPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

    -- Need a join block for phi
    let joinBlock ← StateT.lift LowerM.freshBlockId
    StateT.lift (LowerM.finishBlock (.jump joinBlock) elseBlock)

    -- Lower miss branch
    let missVal ← match entry.getPort ⟨3⟩ with
      | some missPort => lowerNode graph missPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

    StateT.lift (LowerM.finishBlock (.jump joinBlock) joinBlock)

    -- Phi to merge results, use node's type annotation
    StateT.lift (LowerM.emitInst
      (.phi #[(Operand.local hitVal, thenBlock), (Operand.local missVal, elseBlock)] nodeTy)
      nodeTy)

  | .op1 op => do
    let operandVal ← match entry.getPort ⟨1⟩ with
      | some opPort => lowerNode graph opPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)
    -- Use node's type annotation for result
    StateT.lift (LowerM.emitInst (.unOp (convertUnOp op) (.local operandVal)) nodeTy)

  | .op2 op => do
    let lhsVal ← match entry.getPort ⟨1⟩ with
      | some lhsPort => lowerNode graph lhsPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)
    let rhsVal ← match entry.getPort ⟨2⟩ with
      | some rhsPort => lowerNode graph rhsPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)
    -- Use node's type annotation for result
    let binOp := convertBinOp op
    StateT.lift (LowerM.emitInst (.binOp binOp (.local lhsVal) (.local rhsVal) nodeTy) nodeTy)

  | .dup _label => do
    -- DUP: clone the input value
    let inputVal ← match entry.getPort ⟨0⟩ with -- Principal port
      | some inputPort => lowerNode graph inputPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

    -- Clone for aux0 using node's type
    let copy0 ← StateT.lift (LowerM.emitInst (.clone (.local inputVal) nodeTy) nodeTy)
    -- Clone for aux1
    let copy1 ← StateT.lift (LowerM.emitInst (.clone (.local inputVal) nodeTy) nodeTy)

    -- Bind copies to output ports
    let port0 : CPortId := ⟨nodeId, ⟨1⟩⟩
    let port1 : CPortId := ⟨nodeId, ⟨2⟩⟩
    StateT.lift (LowerM.bindPort port0 copy0)
    StateT.lift (LowerM.bindPort port1 copy1)

    pure inputVal  -- Return original for principal

  | .sup _label => do
    -- SUP: select between alternatives (should be resolved at compile time)
    -- For residual SUPs, emit runtime selection
    StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

  | .ref refId => do
    -- Global reference: get function from book, type comes from annotation
    let funcId := FuncId.mk refId
    StateT.lift (LowerM.emitInst (.copy (.func funcId)) nodeTy)

  | .alo refId => do
    -- Allocation/instantiation: call the referenced function
    let funcId := FuncId.mk refId
    StateT.lift (LowerM.emitInst (.call funcId #[] nodeTy) nodeTy)

  | .use => do
    -- Strict evaluation: force the term, then continue
    let termVal ← match entry.getPort ⟨1⟩ with
      | some termPort => lowerNode graph termPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)
    -- In compiled code, terms are already evaluated (CBV), so this is identity
    pure termVal

  | .array _elemTy => do
    -- Array node: lower length and data, type from annotation
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
    -- Array indexing: load element at runtime index, result type from annotation
    let arrayVal ← match entry.getPort ⟨1⟩ with
      | some arrayPort => lowerNode graph arrayPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

    let indexVal ← match entry.getPort ⟨2⟩ with
      | some indexPort => lowerNode graph indexPort.node
      | none => StateT.lift (LowerM.emitInst (.copy (.const (.int 0 .u64))) (.prim .u64))

    -- Get data pointer (at offset 8 in array struct)
    let baseAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.bitcast (.prim .i64)) (.local arrayVal)) (.prim .i64))
    let offset8 ← StateT.lift (LowerM.emitInst (.copy (.const (.int 8 .i64))) (.prim .i64))
    let dataPtrAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offset8) (.prim .i64)) (.prim .i64))
    let dataPtrSlot ← StateT.lift (LowerM.emitInst (.unOp (.bitcast .rawPtr) (.local dataPtrAddr)) .rawPtr)
    let dataPtr ← StateT.lift (LowerM.emitInst (.load (.local dataPtrSlot) .rawPtr) .rawPtr)

    -- Calculate element address (use node type's size for element)
    let elemSize ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat nodeTy.sizeBytes) .i64))) (.prim .i64))
    let offset ← StateT.lift (LowerM.emitInst (.binOp .mul (.local indexVal) (.local elemSize) (.prim .i64)) (.prim .i64))
    let dataAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.bitcast (.prim .i64)) (.local dataPtr)) (.prim .i64))
    let elemAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local dataAsI64) (.local offset) (.prim .i64)) (.prim .i64))
    let elemPtr ← StateT.lift (LowerM.emitInst (.unOp (.bitcast .rawPtr) (.local elemAddr)) .rawPtr)

    -- Load with the node's actual type
    StateT.lift (LowerM.emitInst (.load (.local elemPtr) nodeTy) nodeTy)

  | .slice => do
    -- Slice: create view without copying
    StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

  -- Cache result
  modify fun ns => { ns with results := ns.results.insert nodeId.id result }
  pure result

/-! ## Function Lowering -/

/-- Traverse LAM chain to find body and collect var ports.
    Returns (body node, array of var port node IDs) -/
def traverseLamChain (graph : CGraph) (root : CNodeId) (arity : Nat) : CNodeId × Array CNodeId := Id.run do
  let mut current := root
  let mut varNodes : Array CNodeId := #[]

  for _ in [:arity] do
    if let some entry := graph.getNode current then
      match entry.node with
      | .lam _ =>
        -- Collect the var port's connected node (port 1)
        if let some varPort := entry.getPort ⟨1⟩ then
          varNodes := varNodes.push varPort.node
        -- Move to body (port 2)
        if let some bodyPort := entry.getPort ⟨2⟩ then
          current := bodyPort.node
      | _ => break
    else
      break

  (current, varNodes)

/-- Lower a Circuit definition to an Alloy function -/
def lowerDefinition (graph : CGraph) (def_ : CDefinition) (funcId : FuncId) : Func :=
  -- Build signature from the definition's type annotation
  let sig := buildSignatureFromType def_.name def_.ty def_.arity

  let (_, func) := LowerM.run' funcId sig do
    if def_.arity == 0 then
      -- No parameters: just lower the root directly
      let (result, _) ← StateT.run (lowerNode graph def_.root) {}
      LowerM.terminate (.ret (.local result))
    else
      -- Has parameters: traverse LAM chain and bind params to var ports
      let (bodyNode, varNodes) := traverseLamChain graph def_.root def_.arity

      -- Build initial NodeState with var ports mapped to function parameters
      let mut initState : NodeState := {}
      for i in [:varNodes.size] do
        if h : i < varNodes.size then
          -- Map the var port node to the corresponding function parameter
          let varNodeId := varNodes[i]
          let paramId : LocalId := ⟨i⟩
          initState := { initState with results := initState.results.insert varNodeId.id paramId }

      -- Also mark LAM nodes as visited so we don't re-traverse them
      let mut current := def_.root
      for _ in [:def_.arity] do
        initState := { initState with visited := initState.visited.insert current.id }
        if let some entry := graph.getNode current then
          if let some bodyPort := entry.getPort ⟨2⟩ then
            current := bodyPort.node

      -- Lower the body with var ports pre-bound
      let (result, _) ← StateT.run (lowerNode graph bodyNode) initState
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

end Somac.Alloy.Lower
