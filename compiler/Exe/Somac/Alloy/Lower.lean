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
import Soma.Core.Name
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
open Soma.Core (Name FFIOp Intrinsic)

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
  deriving Inhabited

namespace LowerState

/-- Create initial state for a function -/
def init (funcId : FuncId) (sig : Signature) : LowerState :=
  let entry : Block := { id := .entry, terminator := .unreachable }
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
  { s with currentBlock := newBlock, blocks := s.blocks.push finished }

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

def getCurrentBlockId : LowerM BlockId := do
  let s ← get
  pure s.currentBlock.id

end LowerM

/-- Convert Circuit PrimType to Alloy PrimTy -/
def convertPrimType : PrimType → PrimTy
  | .u8 => .u8 | .u16 => .u16 | .u32 => .u32 | .u64 => .u64
  | .i8 => .i8 | .i16 => .i16 | .i32 => .i32 | .i64 => .i64
  | .f32 => .f32 | .f64 => .f64
  | .bool => .bool
  | .char => .u32

/-- Convert Circuit Op2Code to Alloy BinOp -/
def convertBinOp : Op2Code → BinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .rem
  | .and => .and | .or => .or | .xor => .xor | .shl => .shl | .shr => .shr
  | .eq => .eq | .ne => .ne | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge

/-- Convert Circuit Op1Code to Alloy UnOp -/
def convertUnOp : Op1Code → UnOp
  | .not => .not
  | .neg => .neg

/-- Convert Core FFIOp to Alloy IntrinsicOp -/
def convertFFIOp : FFIOp → IntrinsicOp
  | .null => .ptrNull
  | .ptrAdd => .ptrAdd
  | .ptrDiff => .ptrDiff
  | .ptrRead => .ptrRead
  | .ptrWrite => .ptrWrite
  | .ptrCast => .ptrCast
  | .toCString => .toCString
  | .fromCString => .fromCString
  | .cstringLen => .cstringLen
  | .strcat => .strcat
  | .intToString => .intToString
  | .pureIO => .pureIO

/-- Convert Core.PrimOp to Alloy.PrimOp -/
def convertCorePrimOp : Soma.Core.PrimOp → PrimOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod
  | .eq => .eq | .ne => .ne | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge
  | .and => .and | .or => .or | .not => .not | .neg => .neg

/-- Result of resolving a function reference through the IR graph -/
inductive CanonicalRef where
  /-- Direct reference to a book definition by index -/
  | bookRef (idx : Nat)
  /-- Runtime-computed value -/
  | dynamicValue (nodeId : CNodeId)
  deriving Repr, Inhabited

/-- Follow USE/DUP chains to find the canonical source of a value -/
partial def resolveCanonicalRef (graph : CGraph) (nodeId : CNodeId)
    (fuel : Nat := 1000) : CanonicalRef :=
  if fuel == 0 then
    .dynamicValue nodeId
  else
    match graph.getNode nodeId with
    | some entry =>
      match entry.node with
      | .ref idx => .bookRef idx
      | .alo idx => .bookRef idx
      | .use =>
        -- USE reads its value from port 1, follow through
        match entry.getPort ⟨1⟩ with
        | some port => resolveCanonicalRef graph port.node (fuel - 1)
        | none => .dynamicValue nodeId
      | .dup _ =>
        -- DUP duplicates its input from port 0, follow through
        match entry.getPort ⟨0⟩ with
        | some port => resolveCanonicalRef graph port.node (fuel - 1)
        | none => .dynamicValue nodeId
      | _ =>
        .dynamicValue nodeId
    | none => .dynamicValue nodeId

/-- Build a FuncRef from a book index, handling intrinsics and externals -/
def buildFuncRefFromBookRef (graph : CGraph) (refId : Nat)
    (funcIdMap : Option (Std.HashMap Nat FuncId) := none) : FuncRef :=
  match graph.getDefinition refId with
  | some def_ =>
    -- Check if the definition's Name carries intrinsic information
    match def_.name.intrinsic? with
    | some (Intrinsic.ffiOp op) => .intrinsic (convertFFIOp op)
    | some (Intrinsic.extern name) => .externC name
    | some (Intrinsic.primOp op) => .primOp (convertCorePrimOp op)
    | some (Intrinsic.llvm name) => .externC name
    | some (Intrinsic.runtime fn) => .externC fn.name
    | none =>
      if def_.isExternal then
        .external def_.name.display
      else
        -- Local function
        match funcIdMap with
        | some map =>
          match map.get? refId with
          | some funcId => .local funcId
          | none => .external def_.name.display
        | none =>
          .local (FuncId.mk refId)
  | none =>
    -- todo: consider panicking
    .external s!"unresolved_ref_{refId}"

open Soma.Core (Value StarPrimitive HigherPrimitive TypeId)

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
  | .array => .rawPtr | .list => .rawPtr | .ref => .rawPtr
  | .io => .prim .unit | .ptr => .rawPtr

mutual

/-- Extract variant information from a row type -/
partial def extractRowVariants (row : Value) (idx : Nat := 0) (acc : Array (Nat × Array Ty) := #[])
    : Array (Nat × Array Ty) :=
  match row with
  | Value.vRowEmpty => acc
  | Value.vRowExtend _label fieldTy tail =>
    let fields := match fieldTy with
      | Value.vPrimTy (.unit) => #[]
      | Value.vSigma _ _ fst sndClos =>
        let fstTy := convertValueType fst
        let sndTy := match sndClos with
          | .const _ v => convertValueType v
          | _ => .prim .i64
        #[fstTy, sndTy]
      | Value.vPair fst snd =>
        #[convertValueType fst, convertValueType snd]
      | other => #[convertValueType other]
    extractRowVariants tail (idx + 1) (acc.push (idx, fields))
  | _ => acc -- Malformed

/-- Convert a Soma Value type to an Alloy Ty -/
partial def convertValueType : Value → Ty
  -- Primitive types
  | Value.vPrimTy prim => .prim (convertStarPrimitive prim)

  -- Higher-kinded primitives
  | Value.vHigherPrim prim => convertHigherPrimitive prim
  | Value.vPi _ _ _ dom cod =>
    let domTy := convertValueType dom
    let codTy := match cod with
      | .const _ result => convertValueType result
      | .term _ _ _ => .prim .i64
    .closure #[domTy] codTy

  -- Lambda (shouldn't appear as a type, but handle gracefully)
  | Value.vLam _ _ _ _ _ => .closure #[] (.prim .i64)
  | Value.vSigma _ _ fst sndClos =>
    let sndTy := match sndClos with
      | .const _ v => convertValueType v
      | _ => .prim .i64 -- Dependent type, fall back to boxed
    .struct #[("fst", convertValueType fst), ("snd", sndTy)]
  | Value.vPair fst snd =>
    .struct #[("fst", convertValueType fst), ("snd", convertValueType snd)]
  | Value.vDataType id params =>
    if id.module == TypeId.builtinModule && id.unique == HigherPrimitive.io.uniqueId then
      match params with
      | [innerTy] => convertValueType innerTy
      | _ => .prim .unit
    else .tagged (.prim .u32) #[]
  | Value.vConstructor _ _ _ => .rawPtr
  | Value.vRecord _ => .rawPtr
  | Value.vRecordVal _ => .rawPtr
  | Value.vVariant row => .tagged (.prim .u32) (extractRowVariants row)
  | Value.vType _ => .prim .unit
  | Value.vNeutral _ neu =>
    match neu with
    | .nVar v => .tyVar ⟨v.level.lvl⟩
    | .nMeta m => .tyVar ⟨m.id⟩
    | _ => .prim .i64
  | Value.vLabelLit _ => .prim .unit
  | Value.vRowEmpty => .prim .unit
  | Value.vRowExtend _ _ _ => .prim .unit
  | Value.vEq _ _ _ _ => .prim .unit
  | Value.vRefl _ _ => .prim .unit
  | Value.vTransport _ _ _ _ _ _ _ => .prim .i64
  | Value.vIntLit _ => .prim .i32
  | Value.vStringLit _ => .rawPtr
end

partial def extractParams (ty : Value)
    (typeAcc : Array String := #[]) (valAcc : Array (String × Ty) := #[])
    : Array String × Array (String × Ty) :=
  match ty with
  | Value.vPi _ binder name dom cod =>
    let isTypeParam := binder.isImplicit && dom.isType
    match cod with
    | .const _ nextTy =>
      if isTypeParam then extractParams nextTy (typeAcc.push name) valAcc
      else extractParams nextTy typeAcc (valAcc.push (name, convertValueType dom))
    | .term _ _ _ =>
      if isTypeParam then (typeAcc.push name, valAcc)
      else (typeAcc, valAcc.push (name, convertValueType dom))
  | _ => (typeAcc, valAcc)

/-- Extract the return type from a function type (Pi chain) and convert to Alloy Ty -/
def extractReturnType (ty : Value) : Ty :=
  match ty.returnType? with
  | some retVal => convertValueType retVal
  | none => .prim .i64

/-- Build function signature from a Value type. -/
def buildSignatureFromType (name : Name) (ty : Value) (arity : Nat) : Signature :=
  let (typeParams, paramInfos) := extractParams ty
  -- Default type for parameters we can't extract (boxed i64)
  let defaultTy : Ty := .prim .i64
  -- If we got fewer params than arity (due to dependent types), pad with defaultTy
  let params := (List.range arity).toArray.map fun i =>
    if h : i < paramInfos.size then
      let (pname, pty) := paramInfos[i]
      { id := ⟨i⟩, name := pname, ty := pty : Param }
    else { id := ⟨i⟩, name := s!"arg{i}", ty := defaultTy : Param }
  { name := name.display, typeParams, params, retTy := extractReturnType ty }

def getNodeType (entry : CNodeEntry) : Ty := convertValueType entry.ty

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

/-- State maintained during graph traversal -/
structure NodeState where
  /-- Nodes currently being processed (for cycle detection) -/
  processing : Std.HashSet Nat := {}
  /-- Cached results for nodes (principal port values) -/
  results : Std.HashMap Nat LocalId := {}
  /-- LAM node ID → parameter index mapping -/
  lamParams : Std.HashMap Nat Nat := {}
  deriving Inhabited

namespace NodeState

/-- Snapshot the results cache (for branch isolation) -/
def snapshotResults (s : NodeState) : Std.HashMap Nat LocalId := s.results

/-- Restore results cache from a snapshot -/
def restoreResults (s : NodeState) (snapshot : Std.HashMap Nat LocalId) : NodeState :=
  { s with results := snapshot }

end NodeState

/-- Lower a numeric literal -/
def lowerNum (primTy : PrimType) (val : UInt32) : LowerM LocalId := do
  let ty := Ty.prim (convertPrimType primTy)
  let intVal : Int :=
    if primTy.toUInt8 >= 4 && primTy.toUInt8 <= 7 then
      let v := val.toNat
      if v >= 0x80000000 then Int.negOfNat (0x100000000 - v) else Int.ofNat v
    else Int.ofNat val.toNat
  LowerM.emitInst (.copy (.const (.int intVal (convertPrimType primTy)))) ty

/-- Lower a constructor (creates a tagged struct on the heap) -/
def lowerCtor (tag : Nat) (_arity : Nat) (fieldVals : Array LocalId) (ty : Ty) : LowerM LocalId := do
  -- The LLVM codegen handles heap allocation of the payload
  let payload := fieldVals.map fun id => Operand.local id
  let taggedTy := match ty with
    | .tagged _ _ => ty -- Already a tagged type, keep it
    | _ => .tagged (.prim .u32) #[] -- Convert to tagged union type
  LowerM.emitInst (.taggedLit tag payload taggedTy) taggedTy

/-- Build a nested struct literal for nested pair types.
    For a type like `{ fst: A, snd: { fst: B, snd: C } }` with flat fields `[a, b, c]`,
    this recursively builds `{ a, { b, c } }`. -/
partial def lowerNestedStructLit (fieldVals : Array LocalId) (ty : Ty) : LowerM LocalId := do
  match ty with
  | .struct fields =>
    if fields.size == 2 then
      -- Check if second field is also a struct (nested pair)
      let sndTy := fields[1]?.map (·.snd)
      match sndTy with
      | some (Ty.struct innerFields) =>
        if innerFields.size >= 2 && fieldVals.size > 2 then
          -- Nested struct: recursively build the inner struct
          let innerTy := Ty.struct innerFields
          let innerVals := fieldVals.extract 1 fieldVals.size
          let innerVal ← lowerNestedStructLit innerVals innerTy
          -- Build outer struct with first field and nested inner
          let outerFields := #[Operand.local fieldVals[0]!, Operand.local innerVal]
          LowerM.emitInst (.structLit outerFields ty) ty
        else
          -- Not enough fields for nesting, use flat
          let ops := fieldVals.map fun id => Operand.local id
          LowerM.emitInst (.structLit ops ty) ty
      | _ =>
        -- Second field is not a struct, use flat
        let ops := fieldVals.map fun id => Operand.local id
        LowerM.emitInst (.structLit ops ty) ty
    else
      -- Not a 2-field struct, use flat
      let ops := fieldVals.map fun id => Operand.local id
      LowerM.emitInst (.structLit ops ty) ty
  | _ =>
    -- Not a struct type, emit single value
    if h : fieldVals.size > 0 then
      pure fieldVals[0]
    else
      LowerM.emitInst (.copy (.const (.undef ty))) ty

/-- Lower tag extraction for pattern matching -/
def lowerGetTag (scrutinee : LocalId) : LowerM LocalId := do
  -- Use .getTag instruction which handles both by-value and pointer-based tagged unions
  LowerM.emitInst (.getTag (.local scrutinee)) tagType

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
def lowerString (stringIdx : Nat) (len : Nat) : LowerM LocalId := do
  let stringSize := 16
  let stringPtr ← LowerM.emitInst (.malloc (.const (.int (Int.ofNat stringSize) .u64))) .rawPtr

  -- Store length
  let lenVal ← LowerM.emitInst (.copy (.const (.int (Int.ofNat len) .u64))) (.prim .u64)
  LowerM.emitVoid (.store (.local stringPtr) (.local lenVal))

  -- Store data pointer
  let baseAsI64 ← LowerM.emitInst (.unOp (.ptrtoint .i64) (.local stringPtr)) (.prim .i64)
  let offset8 ← LowerM.emitInst (.copy (.const (.int 8 .i64))) (.prim .i64)
  let dataPtrAddr ← LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offset8) (.prim .i64)) (.prim .i64)
  let dataPtrSlot ← LowerM.emitInst (.unOp .inttoptr (.local dataPtrAddr)) .rawPtr

  -- Reference the string data directly from the global string table
  let dataPtr ← LowerM.emitInst (.copy (.const (.string stringIdx len))) .rawPtr
  LowerM.emitVoid (.store (.local dataPtrSlot) (.local dataPtr))
  pure stringPtr

/-- Check if a type needs heap deallocation when erased (todo: more nuanced check) -/
def needsErase : Ty → Bool
  | .prim _ => false
  | .rawPtr | .ptr _ | .closure _ _ | .tagged _ _ => true
  | .struct _ | .array _ _ | .funcPtr _ _ => false
  | .tyVar _ => true
  | .forall_ _ body => needsErase body
  | .tyApp func _ => needsErase func

mutual

/-- Lower an operand by following a wire from a port -/
partial def lowerOperand (graph : CGraph) (port : CPortId) : StateT NodeState LowerM LocalId := do
  let ns ← get

  -- Check if this specific port was already bound
  if let some cached := ns.results.get? (port.node.id * 1000 + port.port.idx) then
    return cached

  -- Special case: accessing a LAM's var port means we want the parameter
  if port.port.idx == 1 then
    if let some paramIdx := ns.lamParams.get? port.node.id then
      return ⟨paramIdx⟩

  -- Otherwise, lower the node itself
  lowerNode graph port.node

/-- Lower a node, returning the value at its principal port -/
partial def lowerNode (graph : CGraph) (nodeId : CNodeId) : StateT NodeState LowerM LocalId := do
  let ns ← get

  -- Check memoization cache
  if let some result := ns.results.get? nodeId.id then
    return result

  -- Cycle detection
  if ns.processing.contains nodeId.id then
    let undef ← StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
    return undef

  -- Mark as processing
  modify fun s => { s with processing := s.processing.insert nodeId.id }

  -- Get the node
  let some entry := graph.getNode nodeId | do
    let undef ← StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
    return undef

  let nodeTy := getNodeType entry

  let getPortType (portIdx : Nat) (defaultTy : Ty := nodeTy) : Ty :=
    match entry.getPort ⟨portIdx⟩ with
    | some targetPort =>
      match graph.getNode targetPort.node with
      | some targetEntry => getNodeType targetEntry
      | none => defaultTy
    | none => defaultTy

  -- Helper to lower an operand from a port connection
  let lowerPort (portIdx : Nat) (defaultTy : Ty := nodeTy) : StateT NodeState LowerM LocalId := do
    match entry.getPort ⟨portIdx⟩ with
    | some targetPort => lowerOperand graph targetPort
    | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef defaultTy))) defaultTy)

  let result ← match entry.node with
  | .num primTy val =>
    StateT.lift (lowerNum primTy val)

  | .era =>
    StateT.lift (LowerM.emitInst (.copy (.const .unit)) (.prim .unit))

  | .lam _ => lowerPort 2

  | .app => do
    -- Application: call closure with argument
    -- aux0 = function, aux1 = argument
    let fnPort := entry.getPort ⟨1⟩

    -- Check for intrinsic/extern calls
    let maybeIntrinsic ← match fnPort with
      | some fp =>
        match graph.getNode fp.node with
        | some fnEntry =>
          match fnEntry.node with
          | .ref refId | .alo refId =>
            match graph.getDefinition refId with
            | some def_ =>
              match def_.name.intrinsic? with
              | some (Intrinsic.ffiOp op) => pure (some (Sum.inl op : Sum FFIOp String))
              | some (Intrinsic.extern name) => pure (some (Sum.inr name : Sum FFIOp String))
              | _ => pure none
            | none => pure none
          | _ => pure none
        | none => pure none
      | none => pure none

    -- Lower the argument
    let argVal ← lowerPort 2 (.prim .unit)

    match maybeIntrinsic with
    | some (Sum.inl ffiOp) =>
      let intrinsicOp := convertFFIOp ffiOp
      let retTy := intrinsicOp.fixedRetTy.getD nodeTy
      StateT.lift (LowerM.emitInst (.callIntrinsic intrinsicOp #[.local argVal] retTy) retTy)
    | some (Sum.inr externName) =>
      -- Extern function: emit callExtern
      StateT.lift (LowerM.emitInst (.callExtern externName #[.local argVal] nodeTy) nodeTy)
    | none =>
      -- Regular function call: check what the function node is
      match fnPort with
      | none =>
        -- No function port → erased, return unit
        StateT.lift (LowerM.emitInst (.copy (.const .unit)) (.prim .unit))
      | some fp =>
        match graph.getNode fp.node with
        | none =>
          -- Missing node → treat as erased
          StateT.lift (LowerM.emitInst (.copy (.const .unit)) (.prim .unit))
        | some fnEntry =>
          match fnEntry.node with
          | .era =>
            -- Function is ERA → erased, return unit
            StateT.lift (LowerM.emitInst (.copy (.const .unit)) (.prim .unit))
          | .lam _ =>
            -- Inline beta reduction
            lowerNode graph fp.node
          | _ =>
            -- Regular closure call: lower the function and use callClosure
            let fnNodeTy := getNodeType fnEntry
            if fnNodeTy == .prim .unit then
              StateT.lift (LowerM.emitInst (.copy (.const .unit)) (.prim .unit))
            else
              let fnVal ← lowerNode graph fp.node
              StateT.lift (LowerM.emitInst (.callClosure (.local fnVal) #[.local argVal] nodeTy) nodeTy)

  | .ctor tag arity => do
    -- Check for special closure CTOR (tag 0xFFFFFE, arity 2)
    if tag == closureTag && arity == 2 then
      -- Closure CTOR
      let fnPort ← match entry.getPort ⟨1⟩ with
        | some p => pure p
        | none =>
          let undef ← StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)
          return undef

      -- Resolve the function reference by following USE/DUP chains
      let funcRef ← match resolveCanonicalRef graph fnPort.node with
        | .bookRef refId =>
          pure (buildFuncRefFromBookRef graph refId none)
        | .dynamicValue dynNodeId =>
          -- todo: extract the function pointer at runtime.
          pure (FuncRef.external s!"$dynamic_closure_{dynNodeId.id}")

      -- Lower the environment (port 2)
      let envVal ← match entry.getPort ⟨2⟩ with
        | some envPort => lowerOperand graph envPort
        | none => StateT.lift (LowerM.emitInst (.copy (.const (.null .rawPtr))) .rawPtr)

      -- Emit makeClosure instruction
      StateT.lift (LowerM.emitInst (.makeClosure funcRef (.local envVal)) nodeTy)
    else
      -- Regular constructor: build tagged struct
      let mut fieldVals : Array LocalId := #[]
      for i in [:arity] do
        let fieldVal ← lowerPort (i + 1)
        fieldVals := fieldVals.push fieldVal
      -- Check if target type is struct (for tuples/pairs) or tagged union (for ADTs)
      match nodeTy with
      | .struct _ =>
        -- Create struct literal, handling nested pair types
        StateT.lift (lowerNestedStructLit fieldVals nodeTy)
      | _ =>
        -- Create tagged union (for ADTs)
        StateT.lift (lowerCtor tag arity fieldVals nodeTy)

  | .proj fieldIdx => do
    let recordVal ← lowerPort 1
    let recordTy := getPortType 1
    -- Check if record is struct or tagged union
    match recordTy with
    | .struct fields =>
      -- Use extractField for struct types
      -- Compute the correct field type from the struct definition
      let fieldTy := if h : fieldIdx < fields.size then fields[fieldIdx].snd else nodeTy
      StateT.lift (LowerM.emitInst (.extractField (.local recordVal) fieldIdx) fieldTy)
    | _ =>
      -- Use getPayload for tagged unions
      StateT.lift (LowerM.emitInst (.getPayload (.local recordVal) 0 fieldIdx nodeTy) nodeTy)

  | .record numFields => do
    -- Record: check if target type is struct or tagged union
    let mut fieldVals : Array LocalId := #[]
    for i in [:numFields] do
      let fieldVal ← lowerPort (i + 1)
      fieldVals := fieldVals.push fieldVal
    match nodeTy with
    | .struct _ =>
      -- Create struct literal, handling nested pair types
      StateT.lift (lowerNestedStructLit fieldVals nodeTy)
    | _ =>
      -- Create tagged union with tag 0
      StateT.lift (lowerCtor 0 numFields fieldVals nodeTy)

  | .mat expectedTag => do
    let scrutineeVal ← lowerPort 1
    let (_, _thenBlock, elseBlock) ← StateT.lift (lowerMat expectedTag scrutineeVal)
    let cacheSnapshot ← do let ns ← get; pure ns.snapshotResults

    -- Lower hit value
    let hitVal ← lowerPort 2
    -- Record the actual block we're in after lowering the hit branch
    let hitBlock ← StateT.lift LowerM.getCurrentBlockId
    let joinBlock ← StateT.lift LowerM.freshBlockId
    StateT.lift (LowerM.finishBlock (.jump joinBlock) elseBlock)

    -- Restore cache
    modify fun ns => ns.restoreResults cacheSnapshot

    -- Lower miss value
    let missVal ← lowerPort 3
    -- Record the actual block we're in after lowering the miss branch
    let missBlock ← StateT.lift LowerM.getCurrentBlockId
    StateT.lift (LowerM.finishBlock (.jump joinBlock) joinBlock)

    -- Phi to merge results
    StateT.lift (LowerM.emitInst
      (.phi #[(Operand.local hitVal, hitBlock), (Operand.local missVal, missBlock)] nodeTy)
      nodeTy)

  | .op1 op => do
    let operandVal ← lowerPort 1
    StateT.lift (LowerM.emitInst (.unOp (convertUnOp op) (.local operandVal)) nodeTy)

  | .op2 op => do
    let lhsVal ← lowerPort 1
    let rhsVal ← lowerPort 2
    let binOp := convertBinOp op
    let opTy := if binOp.isComparison then getPortType 1 else nodeTy
    StateT.lift (LowerM.emitInst (.binOp binOp (.local lhsVal) (.local rhsVal) opTy) nodeTy)

  | .dup _ => do
    let inputVal ← lowerPort 0
    let copy0 ← StateT.lift (LowerM.emitInst (.clone (.local inputVal) nodeTy) nodeTy)
    let copy1 ← StateT.lift (LowerM.emitInst (.clone (.local inputVal) nodeTy) nodeTy)

    -- Bind copies to specific output port keys
    modify fun ns => { ns with
      results := ns.results.insert (nodeId.id * 1000 + 1) copy0
                 |>.insert (nodeId.id * 1000 + 2) copy1
    }
    pure inputVal

  | .sup _ =>
    StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

  | .ref refId | .alo refId => do
    -- Function reference used as a value
    let funcRef := buildFuncRefFromBookRef graph refId none
    let nullEnv ← StateT.lift (LowerM.emitInst (.copy (.const (.null .rawPtr))) .rawPtr)
    StateT.lift (LowerM.emitInst (.makeClosure funcRef (.local nullEnv)) nodeTy)

  | .use => lowerPort 1

  | .array _ => do
    let _ ← lowerPort 1 (.prim .u64)
    lowerPort 2 .rawPtr

  | .string => do
    -- String node: extract length and string index from connected NUM nodes
    -- aux0 = length (NUM node), aux1 = string table index (NUM node)
    let len : Nat ← match entry.getPort ⟨1⟩ with
      | some lenPort =>
        match graph.getNode lenPort.node with
        | some lenEntry => match lenEntry.node with
          | .num _ val => pure val.toNat
          | _ => pure 0
        | none => pure 0
      | none => pure 0

    let stringIdx : Nat ← match entry.getPort ⟨2⟩ with
      | some idxPort =>
        match graph.getNode idxPort.node with
        | some idxEntry => match idxEntry.node with
          | .num _ val => pure val.toNat
          | _ => pure 0
        | none => pure 0
      | none => pure 0

    StateT.lift (lowerString stringIdx len)

  | .index => do
    let arrayVal ← lowerPort 1
    let indexVal ← lowerPort 2 (.prim .u64)

    let baseAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local arrayVal)) (.prim .i64))
    let offset8 ← StateT.lift (LowerM.emitInst (.copy (.const (.int 8 .i64))) (.prim .i64))
    let dataPtrAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offset8) (.prim .i64)) (.prim .i64))
    let dataPtrSlot ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local dataPtrAddr)) .rawPtr)
    let dataPtr ← StateT.lift (LowerM.emitInst (.load (.local dataPtrSlot) .rawPtr) .rawPtr)

    -- Calculate element address (use node type's size for element)
    let elemSize ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat nodeTy.sizeBytes) .i64))) (.prim .i64))
    let offset ← StateT.lift (LowerM.emitInst (.binOp .mul (.local indexVal) (.local elemSize) (.prim .i64)) (.prim .i64))
    let dataAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local dataPtr)) (.prim .i64))
    let elemAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local dataAsI64) (.local offset) (.prim .i64)) (.prim .i64))
    let elemPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local elemAddr)) .rawPtr)

    -- Load with the node's actual type
    StateT.lift (LowerM.emitInst (.load (.local elemPtr) nodeTy) nodeTy)

  | .slice =>
    StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

  -- Cache result and clear processing flag
  modify fun ns => { ns with
    results := ns.results.insert nodeId.id result
    processing := ns.processing.erase nodeId.id
  }
  pure result

end


/-- Collect LAM chain information for function parameters -/
def collectLamChain (graph : CGraph) (root : CNodeId) (arity : Nat)
    : CNodeId × Std.HashMap Nat Nat := Id.run do
  let mut current := root
  let mut lamParams : Std.HashMap Nat Nat := {}

  for i in [:arity] do
    if let some entry := graph.getNode current then
      match entry.node with
      | .lam _ =>
        -- Record this LAM node as parameter i
        lamParams := lamParams.insert current.id i
        -- Move to body
        if let some bodyPort := entry.getPort ⟨2⟩ then
          current := bodyPort.node
      | _ => break
    else break

  (current, lamParams)

/-- Lower a Circuit definition to an Alloy function -/
def lowerDefinition (graph : CGraph) (def_ : CDefinition) (funcId : FuncId) : Func :=
  -- Build signature from the definition's type annotation
  let sig := buildSignatureFromType def_.name def_.ty def_.arity
  let returnsUnit := sig.retTy == .prim .unit

  let (_, func) := LowerM.run' funcId sig do
    if def_.arity == 0 then
      -- No parameters: just lower the root directly
      let (result, _) ← StateT.run (lowerNode graph def_.root) {}
      if returnsUnit then LowerM.terminate .retUnit
      else LowerM.terminate (.ret (.local result))
    else
      let (bodyNode, lamParams) := collectLamChain graph def_.root def_.arity
      let initState : NodeState := { lamParams }
      let (result, _) ← StateT.run (lowerNode graph bodyNode) initState
      if returnsUnit then LowerM.terminate .retUnit
      else LowerM.terminate (.ret (.local result))

  func

/-- Mapping from Circuit book index to Alloy FuncId -/
abbrev FuncIdMap := Std.HashMap Nat FuncId

mutual

/-- Lower an operand with FuncId map -/
partial def lowerOperandWithMap (graph : CGraph) (port : CPortId) (funcIdMap : FuncIdMap)
    : StateT NodeState LowerM LocalId := do
  let ns ← get

  if let some cached := ns.results.get? (port.node.id * 1000 + port.port.idx) then
    return cached

  if port.port.idx == 1 then
    if let some paramIdx := ns.lamParams.get? port.node.id then
      return ⟨paramIdx⟩

  lowerNodeWithMap graph port.node funcIdMap

/-- Lower a node with FuncId mapping for closure references -/
partial def lowerNodeWithMap (graph : CGraph) (nodeId : CNodeId) (funcIdMap : FuncIdMap)
    : StateT NodeState LowerM LocalId := do
  let ns ← get

  if let some result := ns.results.get? nodeId.id then
    return result

  if ns.processing.contains nodeId.id then
    let undef ← StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
    return undef

  modify fun s => { s with processing := s.processing.insert nodeId.id }

  let some entry := graph.getNode nodeId | do
    let undef ← StateT.lift (LowerM.emitInst (.copy (.const (.undef valueType))) valueType)
    return undef

  let nodeTy := getNodeType entry

  -- todo: remove boilerplate
  let getPortType (portIdx : Nat) (defaultTy : Ty := nodeTy) : Ty :=
    match entry.getPort ⟨portIdx⟩ with
    | some targetPort =>
      match graph.getNode targetPort.node with
      | some targetEntry => getNodeType targetEntry
      | none => defaultTy
    | none => defaultTy

  let lowerPort (portIdx : Nat) (defaultTy : Ty := nodeTy) : StateT NodeState LowerM LocalId := do
    match entry.getPort ⟨portIdx⟩ with
    | some targetPort => lowerOperandWithMap graph targetPort funcIdMap
    | none => StateT.lift (LowerM.emitInst (.copy (.const (.undef defaultTy))) defaultTy)

  let result ← match entry.node with
  | .num primTy val =>
    StateT.lift (lowerNum primTy val)

  | .era =>
    StateT.lift (LowerM.emitInst (.copy (.const .unit)) (.prim .unit))

  | .lam _ =>
    lowerPort 2

  | .app => do
    let fnPort := entry.getPort ⟨1⟩

    let maybeIntrinsic ← match fnPort with
      | some fp =>
        match graph.getNode fp.node with
        | some fnEntry =>
          match fnEntry.node with
          | .ref refId | .alo refId =>
            match graph.getDefinition refId with
            | some def_ =>
              match def_.name.intrinsic? with
              | some (Intrinsic.ffiOp op) => pure (some (Sum.inl op : Sum FFIOp String))
              | some (Intrinsic.extern name) => pure (some (Sum.inr name : Sum FFIOp String))
              | _ => pure none
            | none => pure none
          | _ => pure none
        | none => pure none
      | none => pure none

    let argVal ← lowerPort 2 (.prim .unit)

    match maybeIntrinsic with
    | some (Sum.inl ffiOp) =>
      let intrinsicOp := convertFFIOp ffiOp
      let retTy := intrinsicOp.fixedRetTy.getD nodeTy
      StateT.lift (LowerM.emitInst (.callIntrinsic intrinsicOp #[.local argVal] retTy) retTy)
    | some (Sum.inr externName) =>
      StateT.lift (LowerM.emitInst (.callExtern externName #[.local argVal] nodeTy) nodeTy)
    | none =>
      match fnPort with
      | none =>
        StateT.lift (LowerM.emitInst (.copy (.const .unit)) (.prim .unit))
      | some fp =>
        match graph.getNode fp.node with
        | none =>
          StateT.lift (LowerM.emitInst (.copy (.const .unit)) (.prim .unit))
        | some fnEntry =>
          match fnEntry.node with
          | .era =>
            StateT.lift (LowerM.emitInst (.copy (.const .unit)) (.prim .unit))
          | .lam _ =>
            lowerNodeWithMap graph fp.node funcIdMap
          | _ =>
            let fnNodeTy := getNodeType fnEntry
            if fnNodeTy == .prim .unit then
              StateT.lift (LowerM.emitInst (.copy (.const .unit)) (.prim .unit))
            else
              let fnVal ← lowerNodeWithMap graph fp.node funcIdMap
              StateT.lift (LowerM.emitInst (.callClosure (.local fnVal) #[.local argVal] nodeTy) nodeTy)

  | .ctor tag arity => do
    if tag == closureTag && arity == 2 then
      -- Closure CTOR: function reference at port 1, environment at port 2
      let fnPort ← match entry.getPort ⟨1⟩ with
        | some p => pure p
        | none =>
          let undef ← StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)
          return undef

      -- Resolve the function reference by following USE/DUP chains
      let canonRef := resolveCanonicalRef graph fnPort.node
      let funcRef ← match canonRef with
        | .bookRef refId =>
          pure (buildFuncRefFromBookRef graph refId (some funcIdMap))
        | .dynamicValue dynNodeId =>
          -- todo: consider panicking
          pure (FuncRef.external s!"$dynamic_closure_{dynNodeId.id}")

      let envVal ← match entry.getPort ⟨2⟩ with
        | some envPort => lowerOperandWithMap graph envPort funcIdMap
        | none => StateT.lift (LowerM.emitInst (.copy (.const (.null .rawPtr))) .rawPtr)

      StateT.lift (LowerM.emitInst (.makeClosure funcRef (.local envVal)) nodeTy)
    else
      -- Regular constructor: build tagged struct or struct literal
      let mut fieldVals : Array LocalId := #[]
      for i in [:arity] do
        let fieldVal ← lowerPort (i + 1)
        fieldVals := fieldVals.push fieldVal
      -- Check if target type is struct (for tuples/pairs) or tagged union (for ADTs)
      match nodeTy with
      | .struct _ =>
        -- Create struct literal, handling nested pair types
        StateT.lift (lowerNestedStructLit fieldVals nodeTy)
      | _ =>
        -- Create tagged union (for ADTs)
        StateT.lift (lowerCtor tag arity fieldVals nodeTy)

  | .proj fieldIdx => do
    let recordVal ← lowerPort 1
    let recordTy := getPortType 1
    -- Check if record is struct or tagged union
    match recordTy with
    | .struct fields =>
      -- Use extractField for struct types
      -- Compute the correct field type from the struct definition
      let fieldTy := if h : fieldIdx < fields.size then fields[fieldIdx].snd else nodeTy
      StateT.lift (LowerM.emitInst (.extractField (.local recordVal) fieldIdx) fieldTy)
    | _ =>
      -- Use getPayload for tagged unions
      StateT.lift (LowerM.emitInst (.getPayload (.local recordVal) 0 fieldIdx nodeTy) nodeTy)

  | .record numFields => do
    -- Record: check if target type is struct or tagged union
    let mut fieldVals : Array LocalId := #[]
    for i in [:numFields] do
      let fieldVal ← lowerPort (i + 1)
      fieldVals := fieldVals.push fieldVal
    match nodeTy with
    | .struct _ =>
      -- Create struct literal, handling nested pair types
      StateT.lift (lowerNestedStructLit fieldVals nodeTy)
    | _ =>
      -- Create tagged union with tag 0
      StateT.lift (lowerCtor 0 numFields fieldVals nodeTy)

  | .mat expectedTag => do
    let scrutineeVal ← lowerPort 1
    let (_, _thenBlock, elseBlock) ← StateT.lift (lowerMat expectedTag scrutineeVal)
    let cacheSnapshot ← do let ns ← get; pure ns.snapshotResults

    -- Lower hit value
    let hitVal ← lowerPort 2
    -- Record the actual block we're in after lowering the hit branch
    let hitBlock ← StateT.lift LowerM.getCurrentBlockId
    let joinBlock ← StateT.lift LowerM.freshBlockId
    StateT.lift (LowerM.finishBlock (.jump joinBlock) elseBlock)

    -- Restore cache
    modify fun ns => ns.restoreResults cacheSnapshot

    -- Lower miss value
    let missVal ← lowerPort 3
    -- Record the actual block we're in after lowering the miss branch
    let missBlock ← StateT.lift LowerM.getCurrentBlockId
    StateT.lift (LowerM.finishBlock (.jump joinBlock) joinBlock)

    -- Phi to merge results
    StateT.lift (LowerM.emitInst
      (.phi #[(Operand.local hitVal, hitBlock), (Operand.local missVal, missBlock)] nodeTy)
      nodeTy)

  | .op1 op => do
    let operandVal ← lowerPort 1
    StateT.lift (LowerM.emitInst (.unOp (convertUnOp op) (.local operandVal)) nodeTy)

  | .op2 op => do
    let lhsVal ← lowerPort 1
    let rhsVal ← lowerPort 2
    let binOp := convertBinOp op
    let opTy := if binOp.isComparison then getPortType 1 else nodeTy
    StateT.lift (LowerM.emitInst (.binOp binOp (.local lhsVal) (.local rhsVal) opTy) nodeTy)

  | .dup _ => do
    let inputVal ← lowerPort 0
    let copy0 ← StateT.lift (LowerM.emitInst (.clone (.local inputVal) nodeTy) nodeTy)
    let copy1 ← StateT.lift (LowerM.emitInst (.clone (.local inputVal) nodeTy) nodeTy)

    modify fun ns => { ns with
      results := ns.results.insert (nodeId.id * 1000 + 1) copy0
                 |>.insert (nodeId.id * 1000 + 2) copy1
    }
    pure inputVal

  | .sup _ =>
    StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

  | .ref refId | .alo refId => do
    -- Use centralized helper for consistent FuncRef resolution
    let funcRef := buildFuncRefFromBookRef graph refId (some funcIdMap)
    let nullEnv ← StateT.lift (LowerM.emitInst (.copy (.const (.null .rawPtr))) .rawPtr)
    StateT.lift (LowerM.emitInst (.makeClosure funcRef (.local nullEnv)) nodeTy)

  | .use => lowerPort 1

  | .array _ => do
    let _ ← lowerPort 1 (.prim .u64)
    lowerPort 2 .rawPtr

  | .string => do
    let len : Nat ← match entry.getPort ⟨1⟩ with
      | some lenPort =>
        match graph.getNode lenPort.node with
        | some lenEntry => match lenEntry.node with
          | .num _ val => pure val.toNat
          | _ => pure 0
        | none => pure 0
      | none => pure 0

    let stringIdx : Nat ← match entry.getPort ⟨2⟩ with
      | some idxPort =>
        match graph.getNode idxPort.node with
        | some idxEntry => match idxEntry.node with
          | .num _ val => pure val.toNat
          | _ => pure 0
        | none => pure 0
      | none => pure 0

    StateT.lift (lowerString stringIdx len)

  | .index => do
    let arrayVal ← lowerPort 1
    let indexVal ← lowerPort 2 (.prim .u64)

    let baseAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local arrayVal)) (.prim .i64))
    let offset8 ← StateT.lift (LowerM.emitInst (.copy (.const (.int 8 .i64))) (.prim .i64))
    let dataPtrAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offset8) (.prim .i64)) (.prim .i64))
    let dataPtrSlot ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local dataPtrAddr)) .rawPtr)
    let dataPtr ← StateT.lift (LowerM.emitInst (.load (.local dataPtrSlot) .rawPtr) .rawPtr)

    let elemSize ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat nodeTy.sizeBytes) .i64))) (.prim .i64))
    let offset ← StateT.lift (LowerM.emitInst (.binOp .mul (.local indexVal) (.local elemSize) (.prim .i64)) (.prim .i64))
    let dataAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local dataPtr)) (.prim .i64))
    let elemAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local dataAsI64) (.local offset) (.prim .i64)) (.prim .i64))
    let elemPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local elemAddr)) .rawPtr)
    StateT.lift (LowerM.emitInst (.load (.local elemPtr) nodeTy) nodeTy)

  | .slice =>
    StateT.lift (LowerM.emitInst (.copy (.const (.undef nodeTy))) nodeTy)

  modify fun ns => { ns with
    results := ns.results.insert nodeId.id result
    processing := ns.processing.erase nodeId.id
  }
  pure result

end

/-- Lower a definition with a FuncId map for resolving references -/
def lowerDefinitionWithMap (graph : CGraph) (def_ : CDefinition) (funcId : FuncId)
    (funcIdMap : FuncIdMap) : Func :=
  let sig := buildSignatureFromType def_.name def_.ty def_.arity
  let returnsUnit := sig.retTy == .prim .unit

  let (_, func) := LowerM.run' funcId sig do
    if def_.arity == 0 then
      let (result, _) ← StateT.run (lowerNodeWithMap graph def_.root funcIdMap) {}
      if returnsUnit then LowerM.terminate .retUnit
      else LowerM.terminate (.ret (.local result))
    else
      let (bodyNode, lamParams) := collectLamChain graph def_.root def_.arity
      let initState : NodeState := { lamParams }
      let (result, _) ← StateT.run (lowerNodeWithMap graph bodyNode funcIdMap) initState
      if returnsUnit then LowerM.terminate .retUnit
      else LowerM.terminate (.ret (.local result))

  func

/-- Lower an entire Circuit graph to an Alloy module -/
def lowerGraph (graph : CGraph) (moduleName : String := "main") : Module := Id.run do
  let mut module := Module.empty moduleName

  -- Copy string table from Circuit graph to Alloy module
  let circuitStrings := graph.getStringTable
  let mut stringTable := StringTable.empty
  for s in circuitStrings do
    let (_, st') := stringTable.intern s
    stringTable := st'
  module := { module with strings := stringTable }

  -- First pass: build mapping from Circuit book index to sequential Alloy FuncId
  let mut funcIdMap : FuncIdMap := {}
  let mut nextFuncId : Nat := 0
  for i in [:graph.book.size] do
    if let some def_ := graph.book[i]? then
      if not def_.name.isIntrinsic && not def_.isExternal then
        funcIdMap := funcIdMap.insert i (FuncId.mk nextFuncId)
        nextFuncId := nextFuncId + 1

  -- Second pass: lower definitions using the mapping
  for i in [:graph.book.size] do
    if let some def_ := graph.book[i]? then
      if not def_.name.isIntrinsic && not def_.isExternal then
        let funcId := funcIdMap.get? i |>.getD (FuncId.mk 0)
        let func := lowerDefinitionWithMap graph def_ funcId funcIdMap
        module := module.addFunc func

  -- Set main function using the mapped ID
  if let some (idx, _) := graph.findDefinitionByDisplay "main" then
    if let some mappedId := funcIdMap.get? idx then
      module := module.withMain mappedId

  module

def lower (graph : CGraph) (moduleName : String := "main") : Module :=
  lowerGraph graph moduleName

end Somac.Alloy.Lower
