/-
  Circuit IR to Alloy IR Lowering

  This pass transforms the interaction net representation (Circuit IR) into
  an imperative SSA representation (Alloy IR). The key transformations are:

  1. Nodes → Instructions: Each Circuit node becomes one or more Alloy instructions
  2. Wires → Values: Port connections become SSA value references
  3. DUP chains → Clone calls: Explicit duplication becomes clone operations
  4. Pattern matching → Switches: MAT chains become switch statements
  5. Closures → Struct + FnPtr: Lambda with captures becomes closure type
-/

import Somac.Alloy.Func
import Somac.Circuit.Graph
import Somac.Circuit.Node
import Soma.Core.Value
import Soma.Core.Eval
import Soma.Core.Intrinsic
import Soma.Core.Primitive
import Soma.Dependent.Monad
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

open Somac.Circuit.Term (Op1Code Op2Code Tag)
open Soma.Core (QualifiedName PrimOp FFIOp Intrinsic PrimType)


/-- Mapping from de Bruijn level to bounded type variable index -/
structure TyVarMapping (n : Nat) where
  map : Std.HashMap Nat (Fin n)
  deriving Inhabited

namespace TyVarMapping

def empty : TyVarMapping n := ⟨{}⟩

def get? (m : TyVarMapping n) (level : Nat) : Option (Fin n) :=
  m.map.get? level

def insert (m : TyVarMapping n) (level : Nat) (idx : Fin n) : TyVarMapping n :=
  ⟨m.map.insert level idx⟩

end TyVarMapping

/-- Registry mapping type Uniques to their primitive type representations -/
abbrev PrimTypeRegistry := Std.HashMap Soma.Unique PrimType

/-- Registry mapping function Uniques to their wired-in Alloy roles -/
abbrev WiredFuncRegistry := Std.HashMap Soma.Unique WiredFunc

/-- Convert a WiredRole to its Alloy-level WiredFunc, if it represents a function -/
private def wiredRoleToFunc? : Soma.Dependent.WiredRole → Option WiredFunc
  | .listMap => some .listMap
  | .listFilter => some .listFilter
  | .listFoldl => some .listFoldl
  | .listFoldr => some .listFoldr
  | .listSum => some .listSum
  | .listProduct => some .listProduct
  | .listLength => some .listLength
  | .listAny => some .listAny
  | .listAll => some .listAll
  | .listReverse => some .listReverse
  | _ => none

/-- Build a mapping from function Uniques to WiredFunc roles -/
def buildWiredFuncRegistry (wiredIn : Soma.Dependent.WiredIn) : WiredFuncRegistry :=
  wiredIn.roles.fold (init := {}) fun acc role infos =>
    match wiredRoleToFunc? role with
    | some wf => infos.foldl (init := acc) fun acc info =>
        acc.insert info.name.id wf
    | none => acc

/-- Check if a Core Value type is a List type via the primitive type registry -/
def isListValue (v : Soma.Core.Value) (primTypes : PrimTypeRegistry) : Bool :=
  match v with
  | .vDataType uid _ => primTypes.get? uid == some .list
  | _ => false

/-- Extract the element type parameter from a List Core Value type -/
def listElemValueType (v : Soma.Core.Value) (primTypes : PrimTypeRegistry) : Option Soma.Core.Value :=
  match v with
  | .vDataType uid params =>
    if primTypes.get? uid == some .list then params[0]?
    else none
  | _ => none

/-- Combined context for type conversion during Alloy lowering -/
structure TypeConvCtx (n : Nat) where
  tyVars : TyVarMapping n
  primTypes : PrimTypeRegistry
  inductives : Std.HashMap QualifiedName Soma.Dependent.InductiveMeta := {}
  deriving Inhabited

/-- Build the primitive type registry from the wired-in type registry -/
def buildPrimTypeRegistry (wiredIn : Soma.Dependent.WiredIn) : PrimTypeRegistry :=
  wiredIn.roles.fold (init := {}) fun acc role infos =>
    match Soma.Dependent.WiredRole.primType? role with
    | some prim => infos.foldl (init := acc) fun acc info =>
        acc.insert info.name.id prim
    | none => acc

/-- Mapping from Circuit node ports to Alloy local values -/
abbrev PortMap := Std.HashMap (Nat × Nat) LocalId

/-- Lowering state -/
structure LowerState (n : Nat) where
  /-- Current function being built -/
  func : Func n
  /-- Current block being built -/
  currentBlock : Block n
  /-- All completed blocks -/
  blocks : Array (Block n) := #[]
  /-- Port to value mapping -/
  portMap : PortMap := {}
  /-- Next block ID -/
  nextBlockId : Nat := 1
  /-- Intrinsic dispatch table from elaboration -/
  ctxIntrinsics : Std.HashMap QualifiedName Intrinsic := {}
  /-- String table index for panic message -/
  panicMsgIdx : Nat := 0

namespace LowerState

instance : Inhabited (LowerState n) where
  default := {
    func := default
    currentBlock := default
    blocks := #[]
    portMap := {}
    nextBlockId := 1
    ctxIntrinsics := {}
    panicMsgIdx := 0
  }

/-- Create initial state for a function -/
def init (funcId : FuncId) (sig : Signature n)
    (intrinsics : Std.HashMap QualifiedName Intrinsic := {})
    (panicMsgIdx : Nat := 0) : LowerState n :=
  let entry : Block n := { id := .entry, terminator := .unreachable }
  { func := Func.withBody funcId sig (CFG.withEntry entry)
  , currentBlock := entry
  , ctxIntrinsics := intrinsics
  , panicMsgIdx
  }

/-- Allocate a fresh local -/
def freshLocal (s : LowerState n) : LocalId × LowerState n :=
  let (id, func') := s.func.freshLocal
  (id, { s with func := func' })

/-- Allocate a fresh local with type -/
def freshLocalTyped (s : LowerState n) (ty : Ty n) : LocalId × LowerState n :=
  let (id, func') := s.func.freshLocalTyped ty
  (id, { s with func := func' })

/-- Allocate a fresh block ID -/
def freshBlockId (s : LowerState n) : BlockId × LowerState n :=
  (⟨s.nextBlockId⟩, { s with nextBlockId := s.nextBlockId + 1 })

/-- Add a statement to the current block -/
def emit (s : LowerState n) (stmt : Stmt n) : LowerState n :=
  { s with currentBlock := s.currentBlock.addStmt stmt }

/-- Emit instruction with result -/
def emitWithResult (s : LowerState n) (inst : Inst n) (ty : Ty n) : LocalId × LowerState n :=
  let (id, s') := s.freshLocalTyped ty
  let stmt := Stmt.withResult id inst
  (id, s'.emit stmt)

/-- Emit void instruction -/
def emitVoid (s : LowerState n) (inst : Inst n) : LowerState n :=
  s.emit (Stmt.void inst)

/-- Finish current block with a terminator and start a new one -/
def finishBlock (s : LowerState n) (term : Terminator) (nextId : BlockId) : LowerState n :=
  let finished := s.currentBlock.withTerminator term
  let newBlock : Block n := { id := nextId, terminator := .unreachable }
  { s with currentBlock := newBlock, blocks := s.blocks.push finished }

/-- Set terminator of current block (for final block) -/
def terminate (s : LowerState n) (term : Terminator) : LowerState n :=
  { s with currentBlock := s.currentBlock.withTerminator term }

/-- Register a port-to-value mapping -/
def bindPort (s : LowerState n) (port : CPortId) (val : LocalId) : LowerState n :=
  { s with portMap := s.portMap.insert (port.node.id, port.port.idx) val }

/-- Look up value for a port -/
def lookupPort (s : LowerState n) (port : CPortId) : Option LocalId :=
  s.portMap.get? (port.node.id, port.port.idx)

/-- Build the final CFG -/
def finalize (s : LowerState n) : Func n :=
  let allBlocks := s.blocks.push s.currentBlock
  let cfg : CFG n := {
    blocks := allBlocks.foldl (fun m b => m.insert b.id.id b) {}
    entry := .entry
    nextBlockId := s.nextBlockId
  }
  { s.func with body := some cfg }

end LowerState

/-- Lowering monad -/
abbrev LowerM (n : Nat) := StateM (LowerState n)

namespace LowerM

def run' (funcId : FuncId) (sig : Signature n)
    (intrinsics : Std.HashMap QualifiedName Intrinsic := {})
    (panicMsgIdx : Nat := 0)
    (m : LowerM n α) : α × Func n :=
  let (result, state) := Id.run (StateT.run m (LowerState.init funcId sig intrinsics panicMsgIdx))
  (result, state.finalize)

def freshLocal : LowerM n LocalId := do
  let s ← get
  let (id, s') := s.freshLocal
  set s'
  pure id

def freshLocalTyped (ty : Ty n) : LowerM n LocalId := do
  let s ← get
  let (id, s') := s.freshLocalTyped ty
  set s'
  pure id

def freshBlockId : LowerM n BlockId := do
  let s ← get
  let (id, s') := s.freshBlockId
  set s'
  pure id

def emit (stmt : Stmt n) : LowerM n Unit :=
  modify fun s => s.emit stmt

def emitInst (inst : Inst n) (ty : Ty n) : LowerM n LocalId := do
  let s ← get
  let (id, s') := s.emitWithResult inst ty
  set s'
  pure id

def emitVoid (inst : Inst n) : LowerM n Unit :=
  modify fun s => s.emitVoid inst

def finishBlock (term : Terminator) (nextId : BlockId) : LowerM n Unit :=
  modify fun s => s.finishBlock term nextId

def terminate (term : Terminator) : LowerM n Unit :=
  modify fun s => s.terminate term

def bindPort (port : CPortId) (val : LocalId) : LowerM n Unit :=
  modify fun s => s.bindPort port val

def lookupPort (port : CPortId) : LowerM n (Option LocalId) := do
  let s ← get
  pure (s.lookupPort port)

def getCurrentBlockId : LowerM n BlockId := do
  let s ← get
  pure s.currentBlock.id

/-- Emit a panic + undef fallback for unreachable lowering artifacts. -/
def emitPanic (ty : Ty n) (_reason : String := "unknown") : LowerM n LocalId := do
  let s ← get
  emitVoid (.panic s.panicMsgIdx 0)
  emitInst (.copy (.const (.undef ty.close))) ty

end LowerM

/-- Convert Circuit PrimType to Alloy PrimTy -/
def convertCircuitPrimType : Somac.Circuit.Term.PrimType → PrimTy
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
def convertUnOp : Op1Code → UnOp n
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
        -- USE returns its continuation (port 2), follow through
        match entry.getPort ⟨2⟩ with
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

/-- Resolve an intrinsic from a qualified name -/
private def resolveIntrinsic? (qn : QualifiedName)
    (ctxIntrinsics : Std.HashMap QualifiedName Intrinsic := {}) : Option Intrinsic :=
  ctxIntrinsics.get? qn

/-- Build a FuncRef from a book index, handling intrinsics and externals -/
def buildFuncRefFromBookRef (graph : CGraph) (refId : Nat)
    (funcIdMap : Option (Std.HashMap Nat FuncId) := none)
    (ctxIntrinsics : Std.HashMap QualifiedName Intrinsic := {}) : FuncRef :=
  match graph.getDefinition refId with
  | some def_ =>
    match resolveIntrinsic? def_.name ctxIntrinsics with
    | some (Intrinsic.ffiOp op) => .intrinsic (convertFFIOp op)
    | some (Intrinsic.extern name) => .externC name
    | some (Intrinsic.primOp op) =>
      match funcIdMap >>= (·.get? refId) with
      | some funcId => .local funcId
      | none => .primOp (convertCorePrimOp op)
    | some (Intrinsic.llvm name) => .externC name
    | some (Intrinsic.runtime fn) => .externC fn.name
    | none =>
      if def_.isExternal then
        .external def_.name.symbolName
      else
        match funcIdMap with
        | some map =>
          match map.get? refId with
          | some funcId => .local funcId
          | none => .external def_.name.symbolName
        | none =>
          .local (FuncId.mk refId)
  | none =>
    .external s!"unresolved_ref_{refId}"

/-- Result of collecting a chain of nested APP nodes -/
structure AppChainResult where
  /-- The base function node -/
  baseNodeId : CNodeId
  /-- The base function's node entry -/
  baseEntry : CNodeEntry
  /-- Argument ports in application order -/
  argPorts : Array CPortId
  /-- Node IDs of intermediate app nodes consumed by the chain (excludes the outermost) -/
  intermediateAppNodes : Array CNodeId

/-- Walk a chain of nested APP nodes to collect the base function and all arguments -/
partial def collectAppChain (graph : CGraph) (startEntry : CNodeEntry) : Option AppChainResult :=
  let rec go (currentEntry : CNodeEntry) (revArgs : Array CPortId)
      (intermediates : Array CNodeId) (fuel : Nat) : Option AppChainResult :=
    if fuel == 0 then none
    else do
      let fnPort ← currentEntry.getPort ⟨1⟩
      let fnEntry ← graph.getNode fnPort.node
      match fnEntry.node with
      | .app =>
        -- Another APP node in the chain: collect its arg and continue down
        let arg ← fnEntry.getPort ⟨2⟩
        go fnEntry (revArgs.push arg) (intermediates.push fnPort.node) (fuel - 1)
      | _ =>
        if revArgs.size >= 2 then
          some {
            baseNodeId := fnPort.node
            baseEntry := fnEntry
            argPorts := revArgs.reverse
            intermediateAppNodes := intermediates
          }
        else
          none
  do
    let outerArg ← startEntry.getPort ⟨2⟩
    go startEntry #[outerArg] #[] 100

open Soma.Core (Value)
open Soma.Unique

mutual

/-- Extract field types from a constructor's elaborated Pi type -/
partial def extractCtorFieldTypes (ty : Value) (ctx : TypeConvCtx n) : Array (Ty n) :=
  match ty with
  | Value.vPi _ _ _ dom cod =>
    if dom.isType then
      let neutralArg := Value.vNeutral (.vType .zero) (.nVar ⟨"_", ⟨0⟩⟩)
      extractCtorFieldTypes (cod.applyPure neutralArg) ctx
    else
      let fieldTy := convertValueTypeWithMapping dom ctx
      let neutralArg := Value.vNeutral (.vType .zero) (.nVar ⟨"_", ⟨0⟩⟩)
      #[fieldTy] ++ extractCtorFieldTypes (cod.applyPure neutralArg) ctx
  | _ => #[]

/-- Convert a PrimType to an Alloy Ty -/
partial def convertPrimToAlloyTy (prim : PrimType) (params : List Value) (ctx : TypeConvCtx n) : Ty n :=
  match prim with
  | .int => .prim .i32
  | .int64 => .prim .i64
  | .int16 => .prim .i16
  | .int8 => .prim .i8
  | .float => .prim .f32
  | .double => .prim .f64
  | .bool => .prim .bool
  | .string => Ty.string
  | .unit => .prim .unit
  | .closurePtr => .rawPtr
  | .word => .prim .u32
  | .word8 => .prim .u8
  | .word16 => .prim .u16
  | .word64 => .prim .u64
  | .world => .prim .unit
  | .list => .somaList
  | .array | .ref | .ptr => .rawPtr

/-- Extract variant information from a row type -/
partial def extractRowVariantsWithMapping (row : Value) (ctx : TypeConvCtx n)
    (idx : Nat := 0) (acc : Array (Nat × Array (Ty n)) := #[]) : Array (Nat × Array (Ty n)) :=
  match row with
  | Value.vRowEmpty => acc
  | Value.vRowExtend _label fieldTy tail =>
    let fields := match fieldTy with
      | Value.vPrimTy (.unit) => #[]
      | Value.vSigma _ _ fst sndClos =>
        let fstTy := convertValueTypeWithMapping fst ctx
        let sndTy := match sndClos with
          | .const _ v => convertValueTypeWithMapping v ctx
          | _ => .prim .i64
        #[fstTy, sndTy]
      | Value.vPair fst snd =>
        #[convertValueTypeWithMapping fst ctx, convertValueTypeWithMapping snd ctx]
      | other => #[convertValueTypeWithMapping other ctx]
    extractRowVariantsWithMapping tail ctx (idx + 1) (acc.push (idx, fields))
  | _ => acc

/-- Convert a Soma Value type to an Alloy Ty -/
partial def convertValueTypeWithMapping (val : Value) (ctx : TypeConvCtx n) : Ty n :=
  match val with
  | Value.vPrimTy prim => convertPrimToAlloyTy prim [] ctx

  | Value.vPi _ _ name dom cod =>
    let domTy := convertValueTypeWithMapping dom ctx
    let neutralArg := Value.vNeutral (.vType .zero) (.nVar ⟨name, ⟨0⟩⟩)
    let codResult := cod.applyPure neutralArg
    let codTy := convertValueTypeWithMapping codResult ctx
    .closure #[domTy] codTy
  | Value.vLam _ _ => .closure #[] .rawPtr
  | Value.vSigma _ name fst sndClos =>
    let neutralArg := Value.vNeutral (.vType .zero) (.nVar ⟨name, ⟨0⟩⟩)
    let sndResult := sndClos.applyPure neutralArg
    let sndTy := convertValueTypeWithMapping sndResult ctx
    .struct #[("fst", convertValueTypeWithMapping fst ctx), ("snd", sndTy)]
  | Value.vPair fst snd =>
    .struct #[("fst", convertValueTypeWithMapping fst ctx),
              ("snd", convertValueTypeWithMapping snd ctx)]
  | Value.vDataType dId params =>
    match ctx.primTypes.get? dId with
    | some prim => convertPrimToAlloyTy prim params ctx
    | none =>
      match ctx.inductives.get? ⟨dId⟩ with
      | some indInfo =>
        if indInfo.kind == .record && indInfo.ctors.size == 1 then
          -- Record type (single constructor): produce flat struct with named fields
          let ctor := indInfo.ctors[0]!
          let fields := extractCtorFieldTypes ctor.type ctx
          let fieldNames := indInfo.fieldNames
          let namedFields := fields.mapIdx fun i ty =>
            let name := if h : i < fieldNames.size then fieldNames[i] else s!"field{i}"
            (name, ty)
          .struct namedFields
        else
          let variants := indInfo.ctors.map fun ctor =>
            let fields := extractCtorFieldTypes ctor.type ctx
            (ctor.tag, fields)
          .tagged (.prim .u32) variants
      | none => .tagged (.prim .u32) #[]
  | Value.vConstructor _ _ _ _ => .rawPtr
  | Value.vRecord _ => .rawPtr
  | Value.vRecordVal _ => .rawPtr
  | Value.vVariant row => .tagged (.prim .u32) (extractRowVariantsWithMapping row ctx)
  | Value.vType _ => .rawPtr
  | Value.vNeutral _ neu =>
    match neu with
    | .nVar v =>
      match ctx.tyVars.get? v.level.lvl with
      | some idx => .var idx
      | none => .rawPtr
    | .nMeta m =>
      match ctx.tyVars.get? m.id with
      | some idx => .var idx
      | none => .rawPtr
    | _ => .rawPtr
  | Value.vLabelLit _ => .rawPtr
  | Value.vRowSort => .rawPtr
  | Value.vLabelSort => .rawPtr
  | Value.vRowEmpty => .rawPtr
  | Value.vRowExtend _ _ _ => .rawPtr
  | Value.vEq _ _ _ _ => .rawPtr
  | Value.vRefl _ _ => .rawPtr
  | Value.vTransport _ _ _ _ _ _ _ => .rawPtr
  | Value.vIntLit _ => .prim .i32
  | Value.vFloatLit _ => .prim .f64
  | Value.vStringLit _ => Ty.string

end


mutual

/-- Collect all de Bruijn levels from a Neutral term -/
partial def collectTyVarLevelsNeutral (neu : Soma.Core.Neutral) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
  match neu with
  | .nVar v => acc.insert v.level.lvl
  | .nMeta m => acc.insert m.id
  | .nApp fn arg => collectTyVarLevels arg (collectTyVarLevelsNeutral fn acc)
  | .nFst pair => collectTyVarLevelsNeutral pair acc
  | .nSnd pair => collectTyVarLevelsNeutral pair acc
  | .nFieldAccess record _ => collectTyVarLevelsNeutral record acc
  | .nConst _ _ => acc
  | .nCase scrutinee _ _ => collectTyVarLevelsNeutral scrutinee acc

/-- Collect all de Bruijn levels of type variables appearing in a Value -/
partial def collectTyVarLevels (val : Value) (acc : Std.HashSet Nat := {}) : Std.HashSet Nat :=
  match val with
  | Value.vNeutral _ neu => collectTyVarLevelsNeutral neu acc
  | Value.vPi _ _ name dom cod =>
    let acc' := collectTyVarLevels dom acc
    match cod with
    | .const _ body => collectTyVarLevels body acc'
    | .term _ _ _ =>
      let dummyArg := Value.vNeutral dom (.nVar ⟨name, cod.env.level⟩)
      let nextTy := cod.applyPure dummyArg
      collectTyVarLevels nextTy acc'
  | Value.vSigma _ name fst sndClos =>
    let acc' := collectTyVarLevels fst acc
    match sndClos with
    | .const _ body => collectTyVarLevels body acc'
    | .term _ _ _ =>
      let dummyArg := Value.vNeutral fst (.nVar ⟨name, sndClos.env.level⟩)
      let nextTy := sndClos.applyPure dummyArg
      collectTyVarLevels nextTy acc'
  | Value.vPair fst snd =>
    collectTyVarLevels snd (collectTyVarLevels fst acc)
  | Value.vDataType _ params =>
    params.foldl (fun a p => collectTyVarLevels p a) acc
  | Value.vVariant row => collectTyVarLevels row acc
  | Value.vRowExtend _ fieldTy tail =>
    collectTyVarLevels tail (collectTyVarLevels fieldTy acc)
  | Value.vEq _ ty lhs rhs =>
    collectTyVarLevels rhs (collectTyVarLevels lhs (collectTyVarLevels ty acc))
  | Value.vTransport _ ty motive lhs rhs eq body =>
    let acc' := collectTyVarLevels ty acc
    let acc' := collectTyVarLevels motive acc'
    let acc' := collectTyVarLevels lhs acc'
    let acc' := collectTyVarLevels rhs acc'
    let acc' := collectTyVarLevels eq acc'
    collectTyVarLevels body acc'
  | _ => acc

end

/-- Advance a Closure codomain by substituting a neutral dummy argument -/
private partial def advanceCodomain (cod : Soma.Core.Closure) (dom : Value) : Value :=
  match cod with
  | .const _ body => body
  | .term name _ _ =>
    let dummyArg := Value.vNeutral dom (.nVar ⟨name, cod.env.level⟩)
    cod.applyPure dummyArg

/-- Strip all leading implicit type parameters (∀ a : Type) from a Value type -/
private partial def stripLeadingImplicits (val : Value) : Value :=
  match val with
  | Value.vPi _ binder _ dom cod =>
    if binder.isImplicit && dom.isType then
      stripLeadingImplicits (advanceCodomain cod dom)
    else val
  | _ => val

mutual
/-- Structurally match a polymorphic Value type against a concrete Value type -/
partial def matchTypeStructural (poly concrete : Value)
    (levels : Std.HashSet Nat) (bindings : Std.HashMap Nat Value) : Std.HashMap Nat Value :=
  match poly with
  | Value.vNeutral _ (.nVar v) =>
    if levels.contains v.level.lvl then bindings.insert v.level.lvl concrete
    else bindings
  | Value.vNeutral _ (.nMeta m) =>
    if levels.contains m.id then bindings.insert m.id concrete
    else bindings
  | Value.vPi _ _ _ dom1 cod1 =>
    match concrete with
    | Value.vPi _ _ _ dom2 cod2 =>
      let bindings' := matchTypeStructural dom1 dom2 levels bindings
      let next1 := advanceCodomain cod1 dom1
      let next2 := advanceCodomain cod2 dom2
      matchTypeStructural next1 next2 levels bindings'
    | _ => bindings
  | Value.vDataType id1 params1 =>
    match concrete with
    | Value.vDataType id2 params2 =>
      if id1 == id2 then
        (params1.zip params2).foldl (fun acc (p, c) =>
          matchTypeStructural p c levels acc) bindings
      else bindings
    | _ => bindings
  | Value.vSigma _ _ fst1 sndClos1 =>
    match concrete with
    | Value.vSigma _ _ fst2 sndClos2 =>
      let bindings' := matchTypeStructural fst1 fst2 levels bindings
      let snd1 := advanceCodomain sndClos1 fst1
      let snd2 := advanceCodomain sndClos2 fst2
      matchTypeStructural snd1 snd2 levels bindings'
    | _ => bindings
  | _ => bindings

/-- Match a polymorphic function type against a concrete function type -/
partial def matchPolyAgainstConcrete (poly concrete : Value)
    (levels : Std.HashSet Nat) (bindings : Std.HashMap Nat Value) : Std.HashMap Nat Value :=
  let poly := stripLeadingImplicits poly
  let concrete := stripLeadingImplicits concrete
  matchTypeStructural poly concrete levels bindings
end

/-- Collect all tyVar levels from all reachable nodes in a definition's graph -/
def collectAllTyVarLevels (graph : CGraph) (def_ : CDefinition) : Std.HashSet Nat := Id.run do
  let mut levels := collectTyVarLevels def_.ty

  let mut visited : Std.HashSet Nat := {}
  let mut queue : Array CNodeId := #[def_.root]

  while !queue.isEmpty do
    let nodeId := queue.back!
    queue := queue.pop

    if visited.contains nodeId.id then
      continue
    visited := visited.insert nodeId.id

    match graph.getNode nodeId with
    | some entry =>
      levels := collectTyVarLevels entry.ty levels

      for conn in entry.connections do
        let (_, targetPort) := conn
        if !visited.contains targetPort.node.id then
          queue := queue.push targetPort.node
    | none => pure ()

  levels

/-- Build a type variable mapping from collected levels -/
def buildTyVarMapping (levels : Std.HashSet Nat) : Σ n, TyVarMapping n :=
  let sortedLevels := levels.toArray.qsort (· < ·)
  let n := sortedLevels.size
  let map := sortedLevels.foldl (init := (({} : Std.HashMap Nat (Fin n)), 0)) fun (acc, i) lvl =>
    if h : i < n then
      (acc.insert lvl ⟨i, h⟩, i + 1)
    else
      (acc, i) -- impossible
  ⟨n, ⟨map.1⟩⟩

/-- Build tyVar mapping from an entire definition -/
def buildTyVarMappingFromDefinition (_graph : CGraph) (def_ : CDefinition) : Σ n, TyVarMapping n :=
  let defLevels := collectTyVarLevels def_.ty
  buildTyVarMapping defLevels

/-- Extract type arguments for a call to a polymorphic function -/
partial def extractCallTypeArgs (defTy : Value) (concreteTy : Value)
    (ctx : TypeConvCtx n) : Option (Array (Ty n)) :=
  let levels := collectTyVarLevels defTy
  if levels.isEmpty then none
  else
    let bindings := matchPolyAgainstConcrete defTy concreteTy levels {}
    let sortedLevels := levels.toArray.qsort (· < ·)
    let typeArgs := sortedLevels.map fun level =>
      match bindings.get? level with
      | some val => convertValueTypeWithMapping val ctx
      | none => .rawPtr
    some typeArgs

/-- Match explicit parameter types of a polymorphic definition against concrete argument types -/
private partial def countLeadingImplicits (ty : Value) : Nat :=
  match ty with
  | Value.vPi _ binder _ dom cod =>
    if binder.isImplicit && dom.isType then
      1 + countLeadingImplicits (advanceCodomain cod dom)
    else 0
  | _ => 0

private partial def matchExplicitParamsGo (ty : Value) (args : Array Value) (idx : Nat)
    (retTy : Option Value) (levels : Std.HashSet Nat) (bindings : Std.HashMap Nat Value)
    : Std.HashMap Nat Value :=
  if idx >= args.size then
    match retTy with
    | some ret => matchTypeStructural ty ret levels bindings
    | none => bindings
  else
    match ty with
    | Value.vPi _ _ _ dom cod =>
      let bindings' := matchTypeStructural dom args[idx]! levels bindings
      let next := advanceCodomain cod dom
      matchExplicitParamsGo next args (idx + 1) retTy levels bindings'
    | _ => bindings

partial def matchParamsAgainstArgs (defTy : Value) (argTypes : Array Value) (returnTy : Option Value)
    (levels : Std.HashSet Nat) : Std.HashMap Nat Value :=
  let numImplicits := countLeadingImplicits defTy
  let stripped := stripLeadingImplicits defTy
  -- Pick the alignment that produces the most bindings
  Id.run do
    let mut bestBindings : Std.HashMap Nat Value := {}
    for skip in List.range (numImplicits + 1) do
      if skip ≤ argTypes.size then
        let explicitArgs := argTypes.extract skip argTypes.size
        let bindings := matchExplicitParamsGo stripped explicitArgs 0 returnTy levels {}
        pure ()
        if bindings.size > bestBindings.size then
          bestBindings := bindings
    return bestBindings

/-- Convert resolved type arg Values (from the elaborator) to Alloy Ty -/
private partial def bindResolvedArgsGo (ty : Value) (args : Array Value) (idx : Nat)
    (levels : Std.HashSet Nat) (bindings : Std.HashMap Nat Value)
    : Std.HashMap Nat Value :=
  if idx >= args.size then bindings
  else
    match ty with
    | Value.vPi _ binder _ dom cod =>
      if binder.isImplicit && dom.isType then
        let next := advanceCodomain cod dom
        let lvl := cod.env.level
        let bindings' := if levels.contains lvl.lvl then
          bindings.insert lvl.lvl args[idx]!
        else bindings
        bindResolvedArgsGo next args (idx + 1) levels bindings'
      else bindings
    | _ => bindings

partial def convertResolvedTypeArgs (resolvedArgs : Array Value) (defTy : Value)
    (ctx : TypeConvCtx n) : Option (Array (Ty n)) :=
  let levels := collectTyVarLevels defTy
  if levels.isEmpty then none
  else
    let sortedLevels := levels.toArray.qsort (· < ·)
    let bindings := bindResolvedArgsGo defTy resolvedArgs 0 levels {}
    let typeArgs := sortedLevels.map fun level =>
      match bindings.get? level with
      | some val => convertValueTypeWithMapping val ctx
      | none => .rawPtr
    if typeArgs.any (· != .rawPtr) then some typeArgs
    else none

/-- Extract type arguments by matching the definition's parameter types against
    the concrete argument types from an APP chain -/
partial def extractCallTypeArgsFromArgs (defTy : Value) (argTypes : Array Value)
    (returnTy : Value) (fallbackConcreteTy : Value)
    (ctx : TypeConvCtx n) : Option (Array (Ty n)) :=
  let levels := collectTyVarLevels defTy
  if levels.isEmpty then none
  else
    let bindings := matchParamsAgainstArgs defTy argTypes (some returnTy) levels
    let sortedLevels := levels.toArray.qsort (· < ·)
    let hasUseful := sortedLevels.any fun level => bindings.contains level
    let finalBindings :=
      if hasUseful then bindings
      else
        matchPolyAgainstConcrete defTy fallbackConcreteTy levels {}
    let typeArgs := sortedLevels.map fun level =>
      match finalBindings.get? level with
      | some val => convertValueTypeWithMapping val ctx
      | none => .rawPtr
    some typeArgs

/-- Extract type parameter names and value parameters using a type conversion context -/
partial def extractParamsUsingMapping (ty : Value) (ctx : TypeConvCtx n)
    (typeAcc : Array String := #[]) (valAcc : Array (String × Ty n) := #[])
    : Array String × Array (String × Ty n) :=
  match ty with
  | Value.vPi _ binder name dom cod =>
    let isTypeParam := binder.isImplicit && dom.isType
    match cod with
    | .const _ nextTy =>
      if isTypeParam then
        extractParamsUsingMapping nextTy ctx (typeAcc.push name) valAcc
      else
        let paramTy := convertValueTypeWithMapping dom ctx
        extractParamsUsingMapping nextTy ctx typeAcc (valAcc.push (name, paramTy))
    | .term _ _ _ =>
      -- Evaluate the dependent codomain with a neutral argument to continue traversal
      let dummyArg := Value.vNeutral dom (.nVar ⟨name, cod.env.level⟩)
      let nextTy := cod.applyPure dummyArg
      if isTypeParam then
        extractParamsUsingMapping nextTy ctx (typeAcc.push name) valAcc
      else
        let paramTy := convertValueTypeWithMapping dom ctx
        extractParamsUsingMapping nextTy ctx typeAcc (valAcc.push (name, paramTy))
  | _ => (typeAcc, valAcc)

/-- Extract the return type from a function type (Pi chain) -/
partial def extractReturnTypeWithMapping (ty : Value) (ctx : TypeConvCtx n) : Ty n :=
  match ty with
  | Value.vPi _ _ _ dom cod =>
    match cod with
    | .const _ nextTy => extractReturnTypeWithMapping nextTy ctx
    | .term name _ _ =>
      -- Evaluate the dependent codomain with a neutral argument to extract actual return type
      let dummyArg := Value.vNeutral dom (.nVar ⟨name, cod.env.level⟩)
      let nextTy := cod.applyPure dummyArg
      extractReturnTypeWithMapping nextTy ctx
  | other => convertValueTypeWithMapping other ctx

/-- Build function signature from a Value type with known type parameter count -/
def buildSignatureFromType (name : QualifiedName) (ty : Value) (arity : Nat)
    (ctx : TypeConvCtx n) (numTypeParams : Nat) : Signature n :=
  let (explicitTypeParams, paramInfos) := extractParamsUsingMapping ty ctx
  let typeParamNames := if explicitTypeParams.size >= numTypeParams then
      explicitTypeParams.extract 0 numTypeParams
    else
      let extra := (List.range (numTypeParams - explicitTypeParams.size)).toArray.map fun i =>
        s!"T{explicitTypeParams.size + i}"
      explicitTypeParams ++ extra
  let defaultTy : Ty n := .prim .i64
  let params := (List.range arity).toArray.map fun i =>
    if h : i < paramInfos.size then
      let (pname, pty) := paramInfos[i]
      { id := ⟨i⟩, name := pname, ty := pty : Param n }
    else { id := ⟨i⟩, name := s!"arg{i}", ty := defaultTy : Param n }
  let retTy := extractReturnTypeWithMapping ty ctx
  { name := name.symbolName, typeParamNames, params, retTy }

/-- Get node type with type conversion context -/
def getNodeTypeWithMapping (entry : CNodeEntry) (ctx : TypeConvCtx n) : Ty n :=
  convertValueTypeWithMapping entry.ty ctx

/-- The generic value type used at runtime -/
def valueType : Ty n := .prim .i64

/-- Type for constructor tag -/
def tagType : Ty n := .prim .u32

/-- Type for closure (fn ptr + env ptr) -/
def closureType : Ty n := .struct #[("fn", .rawPtr), ("env", .rawPtr)]

/-- Reserved tag for closure CTORs in Circuit IR -/
def closureTag : Nat := 0xFFFE

/-- Reserved tag for panic CTORs in Circuit IR -/
def panicTag : Nat := 0xFFFF

/-- NODE_FLAT_ARRAY tag value -/
def flatArrayTag : Nat := 4

/-- NODE_FLAT_ARRAY_VIEW tag value -/
def flatArrayViewTag : Nat := 5

/-- Size of the flat array backing header in bytes -/
def flatArrayHeaderSize : Nat := 16

/-- Alloy struct type for flat array backing header: { i64 header, i64 length } -/
def flatArrayHeaderStructTy : Ty n := .struct #[("header", .prim .i64), ("length", .prim .i64)]

/-- Alloy struct type for flat array view: { i64 header, i64 length, ptr data, ptr backing } -/
def viewStructTy : Ty n := .struct #[
  ("header", .prim .i64), ("length", .prim .i64),
  ("data", .rawPtr), ("backing", .rawPtr)]

/-- Emit the 8-byte flat array backing header: tag=4, elem_size, pad, reserved=0 -/
def emitFlatArrayHeader (bufPtr : LocalId) (elemSizeBytes : Nat) : LowerM n Unit := do
  let headerVal : Nat := flatArrayTag + (elemSizeBytes <<< 8)
  let hdr ← LowerM.emitInst (.copy (.const (.int (Int.ofNat headerVal) .i64))) (.prim .i64)
  let hdrFieldPtr ← LowerM.emitInst (.getFieldPtr (.local bufPtr) 0 flatArrayHeaderStructTy) (.ptr (.prim .i64))
  LowerM.emitVoid (.store (.local hdrFieldPtr) (.local hdr))

/-- Get a pointer to the data region of a flat array (past the header) -/
def emitFlatArrayDataPtr (bufPtr : LocalId) : LowerM n LocalId :=
  LowerM.emitInst (.getElemPtr (.local bufPtr) (.const (.int 1 .i64)) flatArrayHeaderStructTy) (.ptr flatArrayHeaderStructTy)

/-- Store the length field of a flat array backing header -/
def emitStoreFlatArrayLength (bufPtr : LocalId) (len : LocalId) : LowerM n Unit := do
  let lenFieldPtr ← LowerM.emitInst (.getFieldPtr (.local bufPtr) 1 flatArrayHeaderStructTy) (.ptr (.prim .i64))
  LowerM.emitVoid (.store (.local lenFieldPtr) (.local len))

/-- Emit a complete view struct: allocate 32 bytes, write header, length, data ptr, backing ptr -/
def emitAllocView (length : LocalId) (dataPtr : LocalId) (backingPtr : LocalId)
    : LowerM n LocalId := do
  let view ← LowerM.emitInst (.callExtern "soma_alloc_view" #[] .rawPtr) .rawPtr
  -- Store header (field 0)
  let headerVal : Nat := flatArrayViewTag
  let hdr ← LowerM.emitInst (.copy (.const (.int (Int.ofNat headerVal) .i64))) (.prim .i64)
  let hdrFieldPtr ← LowerM.emitInst (.getFieldPtr (.local view) 0 viewStructTy) (.ptr (.prim .i64))
  LowerM.emitVoid (.store (.local hdrFieldPtr) (.local hdr))
  -- Store length (field 1)
  let lenFieldPtr ← LowerM.emitInst (.getFieldPtr (.local view) 1 viewStructTy) (.ptr (.prim .i64))
  LowerM.emitVoid (.store (.local lenFieldPtr) (.local length))
  -- Store data pointer (field 2)
  let dataFieldPtr ← LowerM.emitInst (.getFieldPtr (.local view) 2 viewStructTy) (.ptr .rawPtr)
  LowerM.emitVoid (.store (.local dataFieldPtr) (.local dataPtr))
  -- Store backing pointer (field 3)
  let backFieldPtr ← LowerM.emitInst (.getFieldPtr (.local view) 3 viewStructTy) (.ptr .rawPtr)
  LowerM.emitVoid (.store (.local backFieldPtr) (.local backingPtr))
  pure view

/-- Load the length field from a view (field 1) -/
def emitLoadViewLength (viewPtr : LocalId) : LowerM n LocalId := do
  let lenFieldPtr ← LowerM.emitInst (.getFieldPtr (.local viewPtr) 1 viewStructTy) (.ptr (.prim .i64))
  LowerM.emitInst (.load (.local lenFieldPtr) (.prim .i64)) (.prim .i64)

/-- Load the data pointer from a view (field 2) -/
def emitLoadViewData (viewPtr : LocalId) : LowerM n LocalId := do
  let dataFieldPtr ← LowerM.emitInst (.getFieldPtr (.local viewPtr) 2 viewStructTy) (.ptr .rawPtr)
  LowerM.emitInst (.load (.local dataFieldPtr) .rawPtr) .rawPtr

/-- Load the backing pointer from a view (field 3) -/
def emitLoadViewBacking (viewPtr : LocalId) : LowerM n LocalId := do
  let backFieldPtr ← LowerM.emitInst (.getFieldPtr (.local viewPtr) 3 viewStructTy) (.ptr .rawPtr)
  LowerM.emitInst (.load (.local backFieldPtr) .rawPtr) .rawPtr

def emitStoreViewBacking (viewPtr : LocalId) (newBackingPtr : LocalId) : LowerM n Unit := do
  let backFieldPtr ← LowerM.emitInst (.getFieldPtr (.local viewPtr) 3 viewStructTy) (.ptr .rawPtr)
  LowerM.emitVoid (.store (.local backFieldPtr) (.local newBackingPtr))

/-- Default element size for lists when element type is unknown (pointer-sized) -/
def defaultElemSize (ptrBytes : Nat) : Nat := ptrBytes

/-- Get the element size in bytes for a list element type -/
def listElemSize (elemTy : Ty n) (ptrBytes : Nat) : Nat :=
  let sz := elemTy.sizeBytes ptrBytes
  if sz == 0 then defaultElemSize ptrBytes else sz

/-- Extract the list element size from a Core Value type -/
partial def listElemSizeFromValueType (valTy : Value) (ctx : TypeConvCtx n) (ptrBytes : Nat) : Nat :=
  match listElemValueType valTy ctx.primTypes with
  | some elemVal =>
    let elemTy := convertValueTypeWithMapping elemVal ctx
    listElemSize elemTy ptrBytes
  | none => defaultElemSize ptrBytes

/-- State maintained during graph traversal -/
structure NodeState (n : Nat) where
  /-- Nodes currently being processed (for cycle detection) -/
  processing : Std.HashSet Nat := {}
  /-- Cached results for nodes (principal port values) -/
  results : Std.HashMap Nat LocalId := {}
  /-- LAM node ID → parameter index mapping -/
  lamParams : Std.HashMap Nat Nat := {}
  /-- Type variable level → index mapping -/
  tyVarMapping : TyVarMapping n
  /-- Primitive type registry for resolving wired-in types -/
  primTypes : PrimTypeRegistry := {}
  /-- Inductive metadata for resolving ADT variant info -/
  inductives : Std.HashMap QualifiedName Soma.Dependent.InductiveMeta := {}
  /-- Expected result type from the consumer context -/
  expectedResultTy : Option (Ty n) := none
  /-- LocalIds known to hold list-typed (flat array) values -/
  listTypedLocals : Std.HashSet Nat := {}
  /-- Anonymous LAM node ID → graph book index mapping -/
  anonLamBookIdx : Std.HashMap Nat Nat := {}
  /-- Target pointer width in bytes -/
  ptrBytes : Nat := 8
  deriving Inhabited

namespace NodeState

def snapshotResults (s : NodeState n) : Std.HashMap Nat LocalId := s.results

def restoreResults (s : NodeState n) (snapshot : Std.HashMap Nat LocalId) : NodeState n :=
  { s with results := snapshot }

/-- Build a type conversion context from this node state -/
def toTypeConvCtx (s : NodeState n) : TypeConvCtx n :=
  { tyVars := s.tyVarMapping, primTypes := s.primTypes, inductives := s.inductives }

end NodeState

/-- Lower a numeric literal -/
def lowerNum (primTy : Somac.Circuit.Term.PrimType) (val : UInt32) : LowerM n LocalId := do
  let ty : Ty n := Ty.prim (convertCircuitPrimType primTy)
  let intVal : Int :=
    if primTy.toUInt8 >= 4 && primTy.toUInt8 <= 7 then
      let v := val.toNat
      if v >= 0x80000000 then Int.negOfNat (0x100000000 - v) else Int.ofNat v
    else Int.ofNat val.toNat
  LowerM.emitInst (.copy (.const (.int intVal (convertCircuitPrimType primTy)))) ty

/-- Lower a constructor (creates a tagged struct on the heap) -/
def lowerCtor (tag : Nat) (_arity : Nat) (fieldVals : Array LocalId) (ty : Ty n) : LowerM n LocalId := do
  let payload := fieldVals.map fun id => Operand.local id
  let taggedTy : Ty n := match ty with
    | .tagged _ _ => ty
    | _ => .tagged (.prim .u32) #[]
  LowerM.emitInst (.taggedLit tag payload taggedTy) taggedTy

/-- Build a nested struct literal for nested pair types -/
partial def lowerNestedStructLit (fieldVals : Array LocalId) (ty : Ty n) : LowerM n LocalId := do
  match ty with
  | .struct fields =>
    if fields.size == 2 then
      -- Check if second field is also a struct (nested pair)
      let sndTy := fields[1]?.map (·.snd)
      match sndTy with
      | some (Ty.struct innerFields) =>
        if innerFields.size >= 2 && fieldVals.size > 2 then
          let innerTy : Ty n := Ty.struct innerFields
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
      -- todo: consider panicking?
      LowerM.emitInst (.copy (.const (.null .rawPtr))) .rawPtr

/-- Lower tag extraction for pattern matching -/
def lowerGetTag (scrutinee : LocalId) : LowerM n LocalId := do
  LowerM.emitInst (.getTag (.local scrutinee)) tagType

/-- Lower a pattern match (MAT node) -/
def lowerMat (expectedTag : Nat) (scrutinee : LocalId) : LowerM n (LocalId × BlockId × BlockId) := do
  let tag ← lowerGetTag scrutinee
  let expected ← LowerM.emitInst (.copy (.const (.int (Int.ofNat expectedTag) .u32))) tagType
  let cond ← LowerM.emitInst (.binOp .eq (.local tag) (.local expected) tagType) Ty.bool

  let thenBlock ← LowerM.freshBlockId
  let elseBlock ← LowerM.freshBlockId

  LowerM.finishBlock (.branch (.local cond) thenBlock elseBlock) thenBlock

  pure (cond, thenBlock, elseBlock)

/-- Lower a string literal to a fat pointer constant { ptr data, i64 len } -/
def lowerString (stringIdx : Nat) (len : Nat) : LowerM n LocalId := do
  LowerM.emitInst (.copy (.const (.string stringIdx len))) Ty.string

/-- Mapping from Circuit book index to Alloy FuncId -/
abbrev FuncIdMap := Std.HashMap Nat FuncId

mutual

/-- Emit inline field-by-field DUP for types where `canInlineDup` is true.
    Recursively extracts struct fields, copies each one, and reassembles
    two new struct values. Only called for structs of all-flat fields. -/
partial def emitInlineDup (inputVal : LocalId) (ty : Ty n)
    : StateT (NodeState n) (LowerM n) (LocalId × LocalId) := do
  match ty with
  | .struct fields =>
    let mut fields0 : Array Operand := #[]
    let mut fields1 : Array Operand := #[]
    for i in [:fields.size] do
      if h : i < fields.size then
        let (_, fieldTy) := fields[i]
        let fieldVal ← StateT.lift (LowerM.emitInst (.extractField (.local inputVal) i) fieldTy)
        -- All fields are flat (canInlineDup guarantees this), so just copy
        let c0 ← StateT.lift (LowerM.emitInst (.copy (.local fieldVal)) fieldTy)
        let c1 ← StateT.lift (LowerM.emitInst (.copy (.local fieldVal)) fieldTy)
        fields0 := fields0.push (.local c0)
        fields1 := fields1.push (.local c1)
    let struct0 ← StateT.lift (LowerM.emitInst (.structLit fields0 ty) ty)
    let struct1 ← StateT.lift (LowerM.emitInst (.structLit fields1 ty) ty)
    pure (struct0, struct1)
  | .array elem sz =>
    -- Array of flat elements: copy is trivial (the array value itself is flat)
    let c0 ← StateT.lift (LowerM.emitInst (.copy (.local inputVal)) ty)
    let c1 ← StateT.lift (LowerM.emitInst (.copy (.local inputVal)) ty)
    pure (c0, c1)
  | _ =>
    -- Flat primitive or funcPtr: direct register copy
    let c0 ← StateT.lift (LowerM.emitInst (.copy (.local inputVal)) ty)
    let c1 ← StateT.lift (LowerM.emitInst (.copy (.local inputVal)) ty)
    pure (c0, c1)

/-- Emit eager, type-directed String duplication -/
partial def emitStringDup (inputVal : LocalId) : StateT (NodeState n) (LowerM n) (LocalId × LocalId) := do
  let cstr1 ← StateT.lift (LowerM.emitInst (.callIntrinsic .toCString #[.local inputVal] .rawPtr) .rawPtr)
  let copy1 ← StateT.lift (LowerM.emitInst (.callIntrinsic .fromCString #[.local cstr1] Ty.string) Ty.string)
  pure (inputVal, copy1)

/-- Emit eager type-directed tagged-union duplication via specialized clone -/
partial def emitTaggedDup (inputVal : LocalId) (taggedTy : Ty n) (label : UInt32)
    : StateT (NodeState n) (LowerM n) (LocalId × LocalId) := do
  let copy1 ← StateT.lift (LowerM.emitInst (.clone (.local inputVal) taggedTy label) taggedTy)
  pure (inputVal, copy1)

/-- Emit list duplication via lazy SUP -/
partial def emitListDup (inputVal : LocalId) (_srcTy : Ty n) (_label : UInt32)
    (graph : CGraph) (nodeId : CNodeId) (elemSz : Nat)
    : StateT (NodeState n) (LowerM n) (LocalId × LocalId) := do
  let isPatternMatchDup := match graph.getNode nodeId with
    | some entry =>
      let checkPort (portIdx : Nat) : Bool :=
        match entry.getPort ⟨portIdx⟩ with
        | some port => match graph.getNode port.node with
          | some e => match e.node with | .mat _ => true | _ => false
          | none => false
        | none => false
      checkPort 1 || checkPort 2
    | none => false
  -- Shallow struct copy for all list DUPs. Both copies share the backing buffer.
  let _ := isPatternMatchDup
  let _ := elemSz
  let copy0 ← StateT.lift (LowerM.emitInst (.copy (.local inputVal)) .somaList)
  let copy1 ← StateT.lift (LowerM.emitInst (.copy (.local inputVal)) .somaList)
  pure (copy0, copy1)

/-- Lower an operand with FuncId map -/
partial def lowerOperandWithMap (graph : CGraph) (port : CPortId) (funcIdMap : FuncIdMap)
    (expectedTy : Option (Ty n) := none)
    : StateT (NodeState n) (LowerM n) LocalId := do
  let ns ← get

  -- Check if this specific port was already bound
  if let some cached := ns.results.get? (port.node.id * 1000 + port.port.idx) then
    return cached

  -- Special case: accessing a consumed LAM (from collectLamChain)
  if let some paramIdx := ns.lamParams.get? port.node.id then
    if port.port.idx == 1 then
      -- VAR port: return the parameter directly
      return ⟨paramIdx⟩
    else
      -- PRINCIPAL (port 0) or BODY (port 2) port of a consumed LAM.
      -- These are structural connections that shouldn't be followed, produce undef
      let ty := expectedTy.orElse (fun _ => ns.expectedResultTy) |>.getD (.prim .unit)
      return ← StateT.lift (LowerM.emitInst (.copy (.const (.undef ty.close))) ty)

  -- Propagate expected type from consumer to this node
  if let some ty := expectedTy then
    modify fun s => { s with expectedResultTy := some ty }
  let nodeResult ← lowerNodeWithMap graph port.node funcIdMap
  -- Re-check port-specific cache: nodes like DUP populate per-port results
  -- during lowering, so the port-specific binding may now exist.
  let ns' ← get
  if let some cached := ns'.results.get? (port.node.id * 1000 + port.port.idx) then
    return cached

  -- Deferred SUP projection for heap DUPs
  if port.port.idx == 1 || port.port.idx == 2 then
    match graph.getNode port.node with
    | some entry =>
      match entry.node with
      | .dup _ =>
        let nodeTy := getNodeTypeWithMapping entry ns'.toTypeConvCtx
        let usesLazySup := nodeTy.dupTier == .heap && !nodeTy.canInlineDup &&
          Ty.supportsLazySup nodeTy && (match nodeTy with | .closure _ _ => false | _ => true)
        if usesLazySup then
          let projVal ←
            if port.port.idx == 1 then
              StateT.lift (LowerM.emitInst (.supProj0 (.local nodeResult) nodeTy) nodeTy)
            else
              StateT.lift (LowerM.emitInst (.supProj1 (.local nodeResult) nodeTy) nodeTy)
          modify fun s => { s with results := s.results.insert (port.node.id * 1000 + port.port.idx) projVal }
          return projVal
      | _ => pure ()
    | none => pure ()
  pure nodeResult

/-- Resolve a closure CTOR's fn port to a book definition index -/
private partial def resolveClosureFnBookIdx (graph : CGraph) (fnNodeId : CNodeId)
    (anonLamBookIdx : Std.HashMap Nat Nat) : Option Nat :=
  if let some bookIdx := anonLamBookIdx.get? fnNodeId.id then
    some bookIdx
  else
    match resolveCanonicalRef graph fnNodeId with
    | .bookRef refId => some refId
    | _ => none

/-- Lower a node with FuncId mapping for closure references -/
partial def lowerNodeWithMap (graph : CGraph) (nodeId : CNodeId) (funcIdMap : FuncIdMap)
    : StateT (NodeState n) (LowerM n) LocalId := do
  let ns ← get

  -- Check memoization cache
  if let some result := ns.results.get? nodeId.id then
    return result

  -- Cycles in the interaction net graph arise from erased type-level or structural references that are never acessed
  if ns.processing.contains nodeId.id then
    let ty := ns.expectedResultTy.getD valueType
    return ← StateT.lift (LowerM.emitInst (.copy (.const (.undef ty.close))) ty)

  -- Mark as processing
  modify fun s => { s with processing := s.processing.insert nodeId.id }

  -- Missing node: should not happen in well-formed graphs
  let some entry := graph.getNode nodeId | do
    let ty := ns.expectedResultTy.getD valueType
    return ← StateT.lift (LowerM.emitPanic ty s!"missing node {nodeId.id}")

  let ctx := ns.toTypeConvCtx
  let nodeTy := getNodeTypeWithMapping entry ctx

  let getPortType (portIdx : Nat) (defaultTy : Ty n := nodeTy) : Ty n :=
    match entry.getPort ⟨portIdx⟩ with
    | some targetPort =>
      match graph.getNode targetPort.node with
      | some targetEntry => getNodeTypeWithMapping targetEntry ctx
      | none => defaultTy
    | none => defaultTy

  let lowerPort (portIdx : Nat) (defaultTy : Ty n := nodeTy) (expectedTy : Option (Ty n) := none)
      : StateT (NodeState n) (LowerM n) LocalId := do
    match entry.getPort ⟨portIdx⟩ with
    | some targetPort => lowerOperandWithMap graph targetPort funcIdMap expectedTy
    | none => StateT.lift (LowerM.emitPanic defaultTy s!"missing port {portIdx} on node {nodeId.id}")

  let result ← match entry.node with
  | .num primTy val =>
    StateT.lift (lowerNum primTy val)

  | .num64 primTy lo hi => do
    let ty : Ty n := Ty.prim (convertCircuitPrimType primTy)
    let val64 : UInt64 := hi.toUInt64 <<< 32 ||| lo.toUInt64
    if primTy == .f64 then
      StateT.lift (LowerM.emitInst (.copy (.const (.float (Float.ofBits val64) .f64))) ty)
    else
      StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat val64.toNat) (convertCircuitPrimType primTy)))) ty)

  | .era => do
    -- ERA nodes erase the value connected to their principal port.
    match entry.getPort ⟨0⟩ with
    | some sourcePort =>
      if sourcePort.port.isPrincipal then
        -- ERA is erasing a value producer so it's safe to follow
        match graph.getNode sourcePort.node with
        | some sourceEntry =>
          let sourceTy := getNodeTypeWithMapping sourceEntry ctx
          if sourceTy.needsErase then
            -- Check cycle: don't erase if the source is already being processed
            let ns ← get
            if !ns.processing.contains sourcePort.node.id then
              let sourceVal ← lowerOperandWithMap graph sourcePort funcIdMap
              StateT.lift (LowerM.emitVoid (.erase (.local sourceVal) sourceTy))
        | none => pure ()
      else
        pure ()
    | none => pure ()
    let eraTy := match (← get).expectedResultTy with
      | some expected => expected
      | none => nodeTy
    StateT.lift (LowerM.emitInst (.copy (.const (.undef eraTy.close))) eraTy)

  | .lam _ =>
    lowerPort 2

  | .app => do
    -- Try saturated multi-argument call via app chain collection
    let saturatedResult ← do
      match collectAppChain graph entry with
      | some chain =>
        -- We have a multi-arg chain. Check if the base is a known function
        match chain.baseEntry.node with
        | .ctor tag arity =>
          if tag == closureTag && arity == 2 then
            -- Closure CTOR at base of APP chain: resolve fn port to a function and call directly
            let fnResolved ← do
              match chain.baseEntry.getPort ⟨1⟩ with
              | some fnPort =>
                let ns ← get
                pure (resolveClosureFnBookIdx graph fnPort.node ns.anonLamBookIdx)
              | none => pure none
            match fnResolved with
            | some bookIdx =>
              let def_? := graph.getDefinition bookIdx
              let defArity := match def_? with | some d => d.arity | none => 0
              -- Lower all chain args
              let mut argVals : Array LocalId := #[]
              for argPort in chain.argPorts do
                let val ← lowerOperandWithMap graph argPort funcIdMap
                argVals := argVals.push val
              let argOps := argVals.map fun v => Operand.local v
              let ls ← StateT.lift get
              let funcRef := buildFuncRefFromBookRef graph bookIdx (some funcIdMap) ls.ctxIntrinsics
              if chain.argPorts.size == defArity then
                -- Saturated call: emit direct call
                let callRetTy := match def_? with
                  | some d => extractReturnTypeWithMapping d.ty ctx
                  | none => nodeTy
                let result ← match funcRef with
                  | .local funcId =>
                    StateT.lift (LowerM.emitInst (.call funcId argOps callRetTy) callRetTy)
                  | .external name =>
                    StateT.lift (LowerM.emitInst (.callExtern name argOps callRetTy) callRetTy)
                  | _ =>
                    StateT.lift (LowerM.emitInst (.call (FuncId.mk 0) argOps nodeTy) nodeTy)
                for intermediateId in chain.intermediateAppNodes do
                  modify fun s => { s with results := s.results.insert intermediateId.id result }
                pure (some result)
              else if chain.argPorts.size < defArity then
                -- Under-saturated: build partial application via nested makeClosure
                let firstArg := argOps[0]!
                let firstResult ← match funcRef with
                  | .local funcId =>
                    StateT.lift (LowerM.emitInst (.makeClosure (.local funcId) firstArg) nodeTy)
                  | _ =>
                    StateT.lift (LowerM.emitInst (.makeClosure (.local (FuncId.mk 0)) firstArg) nodeTy)
                -- Apply remaining args via callClosure
                let mut current := firstResult
                for i in [1:argOps.size] do
                  current ← StateT.lift (LowerM.emitInst (.callClosure (.local current) #[argOps[i]!] nodeTy) nodeTy)
                for intermediateId in chain.intermediateAppNodes do
                  modify fun s => { s with results := s.results.insert intermediateId.id current }
                pure (some current)
              else
                -- Over-saturated: call with defArity args, then callClosure the rest
                let directArgs := argOps.extract 0 defArity
                let extraArgs := argOps.extract defArity argOps.size
                let callRetTy := match def_? with
                  | some d => extractReturnTypeWithMapping d.ty ctx
                  | none => nodeTy
                let initResult ← match funcRef with
                  | .local funcId =>
                    StateT.lift (LowerM.emitInst (.call funcId directArgs callRetTy) callRetTy)
                  | .external name =>
                    StateT.lift (LowerM.emitInst (.callExtern name directArgs callRetTy) callRetTy)
                  | _ =>
                    StateT.lift (LowerM.emitInst (.call (FuncId.mk 0) directArgs callRetTy) callRetTy)
                let mut current := initResult
                for extraArg in extraArgs do
                  current ← StateT.lift (LowerM.emitInst (.callClosure (.local current) #[extraArg] nodeTy) nodeTy)
                for intermediateId in chain.intermediateAppNodes do
                  modify fun s => { s with results := s.results.insert intermediateId.id current }
                pure (some current)
            | none =>
              -- Can't resolve fn port so we fall through to regular CTOR handling
              pure none
          else
            -- Regular constructor applied via APP chain: collect CTOR fields + chain args
            let mut fieldVals : Array LocalId := #[]
            for i in [:arity] do
              match chain.baseEntry.getPort ⟨i + 1⟩ with
              | some port =>
                let val ← lowerOperandWithMap graph port funcIdMap
                fieldVals := fieldVals.push val
              | none =>
                let val ← StateT.lift (LowerM.emitPanic (.prim .i64) s!"CTOR-APP chain: missing CTOR field {i}")
                fieldVals := fieldVals.push val
            for argPort in chain.argPorts do
              let val ← lowerOperandWithMap graph argPort funcIdMap
              fieldVals := fieldVals.push val
            let result ← match nodeTy with
              | .struct _ => StateT.lift (lowerNestedStructLit fieldVals nodeTy)
              | _ => StateT.lift (lowerCtor tag fieldVals.size fieldVals nodeTy)
            for intermediateId in chain.intermediateAppNodes do
              modify fun s => { s with results := s.results.insert intermediateId.id result }
            pure (some result)
        | .ref refId | .alo refId =>
          match graph.getDefinition refId with
          | some def_ =>
            if def_.arity == chain.argPorts.size then
              -- Saturated call, let's lower all arguments
              let mut argVals : Array LocalId := #[]
              for argPort in chain.argPorts do
                let val ← lowerOperandWithMap graph argPort funcIdMap
                argVals := argVals.push val
              let argOps := argVals.map fun v => Operand.local v

              let callRetTy := extractReturnTypeWithMapping chain.baseEntry.ty ctx

              -- Resolve intrinsics via authoritative table + name fallback
              let ls ← StateT.lift get
              match resolveIntrinsic? def_.name ls.ctxIntrinsics with
              | some (Intrinsic.ffiOp op) =>
                let intrinsicOp := convertFFIOp op
                let retTy : Ty n := match intrinsicOp.fixedRetTy with
                  | some t => ClosedTy.embed t
                  | none => callRetTy
                let result ← StateT.lift (LowerM.emitInst (.callIntrinsic intrinsicOp argOps retTy) retTy)
                -- Memoize intermediate app nodes to prevent relowering
                for intermediateId in chain.intermediateAppNodes do
                  modify fun s => { s with results := s.results.insert intermediateId.id result }
                pure (some result)
              | some (Intrinsic.extern name) =>
                let result ← StateT.lift (LowerM.emitInst (.callExtern name argOps callRetTy) callRetTy)
                for intermediateId in chain.intermediateAppNodes do
                  modify fun s => { s with results := s.results.insert intermediateId.id result }
                pure (some result)
              | _ =>
                -- Regular function: resolve reference
                let funcRef := buildFuncRefFromBookRef graph refId (some funcIdMap) ls.ctxIntrinsics
                let argTypes ← chain.argPorts.mapM fun port =>
                  match graph.getNode port.node with
                  | some argEntry => pure argEntry.ty
                  | none => pure (Value.vType .zero)
                let result ← match funcRef with
                  | .local funcId =>
                    let resolvedTypeArgs? := graph.getResolvedTypeArgs chain.baseNodeId
                    pure ()
                    let typeArgs? := match resolvedTypeArgs? with
                      | some resolved => convertResolvedTypeArgs resolved def_.ty ctx
                      | none => none
                    let typeArgs? := typeArgs?.orElse fun _ =>
                      extractCallTypeArgsFromArgs def_.ty argTypes entry.ty chain.baseEntry.ty ctx
                    pure ()
                    match typeArgs? with
                    | some typeArgs =>
                      StateT.lift (LowerM.emitInst (.callPoly funcId typeArgs argOps callRetTy) callRetTy)
                    | none =>
                      StateT.lift (LowerM.emitInst (.call funcId argOps callRetTy) callRetTy)
                  | .external name =>
                    let resolvedTypeArgs? := graph.getResolvedTypeArgs chain.baseNodeId
                    let extTypeArgs? := match resolvedTypeArgs? with
                      | some resolved => convertResolvedTypeArgs resolved def_.ty ctx
                      | none => none
                    let extTypeArgs? := extTypeArgs?.orElse fun _ =>
                      extractCallTypeArgsFromArgs def_.ty argTypes entry.ty chain.baseEntry.ty ctx
                    match extTypeArgs? with
                    | some typeArgs =>
                      StateT.lift (LowerM.emitInst (.callExternPoly name typeArgs argOps callRetTy) callRetTy)
                    | none =>
                      StateT.lift (LowerM.emitInst (.callExtern name argOps callRetTy) callRetTy)
                  | .externC name =>
                    StateT.lift (LowerM.emitInst (.callExtern name argOps callRetTy) callRetTy)
                  | .intrinsic op =>
                    StateT.lift (LowerM.emitInst (.callIntrinsic op argOps callRetTy) callRetTy)
                  | .primOp _op =>
                    -- PrimOps with multiple args
                    StateT.lift (LowerM.emitInst (.callExtern s!"primop_{_op}" argOps callRetTy) callRetTy)
                for intermediateId in chain.intermediateAppNodes do
                  modify fun s => { s with results := s.results.insert intermediateId.id result }
                pure (some result)
            else
              -- Arity mismatch: not a saturated call, fall through
              pure none
          | none => pure none
        | _ => pure none
      | none => pure none

    match saturatedResult with
    | some result => pure result
    | none => do
      let fnPort := entry.getPort ⟨1⟩

      let lsUnsaturated ← StateT.lift get
      let ctx := ns.toTypeConvCtx
      let maybeIntrinsicWithDef ← match fnPort with
        | some fp =>
          match graph.getNode fp.node with
          | some fnEntry =>
            match fnEntry.node with
            | .ref refId | .alo refId =>
              match graph.getDefinition refId with
              | some def_ =>
                match resolveIntrinsic? def_.name lsUnsaturated.ctxIntrinsics with
                | some (Intrinsic.ffiOp op) =>
                  let v : Sum FFIOp String := Sum.inl op
                  pure (some (v, some def_))
                | some (Intrinsic.extern name) =>
                  let v : Sum FFIOp String := Sum.inr name
                  pure (some (v, some def_))
                | _ => pure none
              | none => pure none
            | _ => pure none
          | none => pure none
        | none => pure none

      let argVal ← lowerPort 2 (.prim .unit)

      match maybeIntrinsicWithDef with
      | some (Sum.inl ffiOp, _) =>
        let intrinsicOp := convertFFIOp ffiOp
        let retTy : Ty n := match intrinsicOp.fixedRetTy with
          | some t => ClosedTy.embed t
          | none => nodeTy
        StateT.lift (LowerM.emitInst (.callIntrinsic intrinsicOp #[.local argVal] retTy) retTy)
      | some (Sum.inr externName, def_?) =>
        let callRetTy := match def_? with
          | some d => extractReturnTypeWithMapping d.ty ctx
          | none => nodeTy
        StateT.lift (LowerM.emitInst (.callExtern externName #[.local argVal] callRetTy) callRetTy)
      | none =>
        -- Regular function call: check what the function node is
        match fnPort with
        | none =>
          -- No function port → erased function call, produce undef
          let erasedTy := (← get).expectedResultTy.getD nodeTy
          StateT.lift (LowerM.emitInst (.copy (.const (.undef erasedTy.close))) erasedTy)
        | some fp =>
          match graph.getNode fp.node with
          | none =>
            -- Missing function node
            StateT.lift (LowerM.emitPanic nodeTy s!"APP node {nodeId.id}: missing fn node {fp.node}")
          | some fnEntry =>
            match fnEntry.node with
            | .era =>
              -- Function is ERA → erased function call, produce undef
              let erasedTy := (← get).expectedResultTy.getD nodeTy
              StateT.lift (LowerM.emitInst (.copy (.const (.undef erasedTy.close))) erasedTy)
            | .lam _ =>
              lowerNodeWithMap graph fp.node funcIdMap
            | .ref refId | .alo refId =>
              let def_? := graph.getDefinition refId
              let defArity := match def_? with
                | some def_ => def_.arity
                | none => 1
              let ls ← StateT.lift get
              let funcRef := buildFuncRefFromBookRef graph refId (some funcIdMap) ls.ctxIntrinsics
              let argType := match entry.getPort ⟨2⟩ with
                | some argPort =>
                  match graph.getNode argPort.node with
                  | some argEntry => argEntry.ty
                  | none => Value.vType .zero
                | none => Value.vType .zero
              let typeArgs? := def_?.bind fun def_ =>
                extractCallTypeArgsFromArgs def_.ty #[argType] entry.ty fnEntry.ty ctx
              if defArity > 1 then
                match typeArgs? with
                | some typeArgs =>
                  StateT.lift (LowerM.emitInst (.makeClosurePoly funcRef typeArgs (.local argVal)) nodeTy)
                | none =>
                  StateT.lift (LowerM.emitInst (.makeClosure funcRef (.local argVal)) nodeTy)
              else
                let callRetTy := extractReturnTypeWithMapping fnEntry.ty ctx
                match funcRef with
                | .local funcId =>
                  match typeArgs? with
                  | some typeArgs =>
                    StateT.lift (LowerM.emitInst (.callPoly funcId typeArgs #[.local argVal] callRetTy) callRetTy)
                  | none =>
                    StateT.lift (LowerM.emitInst (.call funcId #[.local argVal] callRetTy) callRetTy)
                | .external name =>
                  match typeArgs? with
                  | some typeArgs =>
                    StateT.lift (LowerM.emitInst (.callExternPoly name typeArgs #[.local argVal] callRetTy) callRetTy)
                  | none =>
                    StateT.lift (LowerM.emitInst (.callExtern name #[.local argVal] callRetTy) callRetTy)
                | .intrinsic op =>
                  StateT.lift (LowerM.emitInst (.callIntrinsic op #[.local argVal] callRetTy) callRetTy)
                | .primOp _op =>
                  StateT.lift (LowerM.emitInst (.callExtern s!"primop_{_op}" #[.local argVal] callRetTy) callRetTy)
                | .externC name =>
                  StateT.lift (LowerM.emitInst (.callExtern name #[.local argVal] callRetTy) callRetTy)
            | .ctor tag arity =>
              if tag == closureTag && arity == 2 then
                -- Closure CTOR applied via single APP: resolve fn and call/partially apply
                let fnResolved ← do
                  match fnEntry.getPort ⟨1⟩ with
                  | some fnPort2 =>
                    let ns ← get
                    pure (resolveClosureFnBookIdx graph fnPort2.node ns.anonLamBookIdx)
                  | none => pure none
                match fnResolved with
                | some bookIdx =>
                  let def_? := graph.getDefinition bookIdx
                  let defArity := match def_? with | some d => d.arity | none => 1
                  let ls ← StateT.lift get
                  let funcRef := buildFuncRefFromBookRef graph bookIdx (some funcIdMap) ls.ctxIntrinsics
                  if defArity > 1 then
                    -- Unsaturated: partial application via makeClosure
                    StateT.lift (LowerM.emitInst (.makeClosure funcRef (.local argVal)) nodeTy)
                  else
                    -- Saturated: direct call with 1 arg
                    let callRetTy := match def_? with
                      | some d => extractReturnTypeWithMapping d.ty ctx
                      | none => nodeTy
                    match funcRef with
                    | .local funcId =>
                      StateT.lift (LowerM.emitInst (.call funcId #[.local argVal] callRetTy) callRetTy)
                    | .external name =>
                      StateT.lift (LowerM.emitInst (.callExtern name #[.local argVal] callRetTy) callRetTy)
                    | _ =>
                      StateT.lift (LowerM.emitInst (.call (FuncId.mk 0) #[.local argVal] callRetTy) callRetTy)
                | none =>
                  -- Can't resolve fn port so we create a closure and call it
                  let fnVal ← lowerOperandWithMap graph fp funcIdMap
                  StateT.lift (LowerM.emitInst (.callClosure (.local fnVal) #[.local argVal] nodeTy) nodeTy)
              else
                -- Regular constructor applied via single APP: collect CTOR fields + the APP arg
                let mut fieldVals : Array LocalId := #[]
                for i in [:arity] do
                  match fnEntry.getPort ⟨i + 1⟩ with
                  | some port =>
                    let val ← lowerOperandWithMap graph port funcIdMap
                    fieldVals := fieldVals.push val
                  | none =>
                    let val ← StateT.lift (LowerM.emitPanic (.prim .i64) s!"CTOR-APP: missing CTOR field {i}")
                    fieldVals := fieldVals.push val
                fieldVals := fieldVals.push argVal
                match nodeTy with
                | .struct _ => StateT.lift (lowerNestedStructLit fieldVals nodeTy)
                | _ => StateT.lift (lowerCtor tag fieldVals.size fieldVals nodeTy)
            | _ =>
              -- Regular closure call: lower the function and use callClosure
              let fnNodeTy := getNodeTypeWithMapping fnEntry ctx
              if fnNodeTy == .prim .unit then
                -- Erased function → produce undef
                let erasedTy := (← get).expectedResultTy.getD nodeTy
                StateT.lift (LowerM.emitInst (.copy (.const (.undef erasedTy.close))) erasedTy)
              else
                let fnVal ← lowerOperandWithMap graph fp funcIdMap
                StateT.lift (LowerM.emitInst (.callClosure (.local fnVal) #[.local argVal] nodeTy) nodeTy)

  | .ctor tag arity => do
    -- Check for special closure CTOR (tag 0xFFFE, arity 2)
    if tag == closureTag && arity == 2 then
      -- Closure CTOR
      let fnPort ← match entry.getPort ⟨1⟩ with
        | some p => pure p
        | none =>
          return ← StateT.lift (LowerM.emitPanic nodeTy s!"CTOR closure node {nodeId.id}: no fn port")

      let canonRef := resolveCanonicalRef graph fnPort.node

      -- Lower the environment (port 2)
      let savedExpectedTy := (← get).expectedResultTy
      modify fun s => { s with expectedResultTy := none }
      let envVal ← match entry.getPort ⟨2⟩ with
        | some envPort => lowerOperandWithMap graph envPort funcIdMap
        | none => StateT.lift (LowerM.emitInst (.copy (.const (.null .rawPtr))) .rawPtr)
      modify fun s => { s with expectedResultTy := savedExpectedTy }

      match canonRef with
      | .bookRef refId =>
        let ls ← StateT.lift get
        let funcRef := buildFuncRefFromBookRef graph refId (some funcIdMap) ls.ctxIntrinsics
        let fnNodeTy := graph.getNode fnPort.node |>.map (·.ty)
        let typeArgs? := (graph.getDefinition refId).bind fun def_ =>
          fnNodeTy.bind fun concTy => extractCallTypeArgs def_.ty concTy ctx
        match typeArgs? with
        | some typeArgs =>
          StateT.lift (LowerM.emitInst (.makeClosurePoly funcRef typeArgs (.local envVal)) nodeTy)
        | none =>
          StateT.lift (LowerM.emitInst (.makeClosure funcRef (.local envVal)) nodeTy)
      | .dynamicValue _ =>
        -- Check if this LAM was extracted as a synthetic function
        let ns ← get
        if let some bookIdx := ns.anonLamBookIdx.get? fnPort.node.id then
          let ls ← StateT.lift get
          let funcRef := buildFuncRefFromBookRef graph bookIdx (some funcIdMap) ls.ctxIntrinsics
          -- Unit env because the extracted function has all LAM params flattened
          let unitEnv ← StateT.lift (LowerM.emitInst (.copy (.const (.undef (.prim .unit)))) (.prim .unit))
          let fnNodeTy := graph.getNode fnPort.node |>.map (·.ty)
          let typeArgs? := (graph.getDefinition bookIdx).bind fun def_ =>
            fnNodeTy.bind fun concTy => extractCallTypeArgs def_.ty concTy ctx
          let closureVal ← match typeArgs? with
          | some typeArgs =>
            StateT.lift (LowerM.emitInst (.makeClosurePoly funcRef typeArgs (.local unitEnv)) nodeTy)
          | none =>
            StateT.lift (LowerM.emitInst (.makeClosure funcRef (.local unitEnv)) nodeTy)
          -- If the env port connects to a real value (not ERA), partially apply it
          let isEraEnv := match entry.getPort ⟨2⟩ with
            | some envPort =>
              match graph.getNode envPort.node with
              | some envEntry => match envEntry.node with | .era => true | _ => false
              | none => true
            | none => true
          if !isEraEnv then
            StateT.lift (LowerM.emitInst (.callClosure (.local closureVal) #[.local envVal] nodeTy) nodeTy)
          else
            pure closureVal
        else
          let fnClosureVal ← lowerOperandWithMap graph fnPort funcIdMap
          StateT.lift (LowerM.emitInst (.makeClosureDyn (.local fnClosureVal) (.local envVal) nodeTy) nodeTy)
    else if isListValue entry.ty (← get).primTypes then
      if tag == 0 then
        StateT.lift (LowerM.emitInst
          (.structLit #[.const (.null .rawPtr),
                        .const (.int 0 .u32),
                        .const (.int 0 .u32)] .somaList) .somaList)
      else
        let headVal ← lowerPort 1
        let tailVal ← lowerPort 2
        let headTy := getPortType 1 (.prim .i64)
        let elemSz := listElemSize headTy (← get).ptrBytes
        let headAlloca ← StateT.lift (LowerM.emitInst (.alloca headTy) (.ptr headTy))
        StateT.lift (LowerM.emitVoid (.store (.local headAlloca) (.local headVal)))
        let elemSizeConst ← StateT.lift (LowerM.emitInst
          (.copy (.const (.int (Int.ofNat elemSz) .u16))) (.prim .u16))
        StateT.lift (LowerM.emitInst
          (.callExtern "soma_list_cons"
            #[.local headAlloca, .local tailVal, .local elemSizeConst] .somaList) .somaList)
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
    -- Check if the projected value is an array or List type (for church-encoded list destructuring)
    let ns ← get
    let isListProj :=
      -- First check: is the record value known to be list-typed from a prior MAT?
      if ns.listTypedLocals.contains recordVal.id then true
      else
        let rec traceSource (portOpt : Option CPortId) (fuel : Nat) : Bool :=
          match fuel with
          | 0 => false
          | fuel + 1 =>
            match portOpt with
            | some port => match graph.getNode port.node with
              | some srcEntry => match srcEntry.node with
                | .array _ => true
                | .dup _ => traceSource (srcEntry.getPort ⟨0⟩) fuel
                | _ => isListValue srcEntry.ty ns.primTypes
              | none => false
            | none => false
        traceSource (entry.getPort ⟨1⟩) 10
    if isListProj then do
      if fieldIdx == 0 then
        -- Inline head: (char*)list.data + (size_t)list.offset * elem_size
        let pb := (← get).ptrBytes
        let elemSz := listElemSize nodeTy pb
        let dataPtr ← StateT.lift (LowerM.emitInst
          (.extractField (.local recordVal) 0) .rawPtr)
        let offset ← StateT.lift (LowerM.emitInst
          (.extractField (.local recordVal) 2) (.prim .u32))
        let offset64 ← StateT.lift (LowerM.emitInst
          (.unOp (.zext .i64) (.local offset)) (.prim .i64))
        let elemSz64 ← StateT.lift (LowerM.emitInst
          (.copy (.const (.int (Int.ofNat elemSz) .i64))) (.prim .i64))
        let byteOff ← StateT.lift (LowerM.emitInst
          (.binOp .mul (.local offset64) (.local elemSz64) (.prim .i64)) (.prim .i64))
        let headPtr ← StateT.lift (LowerM.emitInst
          (.callIntrinsic .ptrAdd #[.local dataPtr, .local byteOff] .rawPtr) .rawPtr)
        StateT.lift (LowerM.emitInst (.load (.local headPtr) nodeTy) nodeTy)
      else if fieldIdx == 1 then
        -- Inline tail: { list.data, list.len - 1, list.offset + 1 }
        let dataPtr ← StateT.lift (LowerM.emitInst
          (.extractField (.local recordVal) 0) .rawPtr)
        let len ← StateT.lift (LowerM.emitInst
          (.extractField (.local recordVal) 1) (.prim .u32))
        let offset ← StateT.lift (LowerM.emitInst
          (.extractField (.local recordVal) 2) (.prim .u32))
        let one ← StateT.lift (LowerM.emitInst
          (.copy (.const (.int 1 .u32))) (.prim .u32))
        let newLen ← StateT.lift (LowerM.emitInst
          (.binOp .sub (.local len) (.local one) (.prim .u32)) (.prim .u32))
        let newOff ← StateT.lift (LowerM.emitInst
          (.binOp .add (.local offset) (.local one) (.prim .u32)) (.prim .u32))
        StateT.lift (LowerM.emitInst
          (.structLit #[.local dataPtr, .local newLen, .local newOff] .somaList) .somaList)
      else
        StateT.lift (LowerM.emitPanic nodeTy)
    else
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
    let matResultTy := extractReturnTypeWithMapping entry.ty ctx
    let scrutineeVal ← lowerPort 1
    -- Check if the scrutinee is an array or List type (for church-encoded list matching)
    let ns ← get
    let scrutIsArray := match entry.getPort ⟨1⟩ with
      | some scrutPort => match graph.getNode scrutPort.node with
        | some scrutEntry => match scrutEntry.node with
          | .array _ => true
          | _ => isListValue scrutEntry.ty ns.primTypes
        | none => false
      | none => false
    -- Track list-typed scrutinees so PROJ nodes can detect them
    if scrutIsArray then
      modify fun ns => { ns with listTypedLocals := ns.listTypedLocals.insert scrutineeVal.id }

    do

    let (_, _thenBlock, elseBlock) ← if scrutIsArray then
      -- Array-backed list: check list.len field (index 1) for Nil/Cons
      StateT.lift do
        let lenVal ← LowerM.emitInst (.extractField (.local scrutineeVal) 1) (.prim .u32)
        let zero ← LowerM.emitInst (.copy (.const (.int 0 .u32))) (.prim .u32)
        let cond ← if expectedTag == 0 then
          -- Nil: matches when len == 0
          LowerM.emitInst (.binOp .eq (.local lenVal) (.local zero) (.prim .u32)) Ty.bool
        else
          -- Cons: matches when len != 0
          LowerM.emitInst (.binOp .ne (.local lenVal) (.local zero) (.prim .u32)) Ty.bool
        let thenBlock ← LowerM.freshBlockId
        let elseBlock ← LowerM.freshBlockId
        LowerM.finishBlock (.branch (.local cond) thenBlock elseBlock) thenBlock
        pure (cond, thenBlock, elseBlock)
    else
      StateT.lift (lowerMat expectedTag scrutineeVal)
    let cacheSnapshot ← do let ns ← get; pure ns.snapshotResults

    modify fun ns => { ns with expectedResultTy := some matResultTy }

    -- Lower hit value
    let hitVal ← lowerPort 2 matResultTy (some matResultTy)
    -- Record the actual block we're in after lowering the hit branch
    let hitBlock ← StateT.lift LowerM.getCurrentBlockId
    let joinBlock ← StateT.lift LowerM.freshBlockId
    StateT.lift (LowerM.finishBlock (.jump joinBlock) elseBlock)

    -- Restore cache
    modify fun ns => ns.restoreResults cacheSnapshot

    match entry.getPort ⟨3⟩ with
    | some _ =>
      -- Non-exhaustive or chained match: lower miss branch with expected type
      modify fun ns => { ns with expectedResultTy := some matResultTy }
      let missVal ← lowerPort 3 matResultTy (some matResultTy)
      let missBlock ← StateT.lift LowerM.getCurrentBlockId
      StateT.lift (LowerM.finishBlock (.jump joinBlock) joinBlock)
      StateT.lift (LowerM.emitInst
        (.phi #[(Operand.local hitVal, hitBlock), (Operand.local missVal, missBlock)] matResultTy)
        matResultTy)
    | none =>
      -- Exhaustive match: miss branch is unreachable
      let ls ← StateT.lift get
      StateT.lift (LowerM.emitVoid (.panic ls.panicMsgIdx 0))
      StateT.lift (LowerM.finishBlock .unreachable joinBlock)
      pure hitVal

  | .op1 op => do
    let operandVal ← lowerPort 1
    -- Use operand type for consistency with op2 fix
    let ls ← StateT.lift get
    let operandTy := ls.func.getLocalType operandVal |>.getD nodeTy
    StateT.lift (LowerM.emitInst (.unOp (convertUnOp op) (.local operandVal)) operandTy)

  | .op2 op => do
    let binOp := convertBinOp op
    -- Determine the expected operand type from port types BEFORE lowering operands
    let lhsPortTy := getPortType 1
    let rhsPortTy := getPortType 2
    let expectedOpTy :=
      if lhsPortTy.isArithmetic && lhsPortTy != .prim .unit then some lhsPortTy
      else if rhsPortTy.isArithmetic && rhsPortTy != .prim .unit then some rhsPortTy
      else if lhsPortTy.isArithmetic then some lhsPortTy
      else if rhsPortTy.isArithmetic then some rhsPortTy
      else none
    let lhsVal ← lowerPort 1 nodeTy expectedOpTy
    let rhsVal ← lowerPort 2 nodeTy expectedOpTy
    let ls ← StateT.lift get
    let lhsTy := ls.func.getLocalType lhsVal |>.getD nodeTy
    let rhsTy := ls.func.getLocalType rhsVal |>.getD nodeTy
    -- Both operands must be arithmetic for a valid binary op
    if !lhsTy.isArithmetic || !rhsTy.isArithmetic then
      let resultTy := (← get).expectedResultTy.getD nodeTy
      StateT.lift (LowerM.emitInst (.copy (.const (.undef resultTy.close))) resultTy)
    else
      -- Pick the best operand type: prefer non-unit
      let operandTy :=
        if lhsTy != .prim .unit then lhsTy
        else if rhsTy != .prim .unit then rhsTy
        else lhsTy
      let resultTy := if binOp.isComparison then Ty.bool else operandTy
      StateT.lift (LowerM.emitInst (.binOp binOp (.local lhsVal) (.local rhsVal) operandTy) resultTy)

  | .dup label => do
    let inputVal ← lowerPort 0
    match nodeTy.dupTier with
    | .flat =>
      -- Register copy. Both consumers get the same value.
      let copy0 ← StateT.lift (LowerM.emitInst (.copy (.local inputVal)) nodeTy)
      let copy1 ← StateT.lift (LowerM.emitInst (.copy (.local inputVal)) nodeTy)
      modify fun ns => { ns with
        results := ns.results.insert (nodeId.id * 1000 + 1) copy0
                   |>.insert (nodeId.id * 1000 + 2) copy1
      }
      pure inputVal
    | .heap =>
      if nodeTy.canInlineDup then
        -- Compile-time specialization: the type is fully known with no pointers.
        -- Emit field-by-field copy inline (DUP-NOD for flat structs).
        let (copy0, copy1) ← emitInlineDup inputVal nodeTy
        modify fun ns => { ns with
          results := ns.results.insert (nodeId.id * 1000 + 1) copy0
                     |>.insert (nodeId.id * 1000 + 2) copy1
        }
        pure inputVal
      else if nodeTy == Ty.string then
        let (copy0, copy1) ← emitStringDup inputVal
        modify fun ns => { ns with
          results := ns.results.insert (nodeId.id * 1000 + 1) copy0
                     |>.insert (nodeId.id * 1000 + 2) copy1
        }
        pure inputVal
      else if (match nodeTy with | .tagged _ _ => true | _ => false) then
        let (copy0, copy1) ← emitTaggedDup inputVal nodeTy label.id
        modify fun ns => { ns with
          results := ns.results.insert (nodeId.id * 1000 + 1) copy0
                     |>.insert (nodeId.id * 1000 + 2) copy1
        }
        pure inputVal
      else if nodeTy.isSomaList then
        let srcTy := (← StateT.lift get).func.getLocalType inputVal |>.getD .somaList
        let dupElemSz := listElemSizeFromValueType entry.ty ctx (← get).ptrBytes
        let (copy0, copy1) ← emitListDup inputVal srcTy label.id graph nodeId dupElemSz
        modify fun ns => { ns with
          results := ns.results.insert (nodeId.id * 1000 + 1) copy0
                     |>.insert (nodeId.id * 1000 + 2) copy1
          listTypedLocals := ns.listTypedLocals.insert inputVal.id
            |>.insert copy0.id |>.insert copy1.id
        }
        pure inputVal
      else if nodeTy == .rawPtr then
        let ns ← get
        let rec traceDupSource (portOpt : Option CPortId) (fuel : Nat) : Bool :=
          match fuel with
          | 0 => false
          | fuel + 1 =>
            match portOpt with
            | some port => match graph.getNode port.node with
              | some srcEntry => match srcEntry.node with
                | .array _ => true
                | .dup _ => traceDupSource (srcEntry.getPort ⟨0⟩) fuel
                | _ => isListValue srcEntry.ty ns.primTypes
              | none => false
            | none => false
        let isListSource := isListValue entry.ty ns.primTypes ||
          traceDupSource (entry.getPort ⟨0⟩) 10
        let (copy0, copy1) ←
          if isListSource then
            let srcTy := (← StateT.lift get).func.getLocalType inputVal |>.getD .rawPtr
            let dupElemSz := listElemSizeFromValueType entry.ty ctx (← get).ptrBytes
            emitListDup inputVal srcTy label.id graph nodeId dupElemSz
            else
              let clone ← StateT.lift (LowerM.emitInst (.clone (.local inputVal) .rawPtr label.id) .rawPtr)
              pure (inputVal, clone)
        modify fun ns => { ns with
          results := ns.results.insert (nodeId.id * 1000 + 1) copy0
                     |>.insert (nodeId.id * 1000 + 2) copy1
        }
        -- Propagate list-type info to DUP input & outputs so downstream PROJ/MAT nodes detect them
        if isListSource then
          modify fun ns => { ns with
            listTypedLocals := ns.listTypedLocals.insert inputVal.id
              |>.insert copy0.id |>.insert copy1.id
          }
        pure inputVal
      else if (match nodeTy with | .closure _ _ => true | _ => false) then
        let clone ← StateT.lift (LowerM.emitInst (.clone (.local inputVal) nodeTy label.id) nodeTy)
        modify fun ns => { ns with
          results := ns.results.insert (nodeId.id * 1000 + 1) inputVal
                     |>.insert (nodeId.id * 1000 + 2) clone
        }
        pure inputVal
      else match nodeTy with
      | .struct _ => do
        let clone ← StateT.lift (LowerM.emitInst (.clone (.local inputVal) nodeTy label.id) nodeTy)
        modify fun ns => { ns with
          results := ns.results.insert (nodeId.id * 1000 + 1) inputVal
                     |>.insert (nodeId.id * 1000 + 2) clone
        }
        pure inputVal
      | _ =>
        if Ty.supportsLazySup nodeTy then
          let supVal ← StateT.lift (LowerM.emitInst (.lazySup label.id (.local inputVal) nodeTy) nodeTy)
          pure supVal
        else
          panic! s!"ALLOY LOWERING BUG: DUP on unsupported heap type for lazy SUP ({nodeTy}). Implement type-directed clone/erase lowering for this type before enabling SUP duplication."

  | .sup _ => do
    lowerPort 1

  | .ref refId | .alo refId => do
    let ls ← StateT.lift get
    let funcRef := buildFuncRefFromBookRef graph refId (some funcIdMap) ls.ctxIntrinsics
    let nullEnv ← StateT.lift (LowerM.emitInst (.copy (.const (.null .rawPtr))) .rawPtr)
    let typeArgs? := (graph.getDefinition refId).bind fun def_ =>
      extractCallTypeArgs def_.ty entry.ty ctx
    match typeArgs? with
    | some typeArgs =>
      StateT.lift (LowerM.emitInst (.makeClosurePoly funcRef typeArgs (.local nullEnv)) nodeTy)
    | none =>
      StateT.lift (LowerM.emitInst (.makeClosure funcRef (.local nullEnv)) nodeTy)

  | .use => do
    let _termVal ← lowerPort 1
    lowerPort 2

  | .array _ => do
    let len : Nat ← match entry.getPort ⟨1⟩ with
      | some lenPort =>
        match graph.getNode lenPort.node with
        | some lenEntry => match lenEntry.node with
          | .num _ val => pure val.toNat
          | _ => pure 0
        | none => pure 0
      | none => pure 0

    let ctorInfo ← match entry.getPort ⟨2⟩ with
      | some dataPort =>
        match graph.getNode dataPort.node with
        | some ctorEntry => pure (some (dataPort.node, ctorEntry))
        | none => pure none
      | none => pure none

    let pb := (← get).ptrBytes
    let elemSizeBytes : Nat := match ctorInfo with
      | some (_, ctorEntry) =>
        if len > 0 then
          match ctorEntry.getPort ⟨1⟩ with
          | some elemPort =>
            match graph.getNode elemPort.node with
            | some elemEntry => listElemSize (getNodeTypeWithMapping elemEntry ctx) pb
            | none => defaultElemSize pb
          | none => defaultElemSize pb
        else defaultElemSize pb
      | none => defaultElemSize pb

    if len == 0 then
      -- Nil: { null, 0, 0, 0 }
      StateT.lift (LowerM.emitInst
        (.structLit #[.const (.null .rawPtr),
                      .const (.int 0 .u32),
                      .const (.int 0 .u32)] .somaList) .somaList)
    else
      let elemSizeVal ← StateT.lift (LowerM.emitInst
        (.copy (.const (.int (Int.ofNat elemSizeBytes) .u16))) (.prim .u16))
      let elemAllocTy : Ty n := match ctorInfo with
        | some (_, ctorEntry) =>
          match ctorEntry.getPort ⟨1⟩ with
          | some elemPort =>
            match graph.getNode elemPort.node with
            | some elemEntry => getNodeTypeWithMapping elemEntry ctx
            | none => .prim .i64
          | none => .prim .i64
        | none => .prim .i64
      -- Build list via soma_list_from_array: alloca a flat array, store elements, single call
      let arrayTy : Ty n := .array elemAllocTy len
      let arraySlot ← StateT.lift (LowerM.emitInst (.alloca arrayTy) (.ptr arrayTy))
      match ctorInfo with
      | some (_, ctorEntry) =>
        for i in [:len] do
          let elemVal ← match ctorEntry.getPort ⟨i + 1⟩ with
            | some elemPort => lowerOperandWithMap graph elemPort funcIdMap
            | none => StateT.lift (LowerM.emitPanic (.prim .i64))
          let elemPtr ← StateT.lift (LowerM.emitInst
            (.getElemPtr (.local arraySlot) (.const (.int (Int.ofNat i) .i32)) elemAllocTy) (.ptr elemAllocTy))
          StateT.lift (LowerM.emitVoid (.store (.local elemPtr) (.local elemVal)))
      | none => pure ()
      let lenVal ← StateT.lift (LowerM.emitInst
        (.copy (.const (.int (Int.ofNat len) .u32))) (.prim .u32))
      StateT.lift (LowerM.emitInst
        (.callExtern "soma_list_from_array" #[.local arraySlot, .local lenVal, .local elemSizeVal] .somaList) .somaList)

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

    -- Flat buffer layout: { i64 header, i64 length, [N x i64] data }
    let dataStartPtr ← StateT.lift (emitFlatArrayDataPtr arrayVal)
    let elemPtr ← StateT.lift (LowerM.emitInst (.getElemPtr (.local dataStartPtr) (.local indexVal) (.prim .i64)) (.ptr (.prim .i64)))

    let elemI64 ← StateT.lift (LowerM.emitInst (.load (.local elemPtr) (.prim .i64)) (.prim .i64))
    let pb := (← get).ptrBytes
    let nodeSize := Ty.sizeBytes nodeTy pb
    if nodeSize < pb then
      match nodeTy with
      | .prim p => StateT.lift (LowerM.emitInst (.unOp (.trunc p) (.local elemI64)) nodeTy)
      | _ => pure elemI64
    else pure elemI64

  | .slice =>
    StateT.lift (LowerM.emitPanic nodeTy)

  -- Cache result and clear processing flag
  modify fun ns => { ns with
    results := ns.results.insert nodeId.id result
    processing := ns.processing.erase nodeId.id
  }
  pure result

end

/-- Count the arity of a LAM chain starting from a node -/
def countLamChainArity (graph : CGraph) (root : CNodeId) : Nat := Id.run do
  let mut current := root
  let mut arity : Nat := 0
  let mut visited : Std.HashSet Nat := {}
  for _ in [:1000] do
    if visited.contains current.id then break
    visited := visited.insert current.id
    match graph.getNode current with
    | some entry =>
      match entry.node with
      | .lam _ =>
        arity := arity + 1
        match entry.getPort ⟨2⟩ with
        | some bodyPort => current := bodyPort.node
        | none => break
      | _ => break
    | none => break
  arity

/-- Collect LAM chain information for function parameters -/
def collectLamChain (graph : CGraph) (root : CNodeId) (arity : Nat)
    : CNodeId × Std.HashMap Nat Nat := Id.run do
  let mut current := root
  let mut lamParams : Std.HashMap Nat Nat := {}
  let mut visited : Std.HashSet Nat := {}

  for i in [:arity] do
    if visited.contains current.id then break
    visited := visited.insert current.id
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

/-- Lower a definition with a specific type parameter count n -/
def lowerDefinitionWithN (graph : CGraph) (def_ : CDefinition) (funcId : FuncId)
    (funcIdMap : FuncIdMap) (tyVarMapping : TyVarMapping n) (primTypes : PrimTypeRegistry)
    (inductives : Std.HashMap QualifiedName Soma.Dependent.InductiveMeta := {})
    (intrinsics : Std.HashMap QualifiedName Intrinsic := {})
    (panicMsgIdx : Nat := 0)
    (anonLamBookIdx : Std.HashMap Nat Nat := {})
    (wiredRole : Option WiredFunc := none) : Func n :=
  let ctx : TypeConvCtx n := { tyVars := tyVarMapping, primTypes, inductives }
  let (explicitTypeParams, paramInfos) := extractParamsUsingMapping def_.ty ctx
  let numTyVars := n
  let typeParamNames := if explicitTypeParams.size >= numTyVars then
      explicitTypeParams.extract 0 numTyVars
    else
      -- Generate synthetic names for extra type variables
      let extra := (List.range (numTyVars - explicitTypeParams.size)).toArray.map fun i =>
        s!"T{explicitTypeParams.size + i}"
      explicitTypeParams ++ extra
  let defaultTy : Ty n := .prim .i64
  let params := (List.range def_.arity).toArray.map fun i =>
    if h : i < paramInfos.size then
      let (pname, pty) := paramInfos[i]
      { id := ⟨i⟩, name := pname, ty := pty : Param n }
    else { id := ⟨i⟩, name := s!"arg{i}", ty := defaultTy : Param n }
  let retTy := extractReturnTypeWithMapping def_.ty ctx
  let sig : Signature n := { name := def_.name.symbolName, typeParamNames, params, retTy }
  let returnsUnit := sig.retTy == .prim .unit

  let (_, func) := LowerM.run' funcId sig intrinsics panicMsgIdx do
    if def_.arity == 0 then
      let initState : NodeState n := { tyVarMapping, primTypes, inductives, expectedResultTy := some sig.retTy, anonLamBookIdx }
      let (result, _) ← StateT.run (lowerNodeWithMap graph def_.root funcIdMap) initState
      if returnsUnit then LowerM.terminate .retUnit
      else LowerM.terminate (.ret (.local result))
    else
      let (bodyNode, lamParams) := collectLamChain graph def_.root def_.arity
      let initState : NodeState n := { lamParams, tyVarMapping, primTypes, inductives, expectedResultTy := some sig.retTy, anonLamBookIdx }
      let (result, _) ← StateT.run (lowerNodeWithMap graph bodyNode funcIdMap) initState
      if returnsUnit then LowerM.terminate .retUnit
      else LowerM.terminate (.ret (.local result))

  { func with attrs := { func.attrs with wiredRole } }

/-- Lower a Circuit definition to an Alloy function -/
def lowerDefinition (graph : CGraph) (def_ : CDefinition) (funcId : FuncId)
    (funcIdMap : FuncIdMap) (primTypes : PrimTypeRegistry)
    (inductives : Std.HashMap QualifiedName Soma.Dependent.InductiveMeta := {})
    (intrinsics : Std.HashMap QualifiedName Intrinsic := {})
    (panicMsgIdx : Nat := 0)
    (anonLamBookIdx : Std.HashMap Nat Nat := {})
    (wiredRole : Option WiredFunc := none) : SomeFunc :=
  -- Collect all type variable levels and build mapping
  let ⟨n, tyVarMapping⟩ := buildTyVarMappingFromDefinition graph def_
  -- Lower with the determined n
  let func := lowerDefinitionWithN graph def_ funcId funcIdMap tyVarMapping primTypes inductives intrinsics panicMsgIdx anonLamBookIdx wiredRole
  -- Return existentially quantified function
  ⟨n, func⟩

/-- Lower an entire Circuit graph to an Alloy module -/
def lowerGraph (graph : CGraph) (moduleName : String := "main") (primTypes : PrimTypeRegistry := {})
    (inductives : Std.HashMap QualifiedName Soma.Dependent.InductiveMeta := {})
    (intrinsics : Std.HashMap QualifiedName Intrinsic := {})
    (wiredFuncs : WiredFuncRegistry := {}) : Module := Id.run do
  let mut module := Module.empty moduleName

  -- Copy string table from Circuit graph to Alloy module
  let circuitStrings := graph.getStringTable
  let mut stringTable := StringTable.empty
  for s in circuitStrings do
    let (_, st') := stringTable.intern s
    stringTable := st'
  -- Intern panic message for unreachable code paths
  let (panicMsgIdx, st') := stringTable.intern "soma: unreachable code"
  stringTable := st'
  module := { module with strings := stringTable }

  -- Extract anonymous LAMs from closure CTORs as synthetic definitions
  let mut extGraph := graph
  let mut anonLamBookIdx : Std.HashMap Nat Nat := {}
  let mut seen : Std.HashSet Nat := {}
  for (_, entry) in graph.nodes.toList do
    match entry.node with
    | .ctor tag arity =>
      if tag == closureTag && arity == 2 then
        match entry.getPort ⟨1⟩ with
        | some fnPort =>
          if !seen.contains fnPort.node.id then
            match graph.getNode fnPort.node with
            | some fnEntry =>
              match fnEntry.node with
              | .lam _ =>
                seen := seen.insert fnPort.node.id
                let lamArity := countLamChainArity graph fnPort.node
                let syntheticName : QualifiedName :=
                  ⟨{ id := 100000 + fnPort.node.id, module := "$anon", original := s!"lambda${fnPort.node.id}" }⟩
                let (bookIdx, g') := extGraph.addDefinition syntheticName fnPort.node lamArity fnEntry.ty
                extGraph := g'
                anonLamBookIdx := anonLamBookIdx.insert fnPort.node.id bookIdx
              | _ => pure ()
            | none => pure ()
        | none => pure ()
    | _ => pure ()

  -- First pass: build mapping from Circuit book index to sequential Alloy FuncId
  let mut funcIdMap : FuncIdMap := {}
  let mut nextFuncId : Nat := 0
  for i in [:extGraph.book.size] do
    if let some def_ := extGraph.book[i]? then
      if not def_.isExternal then
        funcIdMap := funcIdMap.insert i (FuncId.mk nextFuncId)
        nextFuncId := nextFuncId + 1

  -- Second pass: lower definitions using the mapping
  for i in [:extGraph.book.size] do
    if let some def_ := extGraph.book[i]? then
      if not def_.isExternal then
        let funcId := funcIdMap.get? i |>.getD (FuncId.mk 0)
        let wiredRole := wiredFuncs.get? def_.name.id
        let func := lowerDefinition extGraph def_ funcId funcIdMap primTypes inductives intrinsics panicMsgIdx anonLamBookIdx wiredRole
        module := module.addFunc func

  -- Set main function using the mapped ID
  if let some (idx, _) := extGraph.findDefinitionByDisplay "main" then
    if let some mappedId := funcIdMap.get? idx then
      module := module.withMain mappedId

  module

/-- Main entry point: lower a Circuit graph to an Alloy module -/
def lower (graph : CGraph) (moduleName : String := "main") (primTypes : PrimTypeRegistry := {})
    (inductives : Std.HashMap QualifiedName Soma.Dependent.InductiveMeta := {})
    (intrinsics : Std.HashMap QualifiedName Intrinsic := {})
    (wiredFuncs : WiredFuncRegistry := {}) : Module :=
  lowerGraph graph moduleName primTypes inductives intrinsics wiredFuncs

end Somac.Alloy.Lower
