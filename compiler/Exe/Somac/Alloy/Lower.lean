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

private def intrinsicOfQName? (qn : QualifiedName) : Option Intrinsic :=
  let n := qn.id.original
  match PrimOp.fromString? n with
  | some op => some (.primOp op)
  | none =>
    match FFIOp.fromString? n with
    | some op => some (.ffiOp op)
    | none =>
      if qn.id.module == "$intrinsic" then
        some (.extern n)
      else
        none

private def isIntrinsicQName (qn : QualifiedName) : Bool :=
  (intrinsicOfQName? qn).isSome

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

/-- Check if a Core Value type is a List type via the primitive type registry -/
def isListValue (v : Soma.Core.Value) (primTypes : PrimTypeRegistry) : Bool :=
  match v with
  | .vDataType uid _ => primTypes.get? uid == some .list
  | _ => false

/-- Combined context for type conversion during Alloy lowering -/
structure TypeConvCtx (n : Nat) where
  tyVars : TyVarMapping n
  primTypes : PrimTypeRegistry
  deriving Inhabited

/-- Build the primitive type registry from the wired-in type registry -/
def buildPrimTypeRegistry (wiredIn : Soma.Dependent.WiredIn) : PrimTypeRegistry :=
  wiredIn.roles.fold (init := {}) fun acc role infos =>
    match infos with
    | #[info] =>
      match Soma.Dependent.WiredRole.primType? role with
      | some prim => acc.insert info.name.id prim
      | none => acc
    | _ => acc

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

/-- Emit a panic instruction followed by a dummy return value -/
def emitPanic (ty : Ty n) : LowerM n LocalId := do
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
  | .pureIO => .pureIO
  | .bindIO => .bindIO

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

/-- Resolve an intrinsic from a qualified name -/
private def resolveIntrinsic? (qn : QualifiedName)
    (ctxIntrinsics : Std.HashMap QualifiedName Intrinsic := {}) : Option Intrinsic :=
  ctxIntrinsics.get? qn |>.orElse fun _ => intrinsicOfQName? qn

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

/-- Convert a PrimType to an Alloy Ty -/
partial def convertPrimToAlloyTy (prim : PrimType) (params : List Value) (ctx : TypeConvCtx n) : Ty n :=
  match prim with
  | .int | .int32 => .prim .i32
  | .long | .int64 => .prim .i64
  | .short | .int16 => .prim .i16
  | .byte | .int8 => .prim .i8
  | .float => .prim .f32
  | .double => .prim .f64
  | .bool => .prim .bool
  | .string => Ty.string
  | .unit => .prim .unit
  | .closurePtr => .rawPtr
  | .word8 => .prim .u8
  | .word16 => .prim .u16
  | .word32 => .prim .u32
  | .word64 => .prim .u64
  | .io => match params with
    | [innerTy] => convertValueTypeWithMapping innerTy ctx
    | _ => .prim .unit
  | .array | .list | .ref | .ptr => .rawPtr

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

/-- Byte offset of the refcount field -/
def flatArrayRefcountOffset : Nat := 4

/-- Byte offset of the length field -/
def flatArrayLengthOffset : Nat := 8

/-- Byte offset of the element data -/
def flatArrayDataOffset : Nat := 16

/-- Size of the flat array header in bytes -/
def flatArrayHeaderSize : Nat := 16

/-- Emit the 8-byte flat array header: tag=4, elem_size, pad, refcount=1 -/
def emitFlatArrayHeader (bufPtr : LocalId) (elemSizeBytes : Nat) : LowerM n Unit := do
  let headerVal : Nat :=
    flatArrayTag + (elemSizeBytes <<< 8) + (1 <<< 32)
  let hdr ← LowerM.emitInst (.copy (.const (.int (Int.ofNat headerVal) .i64))) (.prim .i64)
  LowerM.emitVoid (.store (.local bufPtr) (.local hdr))

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
  /-- Expected result type from the consumer context -/
  expectedResultTy : Option (Ty n) := none
  /-- LocalIds known to hold list-typed (flat array) values -/
  listTypedLocals : Std.HashSet Nat := {}
  deriving Inhabited

namespace NodeState

def snapshotResults (s : NodeState n) : Std.HashMap Nat LocalId := s.results

def restoreResults (s : NodeState n) (snapshot : Std.HashMap Nat LocalId) : NodeState n :=
  { s with results := snapshot }

/-- Build a type conversion context from this node state -/
def toTypeConvCtx (s : NodeState n) : TypeConvCtx n :=
  { tyVars := s.tyVarMapping, primTypes := s.primTypes }

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

/-- Lower a string literal via runtime allocation for uniform ownership semantics -/
def lowerString (stringIdx : Nat) (_len : Nat) : LowerM n LocalId := do
  let cstr ← LowerM.emitInst (.copy (.const (.string stringIdx 0))) .rawPtr
  LowerM.emitInst (.callIntrinsic .fromCString #[.local cstr] Ty.string) Ty.string

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

/-- Emit eager type-directed tagged-union duplication by cloning payload buffers -/
partial def emitTaggedDup (inputVal : LocalId) (taggedTy : Ty n) (label : UInt32)
    : StateT (NodeState n) (LowerM n) (LocalId × LocalId) := do
  let tagVal ← StateT.lift (LowerM.emitInst (.extractField (.local inputVal) 0) (.prim .u32))
  let payloadPtr ← StateT.lift (LowerM.emitInst (.extractField (.local inputVal) 1) .rawPtr)
  let lbl : Operand := .const (.int (Int.ofNat label.toNat) .u32)
  let payload1 ← StateT.lift (LowerM.emitInst (.callExtern "soma_clone_tagged_payload" #[.local payloadPtr, lbl] .rawPtr) .rawPtr)
  let copy1 ← StateT.lift (LowerM.emitInst (.structLit #[.local tagVal, .local payload1] taggedTy) taggedTy)
  pure (inputVal, copy1)

/-- Emit refcount-based array duplication -/
partial def emitArrayHeaderDup (inputVal : LocalId) (srcTy : Ty n) (_label : UInt32)
    : StateT (NodeState n) (LowerM n) (LocalId × LocalId) := do
  let inputPtr ← match srcTy with
    | .prim .i64 =>
      StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local inputVal)) .rawPtr)
    | .rawPtr | .ptr _ =>
      pure inputVal
    | _ =>
      panic! s!"ALLOY LOWERING BUG: array DUP expected pointer-like source type, got {srcTy}"
  -- Load refcount from offset 4 (u32)
  let ptrAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local inputPtr)) (.prim .i64))
  let rcOffset ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayRefcountOffset) .i64))) (.prim .i64))
  let rcAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local ptrAsI64) (.local rcOffset) (.prim .i64)) (.prim .i64))
  let rcPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local rcAddr)) .rawPtr)
  let oldRc ← StateT.lift (LowerM.emitInst (.load (.local rcPtr) (.prim .u32)) (.prim .u32))
  let one ← StateT.lift (LowerM.emitInst (.copy (.const (.int 1 .u32))) (.prim .u32))
  let newRc ← StateT.lift (LowerM.emitInst (.binOp .add (.local oldRc) (.local one) (.prim .u32)) (.prim .u32))
  StateT.lift (LowerM.emitVoid (.store (.local rcPtr) (.local newRc)))
  -- Both copies share the same pointer
  pure (inputVal, inputVal)

/-- Lower an operand with FuncId map -/
partial def lowerOperandWithMap (graph : CGraph) (port : CPortId) (funcIdMap : FuncIdMap)
    : StateT (NodeState n) (LowerM n) LocalId := do
  let ns ← get

  -- Check if this specific port was already bound
  if let some cached := ns.results.get? (port.node.id * 1000 + port.port.idx) then
    return cached

  -- Special case: accessing a LAM's var port means we want the parameter
  if port.port.idx == 1 then
    if let some paramIdx := ns.lamParams.get? port.node.id then
      return ⟨paramIdx⟩

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
        if nodeTy.dupTier == .heap && !nodeTy.canInlineDup && Ty.supportsLazySup nodeTy then
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

/-- Lower a node with FuncId mapping for closure references -/
partial def lowerNodeWithMap (graph : CGraph) (nodeId : CNodeId) (funcIdMap : FuncIdMap)
    : StateT (NodeState n) (LowerM n) LocalId := do
  let ns ← get

  -- Check memoization cache
  if let some result := ns.results.get? nodeId.id then
    return result

  -- Cycle detection
  if ns.processing.contains nodeId.id then
    let ty := ns.expectedResultTy.getD valueType
    return ← StateT.lift (LowerM.emitPanic ty)

  -- Mark as processing
  modify fun s => { s with processing := s.processing.insert nodeId.id }

  -- Missing node: should not happen in well-formed graphs
  let some entry := graph.getNode nodeId | do
    let ty := ns.expectedResultTy.getD valueType
    return ← StateT.lift (LowerM.emitPanic ty)

  let ctx := ns.toTypeConvCtx
  let nodeTy := getNodeTypeWithMapping entry ctx

  let getPortType (portIdx : Nat) (defaultTy : Ty n := nodeTy) : Ty n :=
    match entry.getPort ⟨portIdx⟩ with
    | some targetPort =>
      match graph.getNode targetPort.node with
      | some targetEntry => getNodeTypeWithMapping targetEntry ctx
      | none => defaultTy
    | none => defaultTy

  let lowerPort (portIdx : Nat) (defaultTy : Ty n := nodeTy) : StateT (NodeState n) (LowerM n) LocalId := do
    match entry.getPort ⟨portIdx⟩ with
    | some targetPort => lowerOperandWithMap graph targetPort funcIdMap
    | none => StateT.lift (LowerM.emitPanic defaultTy)

  let result ← match entry.node with
  | .num primTy val =>
    StateT.lift (lowerNum primTy val)

  | .era => do
    -- ERA nodes erase the value connected to their principal port.
    -- Emit cleanup only for types that own heap memory (needsErase)
    match entry.getPort ⟨0⟩ with
    | some sourcePort =>
      match graph.getNode sourcePort.node with
      | some sourceEntry =>
        let sourceTy := getNodeTypeWithMapping sourceEntry ctx
        if sourceTy.needsErase then
          let sourceVal ← lowerOperandWithMap graph sourcePort funcIdMap
          StateT.lift (LowerM.emitVoid (.erase (.local sourceVal) sourceTy))
      | none => pure ()
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
                let result ← match funcRef with
                  | .local funcId =>
                    let typeArgs? := extractCallTypeArgs def_.ty chain.baseEntry.ty ctx
                    match typeArgs? with
                    | some typeArgs =>
                      StateT.lift (LowerM.emitInst (.callPoly funcId typeArgs argOps callRetTy) callRetTy)
                    | none =>
                      StateT.lift (LowerM.emitInst (.call funcId argOps callRetTy) callRetTy)
                  | .external name =>
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
      let maybeIntrinsic ← match fnPort with
        | some fp =>
          match graph.getNode fp.node with
          | some fnEntry =>
            match fnEntry.node with
            | .ref refId | .alo refId =>
              match graph.getDefinition refId with
              | some def_ =>
                match resolveIntrinsic? def_.name lsUnsaturated.ctxIntrinsics with
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
        let retTy : Ty n := match intrinsicOp.fixedRetTy with
          | some t => ClosedTy.embed t
          | none => nodeTy
        StateT.lift (LowerM.emitInst (.callIntrinsic intrinsicOp #[.local argVal] retTy) retTy)
      | some (Sum.inr externName) =>
        -- Extern function: emit callExtern
        StateT.lift (LowerM.emitInst (.callExtern externName #[.local argVal] nodeTy) nodeTy)
      | none =>
        -- Regular function call: check what the function node is
        match fnPort with
        | none =>
          -- No function port → erased function call
          StateT.lift (LowerM.emitPanic nodeTy)
        | some fp =>
          match graph.getNode fp.node with
          | none =>
            -- Missing function node
            StateT.lift (LowerM.emitPanic nodeTy)
          | some fnEntry =>
            match fnEntry.node with
            | .era =>
              -- Function is ERA → erased function call
              StateT.lift (LowerM.emitPanic nodeTy)
            | .lam _ =>
              lowerNodeWithMap graph fp.node funcIdMap
            | .ref refId | .alo refId =>
              let def_? := graph.getDefinition refId
              let defArity := match def_? with
                | some def_ => def_.arity
                | none => 1
              let ls ← StateT.lift get
              let funcRef := buildFuncRefFromBookRef graph refId (some funcIdMap) ls.ctxIntrinsics
              let typeArgs? := def_?.bind fun def_ =>
                extractCallTypeArgs def_.ty fnEntry.ty ctx
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
                  StateT.lift (LowerM.emitInst (.callExtern name #[.local argVal] callRetTy) callRetTy)
                | .intrinsic op =>
                  StateT.lift (LowerM.emitInst (.callIntrinsic op #[.local argVal] callRetTy) callRetTy)
                | .primOp _op =>
                  StateT.lift (LowerM.emitInst (.callExtern s!"primop_{_op}" #[.local argVal] callRetTy) callRetTy)
                | .externC name =>
                  StateT.lift (LowerM.emitInst (.callExtern name #[.local argVal] callRetTy) callRetTy)
            | _ =>
              -- Regular closure call: lower the function and use callClosure
              let fnNodeTy := getNodeTypeWithMapping fnEntry ctx
              if fnNodeTy == .prim .unit then
                StateT.lift (LowerM.emitPanic nodeTy)
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
          return ← StateT.lift (LowerM.emitPanic nodeTy)

      let canonRef := resolveCanonicalRef graph fnPort.node
      let (funcRef, typeArgs?) ← match canonRef with
        | .bookRef refId =>
          let ls ← StateT.lift get
          let ref := buildFuncRefFromBookRef graph refId (some funcIdMap) ls.ctxIntrinsics
          let fnNodeTy := graph.getNode fnPort.node |>.map (·.ty)
          let tArgs := (graph.getDefinition refId).bind fun def_ =>
            fnNodeTy.bind fun concTy => extractCallTypeArgs def_.ty concTy ctx
          pure (ref, tArgs)
        | .dynamicValue dynNodeId =>
          -- todo: extract the function pointer at runtime.
          pure (FuncRef.external s!"$dynamic_closure_{dynNodeId.id}", none)

      -- Lower the environment (port 2)
      let envVal ← match entry.getPort ⟨2⟩ with
        | some envPort => lowerOperandWithMap graph envPort funcIdMap
        | none => StateT.lift (LowerM.emitInst (.copy (.const (.null .rawPtr))) .rawPtr)

      -- Emit makeClosure or makeClosurePoly instruction
      match typeArgs? with
      | some typeArgs =>
        StateT.lift (LowerM.emitInst (.makeClosurePoly funcRef typeArgs (.local envVal)) nodeTy)
      | none =>
        StateT.lift (LowerM.emitInst (.makeClosure funcRef (.local envVal)) nodeTy)
    else if isListValue entry.ty (← get).primTypes then
      -- List constructor: produce refcounted flat array
      -- Layout: { u8 tag=4, u8 elem_size=8, u16 pad, u32 refcount=1, i64 length, data... }
      if tag == 0 then
        -- Nil: allocate header only (16 bytes), length=0
        let sizeVal ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayHeaderSize) .i64))) (.prim .i64))
        let buf ← StateT.lift (LowerM.emitInst (.malloc (.local sizeVal)) .rawPtr)
        StateT.lift (emitFlatArrayHeader buf 8)
        -- Store length=0 at offset 8
        let bufI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local buf)) (.prim .i64))
        let lenOff ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayLengthOffset) .i64))) (.prim .i64))
        let lenAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local bufI64) (.local lenOff) (.prim .i64)) (.prim .i64))
        let lenPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local lenAddr)) .rawPtr)
        let zero ← StateT.lift (LowerM.emitInst (.copy (.const (.int 0 .i64))) (.prim .i64))
        StateT.lift (LowerM.emitVoid (.store (.local lenPtr) (.local zero)))
        StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local buf)) (.prim .i64))
      else
        -- Cons x xs: load xs.length, allocate new buffer, write header, store x, copy xs data
        let headVal ← lowerPort 1
        let tailVal ← lowerPort 2
        let tailPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local tailVal)) .rawPtr)
        -- Load tail length from offset 8
        let tailI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local tailPtr)) (.prim .i64))
        let tailLenOff ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayLengthOffset) .i64))) (.prim .i64))
        let tailLenAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local tailI64) (.local tailLenOff) (.prim .i64)) (.prim .i64))
        let tailLenPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local tailLenAddr)) .rawPtr)
        let tailLen ← StateT.lift (LowerM.emitInst (.load (.local tailLenPtr) (.prim .i64)) (.prim .i64))
        let one ← StateT.lift (LowerM.emitInst (.copy (.const (.int 1 .i64))) (.prim .i64))
        let newLen ← StateT.lift (LowerM.emitInst (.binOp .add (.local tailLen) (.local one) (.prim .i64)) (.prim .i64))
        -- Total: headerSize + newLen * 8
        let elemSize ← StateT.lift (LowerM.emitInst (.copy (.const (.int 8 .i64))) (.prim .i64))
        let dataSize ← StateT.lift (LowerM.emitInst (.binOp .mul (.local newLen) (.local elemSize) (.prim .i64)) (.prim .i64))
        let hdrSize ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayHeaderSize) .i64))) (.prim .i64))
        let totalSize ← StateT.lift (LowerM.emitInst (.binOp .add (.local hdrSize) (.local dataSize) (.prim .i64)) (.prim .i64))
        let newBuf ← StateT.lift (LowerM.emitInst (.malloc (.local totalSize)) .rawPtr)
        -- Write header
        StateT.lift (emitFlatArrayHeader newBuf 8)
        -- Store new length at offset 8
        let newBufI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local newBuf)) (.prim .i64))
        let lenOff ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayLengthOffset) .i64))) (.prim .i64))
        let lenAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local newBufI64) (.local lenOff) (.prim .i64)) (.prim .i64))
        let lenPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local lenAddr)) .rawPtr)
        StateT.lift (LowerM.emitVoid (.store (.local lenPtr) (.local newLen)))
        -- Store head at offset 16
        let headOff ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayDataOffset) .i64))) (.prim .i64))
        let headAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local newBufI64) (.local headOff) (.prim .i64)) (.prim .i64))
        let headPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local headAddr)) .rawPtr)
        let headAsI64 ← StateT.lift (LowerM.emitInst (.copy (.local headVal)) (.prim .i64))
        StateT.lift (LowerM.emitVoid (.store (.local headPtr) (.local headAsI64)))
        -- Memcpy tail data: from tail+16 to newBuf+24, size = tailLen * 8
        let tailDataSize ← StateT.lift (LowerM.emitInst (.binOp .mul (.local tailLen) (.local elemSize) (.prim .i64)) (.prim .i64))
        let tailDataOff ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayDataOffset) .i64))) (.prim .i64))
        let tailDataAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local tailI64) (.local tailDataOff) (.prim .i64)) (.prim .i64))
        let tailDataPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local tailDataAddr)) .rawPtr)
        let newDataOff ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat (flatArrayDataOffset + 8)) .i64))) (.prim .i64))
        let newDataAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local newBufI64) (.local newDataOff) (.prim .i64)) (.prim .i64))
        let newDataPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local newDataAddr)) .rawPtr)
        StateT.lift (LowerM.emitVoid (.memcpy (.local newDataPtr) (.local tailDataPtr) (.local tailDataSize)))
        StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local newBuf)) (.prim .i64))
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
    let arrayElemType? :=
      -- First check: is the record value known to be list-typed from a prior MAT?
      if ns.listTypedLocals.contains recordVal.id then some .i64
      else match entry.getPort ⟨1⟩ with
      | some recPort => match graph.getNode recPort.node with
        | some recEntry => match recEntry.node with
          | .array et => some et
          | _ => if isListValue recEntry.ty ns.primTypes then some .i64 else none
        | none => none
      | none => none
    match arrayElemType? with
    | some _elemTy => do
      -- Array-backed list projection (header layout: 8B header, 8B length, data at 16)
      let elemSize : Nat := 8
      let arrPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local recordVal)) .rawPtr)
      let baseAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local arrPtr)) (.prim .i64))
      if fieldIdx == 0 then
        -- Head: load first element from offset 16 (flatArrayDataOffset)
        let dataOff ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayDataOffset) .i64))) (.prim .i64))
        let elemAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local baseAsI64) (.local dataOff) (.prim .i64)) (.prim .i64))
        let elemPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local elemAddr)) .rawPtr)
        StateT.lift (LowerM.emitInst (.load (.local elemPtr) nodeTy) nodeTy)
      else if fieldIdx == 1 then
        -- Tail: create new refcounted array with len-1 elements
        let lenOff ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayLengthOffset) .i64))) (.prim .i64))
        let lenAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local baseAsI64) (.local lenOff) (.prim .i64)) (.prim .i64))
        let lenPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local lenAddr)) .rawPtr)
        let len ← StateT.lift (LowerM.emitInst (.load (.local lenPtr) (.prim .i64)) (.prim .i64))
        let one ← StateT.lift (LowerM.emitInst (.copy (.const (.int 1 .i64))) (.prim .i64))
        let newLen ← StateT.lift (LowerM.emitInst (.binOp .sub (.local len) (.local one) (.prim .i64)) (.prim .i64))
        -- Allocate: headerSize + newLen * elemSize
        let elemSizeVal ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat elemSize) .i64))) (.prim .i64))
        let dataSize ← StateT.lift (LowerM.emitInst (.binOp .mul (.local newLen) (.local elemSizeVal) (.prim .i64)) (.prim .i64))
        let hdrSize ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayHeaderSize) .i64))) (.prim .i64))
        let totalSize ← StateT.lift (LowerM.emitInst (.binOp .add (.local hdrSize) (.local dataSize) (.prim .i64)) (.prim .i64))
        let newBuf ← StateT.lift (LowerM.emitInst (.malloc (.local totalSize)) .rawPtr)
        -- Write header (tag + elem_size + refcount=1)
        StateT.lift (emitFlatArrayHeader newBuf elemSize)
        -- Store new length at offset 8
        let newBufI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local newBuf)) (.prim .i64))
        let newLenOff ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayLengthOffset) .i64))) (.prim .i64))
        let newLenAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local newBufI64) (.local newLenOff) (.prim .i64)) (.prim .i64))
        let newLenPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local newLenAddr)) .rawPtr)
        StateT.lift (LowerM.emitVoid (.store (.local newLenPtr) (.local newLen)))
        -- Memcpy remaining data: src = arr + dataOffset + elemSize, dst = newBuf + dataOffset
        let srcOff ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat (flatArrayDataOffset + elemSize)) .i64))) (.prim .i64))
        let srcAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local baseAsI64) (.local srcOff) (.prim .i64)) (.prim .i64))
        let srcPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local srcAddr)) .rawPtr)
        let dstOff ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayDataOffset) .i64))) (.prim .i64))
        let dstAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local newBufI64) (.local dstOff) (.prim .i64)) (.prim .i64))
        let dstPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local dstAddr)) .rawPtr)
        StateT.lift (LowerM.emitVoid (.memcpy (.local dstPtr) (.local srcPtr) (.local dataSize)))
        StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local newBuf)) (.prim .i64))
      else
        StateT.lift (LowerM.emitPanic nodeTy)
    | none =>
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
    let (_, _thenBlock, elseBlock) ← if scrutIsArray then
      -- Array-backed list: compare length at offset 8 against 0
      StateT.lift do
        let arrPtr ← LowerM.emitInst (.unOp .inttoptr (.local scrutineeVal)) .rawPtr
        let arrI64 ← LowerM.emitInst (.unOp (.ptrtoint .i64) (.local arrPtr)) (.prim .i64)
        let lenOff ← LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayLengthOffset) .i64))) (.prim .i64)
        let lenAddr ← LowerM.emitInst (.binOp .add (.local arrI64) (.local lenOff) (.prim .i64)) (.prim .i64)
        let lenPtr ← LowerM.emitInst (.unOp .inttoptr (.local lenAddr)) .rawPtr
        let len ← LowerM.emitInst (.load (.local lenPtr) (.prim .i64)) (.prim .i64)
        let zero ← LowerM.emitInst (.copy (.const (.int 0 .i64))) (.prim .i64)
        let cond ← if expectedTag == 0 then
          -- Nil: matches when length == 0
          LowerM.emitInst (.binOp .eq (.local len) (.local zero) (.prim .i64)) Ty.bool
        else
          -- Cons (or any other tag): matches when length != 0
          LowerM.emitInst (.binOp .ne (.local len) (.local zero) (.prim .i64)) Ty.bool
        let thenBlock ← LowerM.freshBlockId
        let elseBlock ← LowerM.freshBlockId
        LowerM.finishBlock (.branch (.local cond) thenBlock elseBlock) thenBlock
        pure (cond, thenBlock, elseBlock)
    else
      StateT.lift (lowerMat expectedTag scrutineeVal)
    let cacheSnapshot ← do let ns ← get; pure ns.snapshotResults

    modify fun ns => { ns with expectedResultTy := some nodeTy }

    -- Lower hit value
    let hitVal ← lowerPort 2
    -- Record the actual block we're in after lowering the hit branch
    let hitBlock ← StateT.lift LowerM.getCurrentBlockId
    let joinBlock ← StateT.lift LowerM.freshBlockId
    StateT.lift (LowerM.finishBlock (.jump joinBlock) elseBlock)

    -- Restore cache
    modify fun ns => ns.restoreResults cacheSnapshot

    match entry.getPort ⟨3⟩ with
    | some _ =>
      -- Non-exhaustive or chained match: lower miss branch normally
      let missVal ← lowerPort 3
      let missBlock ← StateT.lift LowerM.getCurrentBlockId
      StateT.lift (LowerM.finishBlock (.jump joinBlock) joinBlock)
      StateT.lift (LowerM.emitInst
        (.phi #[(Operand.local hitVal, hitBlock), (Operand.local missVal, missBlock)] nodeTy)
        nodeTy)
    | none =>
      -- Exhaustive match: miss branch is unreachable
      let ls ← StateT.lift get
      StateT.lift (LowerM.emitVoid (.panic ls.panicMsgIdx 0))
      StateT.lift (LowerM.finishBlock .unreachable joinBlock)
      pure hitVal

  | .op1 op => do
    let operandVal ← lowerPort 1
    StateT.lift (LowerM.emitInst (.unOp (convertUnOp op) (.local operandVal)) nodeTy)

  | .op2 op => do
    let lhsVal ← lowerPort 1
    let rhsVal ← lowerPort 2
    let binOp := convertBinOp op
    let opTy ← if binOp.isComparison then do
        let ls ← StateT.lift get
        pure (ls.func.getLocalType lhsVal |>.getD nodeTy)
      else pure nodeTy
    StateT.lift (LowerM.emitInst (.binOp binOp (.local lhsVal) (.local rhsVal) opTy) nodeTy)

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
      else if nodeTy == .rawPtr then
        -- Inspect source node to select the right clone strategy
        let srcNode? : Option CNode := (entry.getPort ⟨0⟩).bind fun srcPort =>
          graph.getNode srcPort.node |>.map (·.node)
        let (copy0, copy1) ← match srcNode? with
          | some (.array _) =>
            -- Arrays carry their own header; use the typed array-dup helper
            let srcTy := getPortType 0 nodeTy
            emitArrayHeaderDup inputVal srcTy label.id
          | _ =>
            let ns ← get
            let isListDup := isListValue entry.ty ns.primTypes ||
              match (entry.getPort ⟨0⟩).bind (fun p => graph.getNode p.node) with
              | some srcEntry => isListValue srcEntry.ty ns.primTypes
              | none => false
            if isListDup then
              emitArrayHeaderDup inputVal nodeTy label.id
            else
              -- Closures (LAM), algebraic-data-type cells, REF, ALO etc etc are closure-like
              let lbl : Operand := .const (.int (Int.ofNat label.id.toNat) .u32)
              let clone ← StateT.lift (LowerM.emitInst
                (.callExtern "soma_clone_closure" #[.local inputVal, lbl] .rawPtr) .rawPtr)
              pure (inputVal, clone)
        modify fun ns => { ns with
          results := ns.results.insert (nodeId.id * 1000 + 1) copy0
                     |>.insert (nodeId.id * 1000 + 2) copy1
        }
        pure inputVal
      else if Ty.supportsLazySup nodeTy then
        -- Runtime SUP: lazy duplication via superposition nodes.
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

  | .use => lowerPort 1

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

    let elemSize : Nat := 8

    -- Determine the natural element size for sext/zext decisions
    let naturalElemSize : Nat := match ctorInfo with
      | some (_, ctorEntry) =>
        if len > 0 then
          match ctorEntry.getPort ⟨1⟩ with
          | some elemPort =>
            match graph.getNode elemPort.node with
            | some elemEntry => Ty.sizeBytes (getNodeTypeWithMapping elemEntry ctx)
            | none => 8
          | none => 8
        else 8
      | none => 8

    let totalSize := flatArrayHeaderSize + len * elemSize
    let totalSizeVal ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat totalSize) .i64))) (.prim .i64))
    let buf ← StateT.lift (LowerM.emitInst (.malloc (.local totalSizeVal)) .rawPtr)

    StateT.lift (emitFlatArrayHeader buf elemSize)

    let baseAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local buf)) (.prim .i64))
    let lenOffset ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayLengthOffset) .i64))) (.prim .i64))
    let lenAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local baseAsI64) (.local lenOffset) (.prim .i64)) (.prim .i64))
    let lenPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local lenAddr)) .rawPtr)
    let lenConst ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat len) .i64))) (.prim .i64))
    StateT.lift (LowerM.emitVoid (.store (.local lenPtr) (.local lenConst)))

    match ctorInfo with
    | some (_, ctorEntry) =>
      for i in [:len] do
        let elemVal ← match ctorEntry.getPort ⟨i + 1⟩ with
          | some elemPort => lowerOperandWithMap graph elemPort funcIdMap
          | none => StateT.lift (LowerM.emitPanic (.prim .i64))
        let elemI64 ← if naturalElemSize < 8 then
          StateT.lift (LowerM.emitInst (.unOp (.sext .i64) (.local elemVal)) (.prim .i64))
        else pure elemVal
        let offsetVal ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat (flatArrayDataOffset + i * elemSize)) .i64))) (.prim .i64))
        let elemAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local baseAsI64) (.local offsetVal) (.prim .i64)) (.prim .i64))
        let elemPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local elemAddr)) .rawPtr)
        StateT.lift (LowerM.emitVoid (.store (.local elemPtr) (.local elemI64)))
    | none => pure ()

    StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local buf)) (.prim .i64))

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

    -- Flat buffer layout: { header(8), i64 length, data... }
    -- Data starts at offset 16 (after 8-byte header + 8-byte length)
    let baseAsI64 ← StateT.lift (LowerM.emitInst (.unOp (.ptrtoint .i64) (.local arrayVal)) (.prim .i64))
    let dataOffset ← StateT.lift (LowerM.emitInst (.copy (.const (.int (Int.ofNat flatArrayDataOffset) .i64))) (.prim .i64))
    let elemStride ← StateT.lift (LowerM.emitInst (.copy (.const (.int 8 .i64))) (.prim .i64))
    let indexOffset ← StateT.lift (LowerM.emitInst (.binOp .mul (.local indexVal) (.local elemStride) (.prim .i64)) (.prim .i64))
    let totalOffset ← StateT.lift (LowerM.emitInst (.binOp .add (.local dataOffset) (.local indexOffset) (.prim .i64)) (.prim .i64))
    let elemAddr ← StateT.lift (LowerM.emitInst (.binOp .add (.local baseAsI64) (.local totalOffset) (.prim .i64)) (.prim .i64))
    let elemPtr ← StateT.lift (LowerM.emitInst (.unOp .inttoptr (.local elemAddr)) .rawPtr)

    let elemI64 ← StateT.lift (LowerM.emitInst (.load (.local elemPtr) (.prim .i64)) (.prim .i64))
    let nodeSize := Ty.sizeBytes nodeTy
    if nodeSize < 8 then
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

/-- Lower a definition with a specific type parameter count n -/
def lowerDefinitionWithN (graph : CGraph) (def_ : CDefinition) (funcId : FuncId)
    (funcIdMap : FuncIdMap) (tyVarMapping : TyVarMapping n) (primTypes : PrimTypeRegistry)
    (intrinsics : Std.HashMap QualifiedName Intrinsic := {})
    (panicMsgIdx : Nat := 0) : Func n :=
  let ctx : TypeConvCtx n := { tyVars := tyVarMapping, primTypes }
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
      let initState : NodeState n := { tyVarMapping, primTypes, expectedResultTy := some sig.retTy }
      let (result, _) ← StateT.run (lowerNodeWithMap graph def_.root funcIdMap) initState
      if returnsUnit then LowerM.terminate .retUnit
      else LowerM.terminate (.ret (.local result))
    else
      let (bodyNode, lamParams) := collectLamChain graph def_.root def_.arity
      let bodyEntry := graph.getNode bodyNode
      let bodyTag := bodyEntry.map fun e => s!"{e.node}"
      let initState : NodeState n := { lamParams, tyVarMapping, primTypes, expectedResultTy := some sig.retTy }
      let (result, _) ← StateT.run (lowerNodeWithMap graph bodyNode funcIdMap) initState
      if returnsUnit then LowerM.terminate .retUnit
      else LowerM.terminate (.ret (.local result))

  func

/-- Lower a Circuit definition to an Alloy function -/
def lowerDefinition (graph : CGraph) (def_ : CDefinition) (funcId : FuncId)
    (funcIdMap : FuncIdMap) (primTypes : PrimTypeRegistry)
    (intrinsics : Std.HashMap QualifiedName Intrinsic := {})
    (panicMsgIdx : Nat := 0) : SomeFunc :=
  -- Collect all type variable levels and build mapping
  let ⟨n, tyVarMapping⟩ := buildTyVarMappingFromDefinition graph def_
  -- Lower with the determined n
  let func := lowerDefinitionWithN graph def_ funcId funcIdMap tyVarMapping primTypes intrinsics panicMsgIdx
  -- Return existentially quantified function
  ⟨n, func⟩

/-- Lower an entire Circuit graph to an Alloy module -/
def lowerGraph (graph : CGraph) (moduleName : String := "main") (primTypes : PrimTypeRegistry := {})
    (intrinsics : Std.HashMap QualifiedName Intrinsic := {}) : Module := Id.run do
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

  -- First pass: build mapping from Circuit book index to sequential Alloy FuncId
  let mut funcIdMap : FuncIdMap := {}
  let mut nextFuncId : Nat := 0
  for i in [:graph.book.size] do
    if let some def_ := graph.book[i]? then
      if not def_.isExternal then
        funcIdMap := funcIdMap.insert i (FuncId.mk nextFuncId)
        nextFuncId := nextFuncId + 1

  -- Second pass: lower definitions using the mapping
  for i in [:graph.book.size] do
    if let some def_ := graph.book[i]? then
      if not def_.isExternal then
        let funcId := funcIdMap.get? i |>.getD (FuncId.mk 0)
        let func := lowerDefinition graph def_ funcId funcIdMap primTypes intrinsics panicMsgIdx
        module := module.addFunc func

  -- Set main function using the mapped ID
  if let some (idx, _) := graph.findDefinitionByDisplay "main" then
    if let some mappedId := funcIdMap.get? idx then
      module := module.withMain mappedId

  module

/-- Main entry point: lower a Circuit graph to an Alloy module -/
def lower (graph : CGraph) (moduleName : String := "main") (primTypes : PrimTypeRegistry := {})
    (intrinsics : Std.HashMap QualifiedName Intrinsic := {}) : Module :=
  lowerGraph graph moduleName primTypes intrinsics

end Somac.Alloy.Lower
