import Somac.Circuit.Graph
import Somac.Circuit.Node
import Somac.Circuit.Term
import Somac.Circuit.PatternMatch
import Soma.Core.Module
import Soma.Core.Function
import Soma.Core.Value
import Soma.Core.Eval
import Soma.Core.Quantity
import Soma.Core.Expr
import Soma.Core.Intrinsic
import Soma.Core.Literal
import Soma.Dependent.Monad
import Soma.Unique
import Std.Data.HashMap

namespace Somac.Circuit.Lower

open Somac.Circuit.Graph (Graph GraphM Reducibility enumList)
open Somac.Circuit.Node (Node NodeId PortId PortIdx Label)
open Somac.Circuit.Term (Op1Code Op2Code PrimType)
open Somac.Circuit.Term (PrimType)
open Soma.Core (Literal Value Quantity PrimOp FFIOp Intrinsic QualifiedName)
open Soma (Unique)

/-- Usage map: maps local unique id to exact usage count from type checking -/
abbrev UsageMap := Std.HashMap Unique Nat

/-- Convert TCState.usages to UsageMap for clear boundaries -/
def UsageMap.fromTCUsages (usages : Std.HashMap Unique Nat) : UsageMap := usages

structure VarAlloc where
  /-- Current owned source port for this binding -/
  source : PortId
  /-- Remaining dynamic uses available for this binding -/
  remaining : Nat
  /-- Original variable name (for debugging) -/
  name : String
  /-- Type of the bound variable -/
  ty : Value
  /-- Whether this binding is erased -/
  erased : Bool := false
  deriving Inhabited

/-- The unit type used for erased/void values -/
def unitTy : Value := Value.vPrimTy .unit

/-- The integer type -/
def intTy : Value := Value.vPrimTy .int

/-- The boolean type -/
def boolTy : Value := Value.vPrimTy .bool

/-- The string type -/
def stringTy : Value := Value.vPrimTy .string

/-- Variant label registry: assigns collision-free deterministic tags to variant -/
structure VariantTagRegistry where
  /-- Label name → assigned tag -/
  labelToTag : Std.HashMap String Nat := {}
  /-- Assigned tag → label name -/
  tagToLabel : Std.HashMap Nat String := {}
  deriving Inhabited

namespace VariantTagRegistry

/-- The tag space upper bound -/
private def tagSpace : Nat := 0xFFFF

/-- FNV-1a hash of a string, folded to tag space -/
private def fnv1aTag (label : String) : Nat :=
  let fnvOffsetBasis : UInt64 := 14695981039346656037
  let fnvPrime : UInt64 := 1099511628211
  let hash := label.foldl (init := fnvOffsetBasis) fun h c =>
    (h ^^^ c.toNat.toUInt64) * fnvPrime
  hash.toNat % tagSpace

/-- Resolve a variant label to a collision-free tag -/
def resolve (reg : VariantTagRegistry) (label : String)
    : Nat × VariantTagRegistry :=
  match reg.labelToTag.get? label with
  | some tag => (tag, reg)
  | none =>
    let candidate := fnv1aTag label
    let rec probe (tag : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => tag
      | fuel + 1 =>
        match reg.tagToLabel.get? tag with
        | none => tag
        | some existing =>
          if existing == label then tag
          else probe ((tag + 1) % tagSpace) fuel
    let finalTag := probe candidate tagSpace
    (finalTag, {
      labelToTag := reg.labelToTag.insert label finalTag
      tagToLabel := reg.tagToLabel.insert finalTag label
    })

end VariantTagRegistry

/-- Lowering context tracks variable bindings -/
structure LowerCtx where
  /-- Variable allocations by local unique id -/
  bindings : Std.HashMap Unique VarAlloc := {}
  /-- Global function QualifiedName → book index -/
  globals : Std.HashMap QualifiedName Nat := {}
  /-- Constructor QualifiedName → (type QualifiedName, tag, arity) -/
  constructors : Std.HashMap QualifiedName (QualifiedName × Nat × Nat) := {}
  /-- Constructor type registry for field type lookup during pattern matching -/
  ctorTypeRegistry : PatternMatch.ConstructorTypeRegistry := {}
  /-- Current function QualifiedName (for recursion detection) -/
  currentFn : Option QualifiedName := none
  /-- Usage counts from type checking (Unique → exact count) -/
  usageMap : UsageMap := {}
  /-- Intrinsic dispatch table from elaboration/type-checking -/
  intrinsics : Std.HashMap QualifiedName Intrinsic := {}
  /-- Global type registry: QualifiedName → full Value type (for type synthesis) -/
  globalTypes : Std.HashMap QualifiedName Value := {}
  /-- Variant label → tag registry -/
  variantTags : VariantTagRegistry := {}
  /-- Next synthetic local id used during lowering -/
  nextSyntheticId : Nat := 0
  /-- Global environment for evaluating type annotations -/
  evalGlobalEnv : Soma.Core.GlobalEnv := .empty
  /-- Metavariable solutions from type checking -/
  metaState : Soma.Core.MetaState := .empty
  /-- Type abbreviation environment for unfolding parameterized type aliases -/
  abbrevEnv : Soma.Dependent.AbbrevEnv := {}
  deriving Inhabited

namespace LowerCtx

def empty : LowerCtx := {}

/-- Register an ownership-based variable binding -/
def bindVarOwned (ctx : LowerCtx) (id : Unique) (name : String)
    (source : PortId) (remaining : Nat) (ty : Value)
    (erased : Bool := false) : LowerCtx :=
  { ctx with bindings := ctx.bindings.insert id ⟨source, remaining, name, ty, erased⟩ }

/-- Check if a binding is erased -/
def isBindingErased (ctx : LowerCtx) (id : Unique) : Bool :=
  match ctx.bindings.get? id with
  | some alloc => alloc.erased
  | none => false

/-- Look up type for a binding -/
def getVarType (ctx : LowerCtx) (id : Unique) : Option Value :=
  ctx.bindings.get? id |>.map (·.ty)

/-- Register a global function -/
def registerGlobal (ctx : LowerCtx) (name : QualifiedName) (idx : Nat) : LowerCtx :=
  { ctx with globals := ctx.globals.insert name idx }

/-- Look up a global function's book index -/
def lookupGlobal (ctx : LowerCtx) (name : QualifiedName) : Option Nat :=
  ctx.globals.get? name

/-- Register a constructor -/
def registerCtor (ctx : LowerCtx) (name : QualifiedName) (typeName : QualifiedName) (tag arity : Nat) : LowerCtx :=
  { ctx with constructors := ctx.constructors.insert name (typeName, tag, arity) }

/-- Register a constructor with its elaborated type (for pattern matching field type lookup) -/
def registerCtorType (ctx : LowerCtx) (unique : Soma.Unique) (tag : Nat)
    (ctorType : Value) : LowerCtx :=
  let info := PatternMatch.ConstructorTypeRegistry.fromElaboratedType ctorType
  { ctx with ctorTypeRegistry := ctx.ctorTypeRegistry.register unique tag info }

/-- Look up constructor info -/
def lookupCtor (ctx : LowerCtx) (name : QualifiedName) : Option (QualifiedName × Nat × Nat) :=
  ctx.constructors.get? name

/-- Look up the full type for a global -/
def lookupGlobalType (ctx : LowerCtx) (name : QualifiedName) : Option Value :=
  ctx.globalTypes.get? name

/-- Register a global function's type -/
def registerGlobalType (ctx : LowerCtx) (name : QualifiedName) (ty : Value) : LowerCtx :=
  { ctx with globalTypes := ctx.globalTypes.insert name ty }

/-- Look up usage count for a binding. Returns 1 if not found (safe default) -/
def getUsageCount (ctx : LowerCtx) (id : Unique) : Nat :=
  ctx.usageMap.getD id 1

/-- Create context with a usage map -/
def withUsageMap (usageMap : UsageMap) : LowerCtx :=
  { empty with usageMap := usageMap }

/-- Generate a fresh synthetic unique for lowering-introduced locals. -/
def freshSyntheticUnique (ctx : LowerCtx) (name : String) : Unique × LowerCtx :=
  let unique : Unique := { id := ctx.nextSyntheticId, module := "$lam", original := name }
  (unique, { ctx with nextSyntheticId := ctx.nextSyntheticId + 1 })

end LowerCtx

/-- Apply a list of arguments to a value by peeling vLam/vPi closures -/
private partial def applyArgs (v : Value) : List Value → Option Value
  | [] => some v
  | arg :: rest =>
    match v with
    | .vLam _ body => applyArgs (body.applyPure arg) rest
    | .vPi _ _ _ _ cod => applyArgs (cod.applyPure arg) rest
    | _ => none

/-- Unfold type abbreviations in a Value -/
partial def unfoldValue (v : Value) (abbrevEnv : Soma.Dependent.AbbrevEnv) : Value :=
  match v with
  | .vDataType dId params =>
    let qn : QualifiedName := ⟨dId⟩
    match abbrevEnv.get? qn with
    | some abbrevInfo =>
      if params.length == abbrevInfo.arity then
        match applyArgs abbrevInfo.expansion params with
        | some result => unfoldValue result abbrevEnv
        | none => v
      else v
    | none => v
  | _ => v

abbrev LowerM := StateT LowerCtx GraphM

namespace LowerM

/-- Run lowering and extract the graph -/
def run' (m : LowerM α) (usageMap : UsageMap := {}) : α × Graph :=
  let initialCtx := LowerCtx.withUsageMap usageMap
  let ((result, _ctx), graph) := Id.run (StateT.run (StateT.run m initialCtx) Graph.empty)
  (result, graph)

/-- Run lowering and return just the graph -/
def build (m : LowerM α) (usageMap : UsageMap := {}) : Graph :=
  (run' m usageMap).2

/-- Lift a GraphM action -/
def liftGraph (m : GraphM α) : LowerM α :=
  StateT.lift m

/-- Get the context -/
def getCtx : LowerM LowerCtx := get

/-- Set the context -/
def setCtx (ctx : LowerCtx) : LowerM Unit := set ctx

/-- Modify the context -/
def modifyCtx (f : LowerCtx → LowerCtx) : LowerM Unit := modify f

/-- Run with a temporarily modified context (restores after) -/
def withCtx (f : LowerCtx → LowerCtx) (m : LowerM α) : LowerM α := do
  let saved ← getCtx
  setCtx (f saved)
  let result ← m
  setCtx saved
  pure result

/-- Add a node to the graph -/
def addNode (n : Node) (ty : Value) : LowerM NodeId :=
  liftGraph (GraphM.addNode n ty)

/-- Connect two ports -/
def connect (p1 p2 : PortId) : LowerM Unit :=
  liftGraph (GraphM.connect p1 p2)

/-- Get a fresh DUP/SUP label -/
def freshLabel : LowerM Label :=
  liftGraph GraphM.freshLabel

/-- Get n fresh labels -/
def freshLabels (n : Nat) : LowerM (Array Label) :=
  liftGraph (GraphM.freshLabels n)

/-- Set the graph's root port -/
def setRoot (p : PortId) : LowerM Unit :=
  liftGraph (GraphM.setRoot p)

/-- Store resolved type arguments for a call site node -/
def recordTypeArgs (nodeId : NodeId) (typeArgs : Array Value) : LowerM Unit :=
  liftGraph (modify fun g => g.setResolvedTypeArgs nodeId typeArgs)

/-- Add a definition to the book -/
def addDefinition (name : QualifiedName) (root : NodeId) (arity : Nat) (ty : Value)
    (reducibility : Reducibility := .reducible) : LowerM Nat :=
  liftGraph (GraphM.addDefinition name root arity ty reducibility)

/-- Resolve a variant label to a collision-free tag -/
def resolveVariantTag (label : String) : LowerM Nat := do
  let ctx ← getCtx
  let (tag, newRegistry) := ctx.variantTags.resolve label
  setCtx { ctx with variantTags := newRegistry }
  pure tag

/-- Generate a fresh synthetic unique for lowering-introduced locals -/
def freshSyntheticUnique (name : String) : LowerM Unique := do
  let ctx ← getCtx
  let (unique, ctx') := ctx.freshSyntheticUnique name
  setCtx ctx'
  pure unique

end LowerM

/-- MonadGraph instance for LowerM -/
instance : PatternMatch.MonadGraph LowerM where
  addNode := LowerM.addNode
  connect := LowerM.connect
  freshLabel := LowerM.freshLabel
  freshLabels := LowerM.freshLabels

/-- Build a DUP chain for n uses, returning (ports, isErased)
    If n=0, connects an ERA to consume the value and returns (empty, true)
    If n=1, returns the source port directly (no DUP needed)
    If n>1, builds a chain of DUP nodes -/
def buildDupChain (sourcePort : PortId) (n : Nat) (ty : Value) : LowerM (Array PortId × Bool) := do
  if n == 0 then
    -- Erased: connect to ERA
    let era ← LowerM.addNode .era unitTy
    LowerM.connect (PortId.principal era) sourcePort
    pure (#[], true)
  else if n == 1 then
    -- Linear: direct use
    pure (#[sourcePort], false)
  else
    -- n > 1: build chain of n-1 DUP nodes
    let labels ← LowerM.freshLabels (n - 1)
    let mut usePorts : Array PortId := #[]
    let mut chainPort := sourcePort

    for i in [:n - 1] do
      let dup ← LowerM.addNode (.dup labels[i]!) ty
      -- Connect value to DUP's principal port
      LowerM.connect (PortId.principal dup) chainPort
      -- aux0 goes to a use
      usePorts := usePorts.push ⟨dup, ⟨1⟩⟩
      -- aux1 continues the chain
      chainPort := ⟨dup, ⟨2⟩⟩

    -- The final chainPort (last DUP's aux1) is the last use
    usePorts := usePorts.push chainPort
    pure (usePorts, false)

/-- Increment usage count in a map -/
private def usageInc (m : Std.HashMap Unique Nat) (id : Unique) (k : Nat := 1) : Std.HashMap Unique Nat :=
  m.insert id (m.getD id 0 + k)

/-- Pointwise addition of two usage maps -/
private def usageAdd (a b : Std.HashMap Unique Nat) : Std.HashMap Unique Nat :=
  b.fold (init := a) fun acc id cnt => usageInc acc id cnt

/-- Structural usage count for Core expressions (additive over syntax tree) -/
partial def countUsesExpr (e : Soma.Core.Expr) : Std.HashMap Unique Nat :=
  match e with
  | .fvar u _ => usageInc {} u
  | .app fn arg => usageAdd (countUsesExpr fn) (countUsesExpr arg)
  | .lam _ _ _ body => countUsesExpr body
  | .construct _ _ args _
  | .inject _ args _
  | .array args _ =>
    args.foldl (init := {}) fun acc arg => usageAdd acc (countUsesExpr arg)
  | .if_ cond then_ else_ =>
    usageAdd (countUsesExpr cond) (usageAdd (countUsesExpr then_) (countUsesExpr else_))
  | .«case» scruts arms _ =>
    let scrutUses := scruts.foldl (init := {}) fun acc s => usageAdd acc (countUsesExpr s)
    let armUses := arms.foldl (init := {}) fun acc arm => usageAdd acc (countUsesExpr arm.body)
    usageAdd scrutUses armUses
  | .fieldAccess expr _ _
  | .projFst expr
  | .projSnd expr
  | .ann expr _ => countUsesExpr expr
  | .record fields
  | .recordUpdate (.record fields) #[] =>
    fields.foldl (init := {}) fun acc (_, expr) => usageAdd acc (countUsesExpr expr)
  | .recordUpdate base updates =>
    let baseUses := countUsesExpr base
    let updUses := updates.foldl (init := {}) fun acc (_, expr) => usageAdd acc (countUsesExpr expr)
    usageAdd baseUses updUses
  | .tuple elems =>
    elems.foldl (init := {}) fun acc expr => usageAdd acc (countUsesExpr expr)
  | .pair fst snd => usageAdd (countUsesExpr fst) (countUsesExpr snd)
  | .closure _ captures =>
    captures.foldl (init := {}) fun acc cap => usageAdd acc (countUsesExpr cap)
  | .let_ _ _ val body => usageAdd (countUsesExpr val) (countUsesExpr body)
  | .panic _
  | .lit _
  | .const _ _
  | .sort _ | .pi _ _ _ _ _ | .sigma _ _ _ _ _
  | .primTy _ | .rowSort | .labelSort | .rowEmpty | .rowExtend _ _ _
  | .recordTy _ | .variantTy _ | .labelLit _ | .dataTy _ _
  | .eqTy _ _ _ _ | .refl _ _ | .transport _ _ _ _ _ _ _
  | .mvar _ | .bvar _ | .proj _ _ _ => {}

namespace LowerM

/-- Consume one use of a variable, lazily inserting DUP at the current split site -/
def consumeVar (id : Unique) : LowerM (Option (PortId × Value)) := do
  let ctx ← getCtx
  match ctx.bindings.get? id with
  | none => pure none
  | some alloc =>
    if alloc.erased then
      pure none
    else if alloc.remaining == 0 then
      pure none
    else if alloc.remaining == 1 then
      let updated : VarAlloc := { alloc with remaining := 0, erased := true }
      setCtx { ctx with bindings := ctx.bindings.insert id updated }
      pure (some (alloc.source, alloc.ty))
    else
      let label ← freshLabel
      let dup ← addNode (.dup label) alloc.ty
      connect (PortId.principal dup) alloc.source
      let usePort : PortId := ⟨dup, ⟨1⟩⟩
      let nextSource : PortId := ⟨dup, ⟨2⟩⟩
      let updated : VarAlloc := { alloc with
        source := nextSource
        remaining := alloc.remaining - 1
      }
      setCtx { ctx with bindings := ctx.bindings.insert id updated }
      pure (some (usePort, alloc.ty))

/-- Split a source value into N owned outputs at the current control-flow split site -/
def splitOwnedSource (source : PortId) (n : Nat) (ty : Value) : LowerM (Array PortId) := do
  if n == 0 then
    pure #[]
  else if n == 1 then
    pure #[source]
  else
    let (ports, _) ← buildDupChain source n ty
    pure ports

/-- Build then/else/continuation contexts for split-site lowering of `if` -/
def splitIfContexts (thenUses elseUses : Std.HashMap Unique Nat)
    : LowerM (LowerCtx × LowerCtx × LowerCtx) := do
  let ctx ← getCtx
  let mut contBindings := ctx.bindings
  let mut thenBindings := ctx.bindings
  let mut elseBindings := ctx.bindings

  for (id, alloc) in ctx.bindings.toList do
    let t := thenUses.getD id 0
    let e := elseUses.getD id 0
    let useThen := Nat.min t alloc.remaining
    let useElse := Nat.min e (alloc.remaining - useThen)
    let keep := alloc.remaining - useThen - useElse

    let needed := (if keep > 0 then 1 else 0) + (if useThen > 0 then 1 else 0) + (if useElse > 0 then 1 else 0)
    let outs ← splitOwnedSource alloc.source needed alloc.ty

    let contIdx : Nat := 0
    let thenIdx : Nat := contIdx + (if keep > 0 then 1 else 0)
    let elseIdx : Nat := thenIdx + (if useThen > 0 then 1 else 0)

    let contSource := if keep > 0 then outs[contIdx]! else alloc.source
    let thenSource := if useThen > 0 then outs[thenIdx]! else alloc.source
    let elseSource := if useElse > 0 then outs[elseIdx]! else alloc.source

    let contAlloc : VarAlloc := { alloc with source := contSource, remaining := keep, erased := keep == 0 }
    let thenAlloc : VarAlloc := { alloc with source := thenSource, remaining := useThen, erased := useThen == 0 }
    let elseAlloc : VarAlloc := { alloc with source := elseSource, remaining := useElse, erased := useElse == 0 }

    contBindings := contBindings.insert id contAlloc
    thenBindings := thenBindings.insert id thenAlloc
    elseBindings := elseBindings.insert id elseAlloc

  let contCtx : LowerCtx := { ctx with bindings := contBindings }
  let thenCtx : LowerCtx := { ctx with bindings := thenBindings }
  let elseCtx : LowerCtx := { ctx with bindings := elseBindings }
  pure (thenCtx, elseCtx, contCtx)

end LowerM

/-- Encode a signed integer as UInt32 using two's complement.
    For values that fit in 32 bits, this preserves the bit pattern. -/
def encodeSignedInt (n : Int) : UInt32 :=
  if n >= 0 then
    n.toNat.toUInt32
  else
    -- Two's complement: for negative n, compute 2^32 + n
    -- This gives the correct bit pattern for signed interpretation
    let magnitude := (-n).toNat
    if magnitude ≤ 0x80000000 then
      (0x100000000 - magnitude).toUInt32
    else
      -- Overflow: truncate to 32 bits
      ((0x100000000 - (magnitude % 0x100000000)) % 0x100000000).toUInt32

/-- Lower a literal to a node -/
def lowerLiteral (lit : Literal) : LowerM PortId := do
  match lit with
  | .int n =>
    let encoded := encodeSignedInt n
    let node := Node.num .i32 encoded
    let nid ← LowerM.addNode node intTy
    pure (PortId.principal nid)
  | .float f =>
    let doubleTy := Value.vPrimTy .double
    let bits := f.toBits
    let lo := (bits &&& 0xFFFFFFFF).toUInt32
    let hi := (bits >>> 32).toUInt32
    let nid ← LowerM.addNode (.num64 .f64 lo hi) doubleTy
    pure (PortId.principal nid)
  | .bool b =>
    let node := Node.num .bool (if b then 1 else 0)
    let nid ← LowerM.addNode node boolTy
    pure (PortId.principal nid)
  | .string s =>
    -- String literals: use STRING node
    -- Length is the byte length of the UTF-8 encoded string
    let len := s.utf8ByteSize.toUInt32
    let word64Ty := Value.vPrimTy .word64
    let lenNode ← LowerM.addNode (.num .u64 len) word64Ty

    -- Intern the string and store its index (not hash) so Alloy can reference it
    let stringIdx ← LowerM.liftGraph (GraphM.internString s)
    let dataNode ← LowerM.addNode (.num .u64 stringIdx.toUInt32) word64Ty

    -- Create STRING node
    let stringNode ← LowerM.addNode .string stringTy
    LowerM.connect ⟨stringNode, ⟨1⟩⟩ (PortId.principal lenNode) -- aux0 = length
    LowerM.connect ⟨stringNode, ⟨2⟩⟩ (PortId.principal dataNode) -- aux1 = string table index

    pure (PortId.principal stringNode)

/-- Lower a variable reference -/
def lowerVar (bindingId : Unique) : LowerM (Option PortId) := do
  let ctx ← LowerM.getCtx
  if ctx.isBindingErased bindingId then
    pure none
  else
    match ← LowerM.consumeVar bindingId with
    | some (port, _ty) =>
      pure (some port)
    | none =>
      pure none

/-- Convert a PrimOp to an Op1Code for unary operations -/
def primOpToOp1Code : PrimOp → Option Op1Code
  | .not => some .not
  | .neg => some .neg
  | _ => none

/-- Convert a PrimOp to an Op2Code for binary operations -/
def primOpToOp2Code : PrimOp → Option Op2Code
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | .mod => some .mod
  | .eq  => some .eq
  | .ne  => some .ne
  | .lt  => some .lt
  | .le  => some .le
  | .gt  => some .gt
  | .ge  => some .ge
  | .and => some .and
  | .or  => some .or
  | .not => none  -- Unary operation
  | .neg => none  -- Unary operation


/-- Lower a global function or constructor reference to a circuit node -/
def lowerGlobal (name : QualifiedName) (ty : Value) : LowerM PortId := do
  let ctx ← LowerM.getCtx
  -- First check if it's a known function
  match ctx.lookupGlobal name with
  | some idx =>
    -- Check if this is a self-recursive call
    let isSelfRecursive := ctx.currentFn == some name
    -- Check if the result type is a non-function type
    let isNullaryCall := !ty.isPi
    if isSelfRecursive || isNullaryCall then
      -- Self-recursive call or nullary function: emit ALO for instantiation
      let alo ← LowerM.addNode (.alo idx) ty
      pure (PortId.principal alo)
    else
      let ref ← LowerM.addNode (.ref idx) ty
      pure (PortId.principal ref)
  | none =>
    match ctx.lookupCtor name with
    | some (_, tag, arity) =>
      if arity == 0 then
        let ctor ← LowerM.addNode (.ctor tag 0) ty
        pure (PortId.principal ctor)
      else
        panic! s!"lowerGlobal: partial constructor application should have been desugared: {name.display}"
    | none =>
      panic! s!"lowerGlobal: unknown global '{name.display}' (not in globals, not a constructor)"

/-- Lower a first-class projection function -/
def lowerFirstClassProj (fieldIdx : Nat) (ty : Value) : LowerM PortId := do
  -- Create LAM node (not erased - the parameter is used)
  let lam ← LowerM.addNode (.lam false) ty

  -- The LAM's aux0 (var port) will receive the record argument
  let varPort : PortId := ⟨lam, ⟨1⟩⟩

  -- The projected field type is the return type of the projection function
  let proj ← LowerM.addNode (.proj fieldIdx) ty

  -- Connect: LAM.var → PROJ.input
  LowerM.connect ⟨proj, ⟨1⟩⟩ varPort

  -- Connect: PROJ.principal → LAM.body
  LowerM.connect ⟨lam, ⟨2⟩⟩ (PortId.principal proj)

  -- Return the LAM's principal port (the function value)
  pure (PortId.principal lam)

/-- Check if a Core.Expr is a primitive operation global reference -/
private partial def getCoreExprPrimOp (e : Soma.Core.Expr) : LowerM (Option PrimOp) := do
  match e with
  | .const qn _ =>
    let ctx ← LowerM.getCtx
    match ctx.intrinsics.get? qn with
    | some (.primOp op) => pure (some op)
    | _ => pure none
  | .app fn _ =>
    -- If fn is a primop applied to type-level args, propagate
    getCoreExprPrimOp fn
  | _ => pure none

/-- Check if a Core.Expr is type-level (erased at runtime) -/
private def isCoreTypeLevelExpr : Soma.Core.Expr → Bool
  | .sort _ | .pi _ _ _ _ _ | .sigma _ _ _ _ _ | .primTy _
  | .rowSort | .labelSort | .rowEmpty | .rowExtend _ _ _
  | .recordTy _ | .variantTy _ | .labelLit _ | .dataTy _ _
  | .eqTy _ _ _ _ | .refl _ _ | .transport _ _ _ _ _ _ _
  | .mvar _ | .bvar _ => true
  | _ => false

/-- Compute the type of a Core expression -/
def getExprType (e : Soma.Core.Expr) : LowerM Value := do
  let ctx ← LowerM.getCtx
  pure (e.typeOf ctx.evalGlobalEnv (unfoldValue · ctx.abbrevEnv))

/-- Evaluate a Core expression to a Value -/
def evalExprToValue (e : Soma.Core.Expr) : LowerM Value := do
  let ctx ← LowerM.getCtx
  let evalCtx : Soma.Core.EvalCtx := {
    env := .empty
    globals := ctx.evalGlobalEnv
    metas := ctx.metaState
  }
  pure (Soma.Core.evalCoreExpr evalCtx e)

/-- Lower a Core.Expr variable (fvar) by looking up its Unique.id in the bindings map -/
private def lowerCoreVar (u : Unique) : LowerM (Option PortId) := do
  lowerVar u

mutual

/-- Lower a Core.Expr to a Circuit IR subgraph. -/
partial def lowerCoreExpr (e : Soma.Core.Expr) (ty : Value) : LowerM (Option PortId) := do
  match e with
  | .fvar u _ => lowerCoreVar u

  | .lit lit => some <$> lowerLiteral lit

  | .app fn arg => lowerCoreApp fn arg ty

  | .lam info name _domain body => some <$> lowerCoreLam info name body ty

  | .construct _qn tag args _ => lowerCoreConstruct tag args ty

  | .if_ cond then_ else_ => lowerCoreIf cond then_ else_ ty

  | .«case» scruts arms _ => lowerCoreCase scruts arms ty

  | .const qn _ => some <$> lowerGlobal qn ty

  | .fieldAccess expr _field idx => lowerCoreFieldAccess expr idx ty

  | .record fields => lowerCoreRecord fields ty

  | .tuple elems => lowerCoreTuple elems ty

  | .pair fst snd => lowerCorePair fst snd ty

  | .projFst e => lowerCoreProj e 0 ty

  | .projSnd e => lowerCoreProj e 1 ty

  | .panic msg =>
    let word64Ty := Value.vPrimTy .word64
    let word32Ty := Value.vPrimTy .word
    let msgNode ← LowerM.addNode (Node.num .u64 msg.hash.toUInt32) word64Ty
    let msgPort := PortId.principal msgNode
    let lineNode ← LowerM.addNode (Node.num .u32 0) word32Ty
    let panicTag := 0xFFFF
    let panicCtor ← LowerM.addNode (.ctor panicTag 2) ty
    LowerM.connect ⟨panicCtor, ⟨1⟩⟩ msgPort
    LowerM.connect ⟨panicCtor, ⟨2⟩⟩ (PortId.principal lineNode)
    pure (some (PortId.principal panicCtor))

  | .ann expr _ty => lowerCoreExpr expr ty

  | .closure qn captures => lowerCoreClosure qn captures ty

  | .array elems _ => lowerCoreArray elems (← getExprType e)

  | .proj _typeName _field idx => some <$> lowerFirstClassProj idx ty

  | .inject label args _ => lowerCoreInject label args ty

  | .recordUpdate base updates => lowerCoreRecordUpdate base updates ty

  | .let_ _name _ty val body => do
    -- Open the body by replacing bvar(0) with an fvar, then lower as a bound variable
    let letUnique ← LowerM.freshSyntheticUnique _name
    let fvarBody := Soma.Core.Expr.instantiate body (Soma.Core.Expr.fvar letUnique _ty)
    let annotationTy := Soma.Core.evalClosed _ty
    let usageCount := fvarBody.countFVar letUnique
    let valPort? ← lowerCoreExpr val annotationTy
    match valPort? with
    | none =>
      -- val is type-level (erased) so we just lower the body directly
      lowerCoreExpr fvarBody ty
    | some valPort =>
      let valTy ← do
        match ← LowerM.liftGraph (get >>= fun g => pure (g.getNode valPort.node)) with
        | some entry => pure entry.ty
        | none => pure annotationTy
      if usageCount == 0 then
        -- Emit a USE node to force evaluation of the value before continuing with the body
        let bodyPort? ← lowerCoreExpr fvarBody ty
        match bodyPort? with
        | none =>
          -- Body is type-level, just return none
          pure none
        | some bodyPort =>
          let useNode ← LowerM.addNode .use ty
          LowerM.connect ⟨useNode, ⟨1⟩⟩ valPort
          LowerM.connect ⟨useNode, ⟨2⟩⟩ bodyPort
          pure (some (PortId.principal useNode))
      else
        LowerM.modifyCtx fun ctx =>
          ctx.bindVarOwned letUnique _name valPort usageCount valTy false
        lowerCoreExpr fvarBody ty

  -- Type-level constructs (erased at runtime)
  | .sort _ | .pi _ _ _ _ _ | .sigma _ _ _ _ _
  | .primTy _ | .rowSort | .labelSort | .rowEmpty
  | .rowExtend _ _ _ | .recordTy _ | .variantTy _
  | .labelLit _ | .dataTy _ _ | .eqTy _ _ _ _
  | .refl _ _ | .transport _ _ _ _ _ _ _
  | .mvar _ | .bvar _ =>
    pure none

/-- Lower a Core.Expr function application -/
partial def lowerCoreApp (fn arg : Soma.Core.Expr) (ty : Value)
    : LowerM (Option PortId) := do
  let rec collectAppSpine (e : Soma.Core.Expr) (args : Array Soma.Core.Expr)
      : Soma.Core.Expr × Array Soma.Core.Expr :=
    match e with
    | .app fn' arg' => collectAppSpine fn' (#[arg'] ++ args)
    | _ => (e, args)
  let (baseFn, allArgs) := collectAppSpine fn #[arg]

  if isCoreTypeLevelExpr baseFn then
    return none

  match baseFn with
  | .const qn _ =>
    let ctx ← LowerM.getCtx
    match ctx.lookupCtor qn with
    | some (_, tag, arity) =>
      let explicitArgs := allArgs.filter (!isCoreTypeLevelExpr ·)
      if explicitArgs.size == arity then
        lowerCoreConstruct tag explicitArgs ty
      else
        lowerCoreAppDefault fn arg ty
    | none =>
      let typeArgExprs := allArgs.filter isCoreTypeLevelExpr
      if typeArgExprs.size > 0 then
        let mut typeArgVals : Array Value := #[]
        for e in typeArgExprs do
          let v ← evalExprToValue e
          typeArgVals := typeArgVals.push v
        let result ← lowerCoreAppDefault fn arg ty
        match ctx.lookupGlobal qn with
        | some _idx =>
          match result with
          | some resultPort =>
            let mut curNode := resultPort.node
            for _ in [:allArgs.size + 2] do
              let nodeEntry? ← LowerM.liftGraph (get >>= fun g => pure (g.getNode curNode))
              match nodeEntry? with
              | some nodeEntry => match nodeEntry.node with
                | .app => match nodeEntry.getPort ⟨1⟩ with
                  | some fnPort => curNode := fnPort.node
                  | none => break
                | .ref _ | .alo _ =>
                  LowerM.recordTypeArgs curNode typeArgVals
                  break
                | _ => break
              | none => break
          | none => pure ()
        | none => pure ()
        pure result
      else
        lowerCoreAppDefault fn arg ty
  | _ => lowerCoreAppDefault fn arg ty

/-- Default application lowering -/
partial def lowerCoreAppDefault (fn arg : Soma.Core.Expr) (ty : Value)
    : LowerM (Option PortId) := do
  -- Check for binary primop: f x y where f is a primop
  match fn with
  | .app innerFn innerArg =>
    match ← getCoreExprPrimOp innerFn with
    | some primOp =>
      match primOpToOp2Code primOp with
      | some op2 =>
        let argTy ← getExprType innerArg
        let arg1Port? ← lowerCoreExpr innerArg argTy
        let arg2Port? ← lowerCoreExpr arg argTy
        match arg1Port?, arg2Port? with
        | some arg1Port, some arg2Port =>
          let op2Node ← LowerM.addNode (.op2 op2) ty
          LowerM.connect ⟨op2Node, ⟨1⟩⟩ arg1Port
          LowerM.connect ⟨op2Node, ⟨2⟩⟩ arg2Port
          pure (some (PortId.principal op2Node))
        | _, _ => lowerCoreAppGeneric fn arg ty
      | none => lowerCoreAppGeneric fn arg ty
    | none => lowerCoreAppGeneric fn arg ty
  | _ =>
    -- Check for unary primop
    match ← getCoreExprPrimOp fn with
    | some primOp =>
      match primOpToOp1Code primOp with
      | some op1 =>
        let argTy ← getExprType arg
        let argPort? ← lowerCoreExpr arg argTy
        match argPort? with
        | some argPort =>
          let op1Node ← LowerM.addNode (.op1 op1) ty
          LowerM.connect ⟨op1Node, ⟨1⟩⟩ argPort
          pure (some (PortId.principal op1Node))
        | none => lowerCoreAppGeneric fn arg ty
      | none => lowerCoreAppGeneric fn arg ty
    | none =>
      -- Check if arg is type-level (erased)
      if isCoreTypeLevelExpr arg then
        lowerCoreExpr fn ty
      else
        lowerCoreAppGeneric fn arg ty

/-- Generic application lowering for Core.Expr -/
partial def lowerCoreAppGeneric (fn arg : Soma.Core.Expr) (ty : Value)
    : LowerM (Option PortId) := do
  let fnTy ← getExprType fn
  let ctx ← LowerM.getCtx
  -- Unfold type abbreviations if needed
  let effectiveFnTy := match fnTy.piDomain? with
    | some _ => fnTy
    | none => unfoldValue fnTy ctx.abbrevEnv
  match effectiveFnTy.piDomain? with
  | none =>
    -- Type-level or erased application
    pure none
  | some argTy =>
    -- Compute the actual result type from the Pi codomain
    let resultTy := match effectiveFnTy.piApply (Value.vNeutral argTy (.nVar ⟨"_", ⟨0⟩⟩)) with
      | some codTy => codTy
      | none => ty
    let fnPort? ← lowerCoreExpr fn fnTy
    match fnPort? with
    | none => pure none
    | some fnPort =>
      let argPort? ← lowerCoreExpr arg argTy
      match argPort? with
      | some argPort =>
        let app ← LowerM.addNode .app resultTy
        LowerM.connect ⟨app, ⟨1⟩⟩ fnPort
        LowerM.connect ⟨app, ⟨2⟩⟩ argPort
        pure (some (PortId.principal app))
      | none =>
        pure (some fnPort)

/-- Lower a Core.Expr lambda -/
partial def lowerCoreLam (_info : Soma.Core.BinderInfo) (name : String)
    (body : Soma.Core.Expr) (ty : Value) : LowerM PortId := do
  -- The body uses bvar(0) for the lambda parameter (locally nameless).
  -- Instantiate bvar(0) with fvar(u) so it can be looked up during lowering.
  let paramUnique ← LowerM.freshSyntheticUnique name
  let paramTyExpr := match ty.piDomain? with
    | some d => Soma.Core.quoteExpr0 d
    | none => .sort .zero
  let openBody := Soma.Core.Expr.instantiate body (.fvar paramUnique paramTyExpr)

  let usageCount := openBody.countFVar paramUnique
  let erased := usageCount == 0

  let lam ← LowerM.addNode (.lam erased) ty
  let paramTy := match ty.piDomain? with
    | some d => d
    | none => panic! s!"lowerCoreLam: expected Pi type for parameter, got {ty}"

  let varPort : PortId := ⟨lam, ⟨1⟩⟩
  let isErased := usageCount == 0
  LowerM.modifyCtx fun ctx =>
    ctx.bindVarOwned paramUnique name varPort usageCount paramTy isErased

  -- Lower the opened body
  let paramNeutral := Value.vNeutral paramTy (.nVar ⟨name, ⟨paramUnique.id⟩⟩)
  let codomainTy := match ty.piApply paramNeutral with
    | some t => t
    | none => panic! s!"lowerCoreLam: expected Pi type for codomain, got {ty}"
  let bodyPort? ← lowerCoreExpr openBody codomainTy
  let bodyPort := bodyPort?.getD ⟨lam, ⟨1⟩⟩
  LowerM.connect ⟨lam, ⟨2⟩⟩ bodyPort

  pure (PortId.principal lam)

/-- Lower a Core.Expr constructor application -/
partial def lowerCoreConstruct (tag : Nat) (args : Array Soma.Core.Expr)
    (ty : Value) : LowerM (Option PortId) := do
  let mut argPorts : Array PortId := #[]
  for arg in args do
    let argTy ← getExprType arg
    let port? ← lowerCoreExpr arg argTy
    match port? with
    | some port => argPorts := argPorts.push port
    | none => pure ()

  let ctor ← LowerM.addNode (.ctor tag argPorts.size) ty
  for i in [:argPorts.size] do
    LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ argPorts[i]!

  pure (some (PortId.principal ctor))

/-- Lower a Core.Expr if-then-else -/
partial def lowerCoreIf (cond then_ else_ : Soma.Core.Expr) (ty : Value)
    : LowerM (Option PortId) := do
  let condPort? ← lowerCoreExpr cond boolTy
  match condPort? with
  | none => pure none
  | some condPort =>
    let thenUses := countUsesExpr then_
    let elseUses := countUsesExpr else_
    let (thenCtx, elseCtx, contCtx) ← LowerM.splitIfContexts thenUses elseUses

    let savedCtx ← LowerM.getCtx
    LowerM.setCtx { savedCtx with bindings := thenCtx.bindings }
    let thenPort? ← lowerCoreExpr then_ ty

    let afterThenCtx ← LowerM.getCtx
    LowerM.setCtx { afterThenCtx with bindings := elseCtx.bindings }
    let elsePort? ← lowerCoreExpr else_ ty

    let afterElseCtx ← LowerM.getCtx
    LowerM.setCtx { afterElseCtx with bindings := contCtx.bindings }

    let thenPort := match thenPort? with
      | some p => p
      | none => condPort -- Fallback
    let elsePort := match elsePort? with
      | some p => p
      | none => condPort -- Fallback

    let mat ← LowerM.addNode (.mat 1) ty
    LowerM.connect ⟨mat, ⟨1⟩⟩ condPort -- aux0 = scrutinee
    LowerM.connect ⟨mat, ⟨2⟩⟩ thenPort -- aux1 = hit (True)
    LowerM.connect ⟨mat, ⟨3⟩⟩ elsePort -- aux2 = miss (False)
    pure (some (PortId.principal mat))

/-- Lower a Core.Expr case expression using existing PatternMatch infrastructure -/
partial def lowerCoreCase (scruts : Array Soma.Core.Expr) (arms : Array Soma.Core.Arm)
    (ty : Value) : LowerM (Option PortId) := do
  -- Lower scrutinees
  let mut scrutPorts : Array PortId := #[]
  let mut scrutTypes : Array Value := #[]
  for scrut in scruts do
    let scrutTy ← getExprType scrut
    let port? ← lowerCoreExpr scrut scrutTy
    match port? with
    | some port =>
      scrutPorts := scrutPorts.push port
      scrutTypes := scrutTypes.push scrutTy
    | none => pure ()

  if scrutPorts.isEmpty then
    pure none
  else
    let ctx ← LowerM.getCtx
    let variantLabels := PatternMatch.collectArmsVariantLabels arms
    let mut variantTagMap : Std.HashMap String Nat := {}
    for label in variantLabels do
      let tag ← LowerM.resolveVariantTag label
      variantTagMap := variantTagMap.insert label tag
    let simplifyCtx : PatternMatch.SimplifyCtx := { variantTags := variantTagMap }
    let matrix := PatternMatch.buildMatrixFromArms simplifyCtx arms
    let tree := PatternMatch.compileMatrix matrix ctx.ctorTypeRegistry scrutTypes

    -- Compute additive usage counts from arm bodies for split-site DUP placement.
    -- The usageMap uses max-counting across branches (suitable for
    -- binding-site placement), but split-site placement needs the total uses across
    -- ALL branches so that splitIfContexts can distribute copies to each branch.
    let mut splitSiteUsages : UsageMap := {}
    for arm in arms do
      let bindingIds := arm.patterns.foldl
        (fun acc p => acc ++ p.collectBindingIds) #[]
      let openedBody := bindingIds.foldr
        (fun uid body => body.instantiate (.fvar uid (.sort (.lit 0)))) arm.body
      let armUses := countUsesExpr openedBody
      for (id, count) in armUses.toList do
        splitSiteUsages := splitSiteUsages.insert id (splitSiteUsages.getD id 0 + count)

    let result ← PatternMatch.lower tree scrutPorts scrutTypes ctx.ctorTypeRegistry ty
      (fun armIndex armCtx => lowerCoreArmBodyByIndex arms armIndex armCtx)
      splitSiteUsages
    pure (some result)
where
  /-- Lower the body of a case arm by index -/
  lowerCoreArmBodyByIndex (arms : Array Soma.Core.Arm) (idx : Nat)
      (armCtx : PatternMatch.ArmContext) : LowerM PortId := do
    if h : idx < arms.size then
      let arm := arms[idx]
      -- Open the arm body: instantiate bvars with fvars matching the pattern binding IDs.
      -- The arm body uses locally-nameless binding (bvars for pattern bindings), while
      -- the Circuit IR lowering resolves variables by fvar Unique IDs
      let bindingIds := arm.patterns.foldl
        (fun acc p => acc ++ p.collectBindingIds) #[]
      let bindingTypes : Std.HashMap Unique Value := armCtx.bindings.foldl
        (init := {}) fun m (id, _, _, _, ty) => m.insert id ty
      let openedBody := bindingIds.foldr
        (fun uid body =>
          let tyExpr := match bindingTypes.get? uid with
            | some ty => Soma.Core.quoteExpr ⟨0⟩ ty
            | none => .sort (.lit 0)
          body.instantiate (.fvar uid tyExpr)) arm.body
      -- Install bindings from armCtx into the context
      for (bindingId, name, source, useCount, varTy) in armCtx.bindings do
        let erased := useCount == 0
        LowerM.modifyCtx fun ctx =>
          ctx.bindVarOwned bindingId name source useCount varTy erased
      -- Lower the arm body
      match ← lowerCoreExpr openedBody ty with
      | some port => pure port
      | none =>
        let era ← LowerM.addNode .era ty
        pure (PortId.principal era)
    else
      let era ← LowerM.addNode .era unitTy
      pure (PortId.principal era)

/-- Lower a Core.Expr field access -/
partial def lowerCoreFieldAccess (expr : Soma.Core.Expr) (idx : Nat)
    (ty : Value) : LowerM (Option PortId) := do
  let recordTy ← getExprType expr
  let exprPort? ← lowerCoreExpr expr recordTy
  match exprPort? with
  | none => pure none
  | some exprPort =>
    let proj ← LowerM.addNode (.proj idx) ty
    LowerM.connect ⟨proj, ⟨1⟩⟩ exprPort
    pure (some (PortId.principal proj))

/-- Lower a Core.Expr record literal -/
partial def lowerCoreRecord (fields : Array (String × Soma.Core.Expr))
    (ty : Value) : LowerM (Option PortId) := do
  let rowFields := ty.recordFields
  let mut fieldPorts : Array PortId := #[]
  for i in [:fields.size] do
    let (_, e) := fields[i]!
    -- Get field type from row structure if available, otherwise infer from expression
    let fieldTy ← match rowFields[i]? with
      | some (_, ft) => pure ft
      | none => getExprType e
    let port? ← lowerCoreExpr e fieldTy
    match port? with
    | some port => fieldPorts := fieldPorts.push port
    | none => pure ()

  let rec_ ← LowerM.addNode (.record fieldPorts.size) ty
  for i in [:fieldPorts.size] do
    LowerM.connect ⟨rec_, ⟨i + 1⟩⟩ fieldPorts[i]!
  pure (some (PortId.principal rec_))

/-- Lower a Core.Expr record update -/
partial def lowerCoreRecordUpdate (base : Soma.Core.Expr)
    (updates : Array (String × Soma.Core.Expr)) (ty : Value)
    : LowerM (Option PortId) := do
  let fields := ty.recordFields
  if fields.isEmpty then
    lowerCoreExpr base ty
  else
    let mut updateMap : Std.HashMap String Soma.Core.Expr := {}
    for (name, expr) in updates do
      updateMap := updateMap.insert name expr

    -- Count how many projections we need from the base (fields NOT in updates)
    let projCount := fields.foldl (fun acc (name, _) =>
      if updateMap.contains name then acc else acc + 1) 0

    -- Lower the base and build a DUP chain for projections
    let basePort? ← lowerCoreExpr base ty
    match basePort? with
    | none => pure none
    | some basePort =>
      let (basePorts, _) ← buildDupChain basePort projCount ty
      let mut projIdx : Nat := 0
      let mut fieldPorts : Array PortId := #[]

      for i in [:fields.size] do
        let (name, fieldTy) := fields[i]!
        match updateMap.get? name with
        | some updateExpr =>
          -- Use the updated expression
          let port? ← lowerCoreExpr updateExpr fieldTy
          match port? with
          | some port => fieldPorts := fieldPorts.push port
          | none => pure ()
        | none =>
          -- Project from the base
          if h : projIdx < basePorts.size then
            let proj ← LowerM.addNode (.proj i) fieldTy
            LowerM.connect ⟨proj, ⟨1⟩⟩ basePorts[projIdx]
            fieldPorts := fieldPorts.push (PortId.principal proj)
            projIdx := projIdx + 1
          else
            pure ()

      -- Construct the new record
      let rec_ ← LowerM.addNode (.record fieldPorts.size) ty
      for i in [:fieldPorts.size] do
        LowerM.connect ⟨rec_, ⟨i + 1⟩⟩ fieldPorts[i]!
      pure (some (PortId.principal rec_))

/-- Lower a Core.Expr tuple -/
partial def lowerCoreTuple (elems : Array Soma.Core.Expr)
    (ty : Value) : LowerM (Option PortId) := do
  let mut elemPorts : Array PortId := #[]
  for e in elems do
    let elemTy ← getExprType e
    let port? ← lowerCoreExpr e elemTy
    match port? with
    | some port => elemPorts := elemPorts.push port
    | none => pure ()

  let ctor ← LowerM.addNode (.ctor 0 elemPorts.size) ty
  for i in [:elemPorts.size] do
    LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ elemPorts[i]!
  pure (some (PortId.principal ctor))

/-- Lower a Core.Expr pair -/
partial def lowerCorePair (fst snd : Soma.Core.Expr)
    (ty : Value) : LowerM (Option PortId) := do
  let (fstTy, sndTy) ← do
    match ty with
    | .vSigma _ _ fstT clos =>
      let fstVal := Soma.Core.evalCoreExpr Soma.Core.EvalCtx.empty fst
      pure (fstT, clos.applyPure fstVal)
    | _ =>
      -- For non-Sigma pair types, infer component types
      let fstTy ← getExprType fst
      let sndTy ← getExprType snd
      pure (fstTy, sndTy)
  let fstPort? ← lowerCoreExpr fst fstTy
  let sndPort? ← lowerCoreExpr snd sndTy
  match fstPort?, sndPort? with
  | none, none => pure none
  | some fstPort, some sndPort =>
    let ctor ← LowerM.addNode (.ctor 0 2) ty
    LowerM.connect ⟨ctor, ⟨1⟩⟩ fstPort
    LowerM.connect ⟨ctor, ⟨2⟩⟩ sndPort
    pure (some (PortId.principal ctor))
  | some fstPort, none =>
    let era ← LowerM.addNode .era unitTy
    let ctor ← LowerM.addNode (.ctor 0 2) ty
    LowerM.connect ⟨ctor, ⟨1⟩⟩ fstPort
    LowerM.connect ⟨ctor, ⟨2⟩⟩ (PortId.principal era)
    pure (some (PortId.principal ctor))
  | none, some sndPort =>
    let era ← LowerM.addNode .era unitTy
    let ctor ← LowerM.addNode (.ctor 0 2) ty
    LowerM.connect ⟨ctor, ⟨1⟩⟩ (PortId.principal era)
    LowerM.connect ⟨ctor, ⟨2⟩⟩ sndPort
    pure (some (PortId.principal ctor))

/-- Lower a Core.Expr projection -/
partial def lowerCoreProj (expr : Soma.Core.Expr) (idx : Nat)
    (ty : Value) : LowerM (Option PortId) := do
  let pairTy ← getExprType expr
  let exprPort? ← lowerCoreExpr expr pairTy
  match exprPort? with
  | none => pure none
  | some exprPort =>
    let proj ← LowerM.addNode (.proj idx) ty
    LowerM.connect ⟨proj, ⟨1⟩⟩ exprPort
    pure (some (PortId.principal proj))

/-- Lower a Core.Expr closure -/
partial def lowerCoreClosure (fnName : Soma.Core.QualifiedName)
    (captures : Array Soma.Core.Expr) (ty : Value) : LowerM (Option PortId) := do
  let fnPort ← lowerGlobal fnName ty

  -- Lower captures
  let mut capturePairs : Array (PortId × Value) := #[]
  for cap in captures do
    let capTy ← getExprType cap
    let port? ← lowerCoreExpr cap capTy
    match port? with
    | some port => capturePairs := capturePairs.push (port, capTy)
    | none => pure ()

  let envPort ← if capturePairs.isEmpty then do
    let era ← LowerM.addNode .era unitTy
    pure (PortId.principal era)
  else if capturePairs.size == 1 then do
    pure capturePairs[0]!.1
  else do
    let captureTypes := capturePairs.map (·.2)
    let envTy := Value.tuple captureTypes
    let ctor ← LowerM.addNode (.ctor 0 capturePairs.size) envTy
    for i in [:capturePairs.size] do
      LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ capturePairs[i]!.1
    pure (PortId.principal ctor)

  let closureCtor ← LowerM.addNode (.ctor 0xFFFE 2) ty
  LowerM.connect ⟨closureCtor, ⟨1⟩⟩ fnPort
  LowerM.connect ⟨closureCtor, ⟨2⟩⟩ envPort
  pure (some (PortId.principal closureCtor))

/-- Lower a Core.Expr array literal -/
partial def lowerCoreArray (elems : Array Soma.Core.Expr)
    (ty : Value) : LowerM (Option PortId) := do
  let elemTy := match ty.dataTypeFirstParam? with
    | some t => t
    | none => panic! s!"lowerCoreArray: expected Array type with element param, got {ty}"
  let mut elemPorts : Array PortId := #[]
  for e in elems do
    let port? ← lowerCoreExpr e elemTy
    match port? with
    | some port => elemPorts := elemPorts.push port
    | none => pure ()

  let len := elemPorts.size
  let word64Ty := Value.vPrimTy .word64
  let lenNode ← LowerM.addNode (.num .u64 len.toUInt32) word64Ty
  let backingTy := Value.tuple (List.replicate len elemTy).toArray
  let dataNode ← LowerM.addNode (.ctor 0xFFFD len) backingTy
  for i in [:len] do
    LowerM.connect ⟨dataNode, ⟨i + 1⟩⟩ elemPorts[i]!

  let arrayNode ← LowerM.addNode (.array .i64) ty
  LowerM.connect ⟨arrayNode, ⟨1⟩⟩ (PortId.principal lenNode)
  LowerM.connect ⟨arrayNode, ⟨2⟩⟩ (PortId.principal dataNode)
  pure (some (PortId.principal arrayNode))

/-- Lower a Core.Expr variant injection -/
partial def lowerCoreInject (label : String) (args : Array Soma.Core.Expr)
    (ty : Value) : LowerM (Option PortId) := do
  let mut argPorts : Array PortId := #[]
  for arg in args do
    let argTy ← getExprType arg
    let port? ← lowerCoreExpr arg argTy
    match port? with
    | some port => argPorts := argPorts.push port
    | none => pure ()

  let tag ← LowerM.resolveVariantTag label
  let ctor ← LowerM.addNode (.ctor tag argPorts.size) ty
  for i in [:argPorts.size] do
    LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ argPorts[i]!
  pure (some (PortId.principal ctor))

end

/-- Lower a function definition -/
def lowerFunction (fn : Soma.Core.TypedFunction) : LowerM NodeId := do
  -- Set current function for recursion detection
  LowerM.modifyCtx fun ctx => { ctx with currentFn := some fn.name }

  -- Create LAM nodes for parameters
  let paramList := fn.params.toList
  let mut lamNodes : Array NodeId := #[]
  let mut currentTy := fn.fnType
  let bodyUses := countUsesExpr fn.body

  let mut currentTy' := currentTy
  let mut done := false
  while !done do
    match currentTy' with
    | .vPi _ binder name dom cod =>
      let isErasedImplicit := match binder with
        | .implicit | .strictImplicit =>
          match dom with
          | .vType _ | .vRowSort | .vLabelSort => true
          | _ => false
        | _ => false
      if isErasedImplicit then
        let dummyArg := Value.vNeutral dom (.nVar ⟨name, cod.env.level⟩)
        currentTy' := cod.applyPure dummyArg
      else
        done := true
    | _ => done := true
  currentTy := currentTy'

  for param in paramList do
    let (bindingId, name) := param
    let usageCount := bodyUses.getD bindingId 0
    let erased := usageCount == 0
    let lam ← LowerM.addNode (.lam erased) currentTy
    lamNodes := lamNodes.push lam

    let paramTy := match currentTy.piDomain? with
      | some d => d
      | none => panic! s!"lowerFunction: expected Pi type for param '{name}', got {currentTy}"
    let paramNeutral := Value.vNeutral paramTy (.nVar ⟨name, ⟨bindingId.id⟩⟩)
    currentTy := match currentTy.piApply paramNeutral with
      | some c => c
      | none => panic! s!"lowerFunction: expected Pi type for codomain after '{name}', got {currentTy}"

    -- Register ownership-based binding, DUP will be inserted lazily at split sites
    let varPort : PortId := ⟨lam, ⟨1⟩⟩
    -- Bind the variable with its erasure status
    LowerM.modifyCtx fun ctx =>
      ctx.bindVarOwned bindingId name varPort usageCount paramTy erased

  -- Wire LAMs together
  for i in [:lamNodes.size - 1] do
    let outer := lamNodes[i]!
    let inner := lamNodes[i + 1]!
    LowerM.connect ⟨outer, ⟨2⟩⟩ (PortId.principal inner)

  -- Lower the body (now Core.Expr)
  let resultTy := currentTy  -- type remaining after peeling all param Pis
  let bodyPort? ← lowerCoreExpr fn.body resultTy

  if lamNodes.isEmpty then
    -- No parameters: body is the root
    match bodyPort? with
    | some port => pure port.node
    | none =>
      let era ← LowerM.addNode .era unitTy
      pure era
  else
    -- Wire body to innermost LAM
    let innermost := lamNodes[lamNodes.size - 1]!
    let bodyPort := match bodyPort? with
      | some port => port
      | none => ⟨innermost, ⟨1⟩⟩
    LowerM.connect ⟨innermost, ⟨2⟩⟩ bodyPort
    pure lamNodes[0]!

/-- Register type definitions and builds the constructor type registry from type checker globals if provided -/
def registerTypes (types : Array Soma.Core.TypeDef)
    (globals : Option Soma.Dependent.Globals := none) : LowerM Unit := do
  for typeDef in types do
    match typeDef with
    | .algebraic _attrs typeName _tvars ctors =>
      let mut usedMetadata := false
      if let some g := globals then
        if let some typeQN := g.resolve #[] #[] typeName.display then
          if let some indInfo := g.lookupInductive typeQN then
            usedMetadata := true
            for ctor in indInfo.ctors do
              LowerM.modifyCtx fun ctx =>
                ctx.registerCtor ctor.name typeName ctor.tag ctor.arity
              LowerM.modifyCtx fun ctx =>
                ctx.registerCtorType typeQN.id ctor.tag ctor.type
      if !usedMetadata then
        for ctor in ctors do
          let arity := ctor.fieldTypeSyntax.size
          LowerM.modifyCtx fun ctx =>
            ctx.registerCtor ctor.name typeName ctor.tag arity

          if let some g := globals then
            if let some typeQN := g.resolve #[] #[] typeName.display then
              if let some ctorMeta := g.lookupCtor typeQN ctor.name.id.original then
                LowerM.modifyCtx fun ctx =>
                  ctx.registerCtorType typeQN.id ctor.tag ctorMeta.type

    | .record _attrs recordName _tvars ctorName fields =>
      let mut usedMetadata := false
      if let some g := globals then
        if let some typeQN := g.resolve #[] #[] recordName.display then
          if let some indInfo := g.lookupInductive typeQN then
            usedMetadata := true
            for ctor in indInfo.ctors do
              LowerM.modifyCtx fun ctx =>
                ctx.registerCtor ctor.name recordName ctor.tag ctor.arity
              LowerM.modifyCtx fun ctx =>
                ctx.registerCtorType typeQN.id ctor.tag ctor.type
      if !usedMetadata then
        let arity := fields.size
        LowerM.modifyCtx fun ctx =>
          ctx.registerCtor ctorName recordName 0 arity

        if let some g := globals then
          if let some typeQN := g.resolve #[] #[] recordName.display then
            if let some ctorMeta := g.lookupCtor typeQN "New" then
              LowerM.modifyCtx fun ctx =>
                ctx.registerCtorType typeQN.id 0 ctorMeta.type

/-- Map from function name to typed function -/
abbrev TypedFunctionMap := Std.HashMap String Soma.Core.TypedFunction

/-- Check if a function should be lowered to actual code -/
def shouldLowerBody (fn : Soma.Core.TypedFunction) : Bool :=
  fn.attrs.intrinsic.isNone && fn.attrs.extern.isNone

/-- Generate a proper Circuit IR function body for a primitive operation -/
def generatePrimOpBody (op : PrimOp) (fnTy : Value) : LowerM (NodeId × Nat) := do
  match primOpToOp2Code op with
  | some op2 =>
    -- Binary operation: 2 parameters
    let paramTy := fnTy.piDomain?.getD intTy
    let lamOuter ← LowerM.addNode (.lam false) fnTy
    -- Compute inner type (codomain after applying first param)
    let innerTy := match fnTy.piApply (Value.vNeutral paramTy (.nVar ⟨"x", ⟨0⟩⟩)) with
      | some t => t
      | none => fnTy
    let lamInner ← LowerM.addNode (.lam false) innerTy
    -- Result type (codomain after applying both params)
    let resultTy := match innerTy.piApply (Value.vNeutral paramTy (.nVar ⟨"y", ⟨0⟩⟩)) with
      | some t => t
      | none => paramTy
    let opNode ← LowerM.addNode (.op2 op2) resultTy
    -- Wire LAMs: outer.body → inner
    LowerM.connect ⟨lamOuter, ⟨2⟩⟩ (PortId.principal lamInner)
    -- Wire inner.body → op2
    LowerM.connect ⟨lamInner, ⟨2⟩⟩ (PortId.principal opNode)
    -- Wire variables to op2 inputs
    LowerM.connect ⟨opNode, ⟨1⟩⟩ ⟨lamOuter, ⟨1⟩⟩ -- first param
    LowerM.connect ⟨opNode, ⟨2⟩⟩ ⟨lamInner, ⟨1⟩⟩ -- second param
    pure (lamOuter, 2)
  | none =>
    match primOpToOp1Code op with
    | some op1 =>
      -- Unary operation: 1 parameter
      let resultTy := match fnTy.piApply (Value.vNeutral unitTy (.nVar ⟨"x", ⟨0⟩⟩)) with
        | some t => t
        | none => fnTy
      let lamNode ← LowerM.addNode (.lam false) fnTy
      let opNode ← LowerM.addNode (.op1 op1) resultTy
      -- Wire body to op1
      LowerM.connect ⟨lamNode, ⟨2⟩⟩ (PortId.principal opNode)
      -- Wire variable to op1 input
      LowerM.connect ⟨opNode, ⟨1⟩⟩ ⟨lamNode, ⟨1⟩⟩
      pure (lamNode, 1)
    | none =>
      -- Unknown op: fallback to ERA placeholder
      let era ← LowerM.addNode .era unitTy
      pure (era, 0)

/-- Lower an entire module using typed functions from type checking -/
def lowerModule (types : Array Soma.Core.TypeDef)
    (typedFunctions : TypedFunctionMap)
    (globals : Option Soma.Dependent.Globals := none)
    (instanceEnv : Soma.Dependent.InstanceEnv := .empty)
    (metas : Soma.Core.MetaState := .empty)
    (abbrevEnv : Soma.Dependent.AbbrevEnv := {}) : LowerM Unit := do
  -- Load abbreviation environment for type alias unfolding
  LowerM.modifyCtx fun ctx => { ctx with abbrevEnv := abbrevEnv }
  -- Load intrinsic dispatch metadata from elaboration/type checking.
  if let some g := globals then
    LowerM.modifyCtx fun ctx => { ctx with
      intrinsics := g.intrinsics
      evalGlobalEnv := g.toGlobalEnvWithClasses instanceEnv
      metaState := metas
    }

  -- Register global types for type synthesis during lowering.
  for (_, fn) in typedFunctions do
    LowerM.modifyCtx fun ctx => ctx.registerGlobalType fn.name fn.fnType
  if let some g := globals then
    for (_, info) in g.allDecls do
      LowerM.modifyCtx fun ctx => ctx.registerGlobalType info.name info.type

  -- Register type constructors from current module
  registerTypes types globals

  -- Register constructors from external dependencies
  if let some g := globals then
    for (_, info) in g.allDecls do
      if info.isConstructor then
        let ctx ← LowerM.getCtx
        let ctorQN := info.name
        if ctx.lookupCtor ctorQN |>.isNone then
          let arity := info.type.explicitArityFull
          LowerM.modifyCtx fun ctx =>
            ctx.registerCtor ctorQN ctorQN info.ctorTag arity

  -- Get list of functions to lower (only those that should be lowered)
  let functions := typedFunctions.toList.filter fun (_, fn) => shouldLowerBody fn

  let intrinsics := typedFunctions.toList.filter fun (_, fn) => not (shouldLowerBody fn)

  -- First pass: register all local functions that will be lowered as globals
  -- Use the index in the filtered list (which matches the book index)
  for (i, (_, fn)) in enumList functions do
    LowerM.modifyCtx fun ctx => ctx.registerGlobal fn.name i

  -- Second pass: register intrinsic/extern functions from the current module
  -- Their book indices start after local functions
  let localCount := functions.length
  for (i, (_, fn)) in enumList intrinsics do
    LowerM.modifyCtx fun ctx => ctx.registerGlobal fn.name (localCount + i)

  -- Third pass: register external functions from dependencies
  -- Their book indices start after all local functions
  let intrinsicCount := intrinsics.length
  if let some g := globals then
    let preCtx ← LowerM.getCtx
    let allExternalCandidates := g.allDecls
    let externals := allExternalCandidates.filter fun (_, info) =>
      let alreadyRegistered := preCtx.globals.contains info.name
      !alreadyRegistered && !info.isConstructor
        && info.origin != .typeDecl && info.origin != .projection
    for (i, (_, info)) in enumList externals do
      LowerM.modifyCtx fun ctx =>
        ctx.registerGlobal info.name (localCount + intrinsicCount + i)

  -- Fourth pass: lower each function body and add to book
  for (_, fn) in functions do
    let root ← lowerFunction fn
    let arity := fn.params.size
    let red := if fn.attrs.irreducible then Reducibility.irreducible else .reducible
    let _ ← LowerM.addDefinition fn.name root arity fn.fnType (reducibility := red)

  -- Fifth pass: add definitions for intrinsic/extern functions from current module
  for (_, fn) in intrinsics do
    let ctx ← LowerM.getCtx
    match ctx.intrinsics.get? fn.name with
    | some (.primOp op) =>
      let (root, arity) ← generatePrimOpBody op fn.fnType
      let _ ← LowerM.addDefinition fn.name root arity fn.fnType
    | _ =>
      let era ← LowerM.addNode .era unitTy
      let arity := fn.fnType.explicitArityFull
      let _ ← LowerM.addDefinition fn.name era arity fn.fnType (reducibility := .external)

  -- Sixth pass: add placeholder definitions for external functions from dependencies
  if let some g := globals then
    let pass6Ctx ← LowerM.getCtx
    let externals := g.allDecls.filter fun (_, info) =>
      let isLocalOrIntrinsic := match pass6Ctx.globals.get? info.name with
        | some idx => idx < localCount + intrinsicCount
        | none => false
      !isLocalOrIntrinsic && !info.isConstructor
        && info.origin != .typeDecl && info.origin != .projection
    for (_, info) in externals do
      let era ← LowerM.addNode .era unitTy
      let arity := info.type.explicitArityFull
      let _ ← LowerM.addDefinition info.name era arity info.type (reducibility := .external)

  -- Set root to main function if it exists
  -- Wire an ERA demand node to the root ALO so demand-driven evaluation can proceed
  let ctx ← LowerM.getCtx
  let mainEntry := ctx.globals.toList.find? fun (name, _) => name.id.original == "main"
  match mainEntry with
  | some (_, idx) =>
    let mainTy := match typedFunctions.get? "main" with
      | some typedFn => typedFn.fnType
      | none => unitTy
    let alo ← LowerM.addNode (.alo idx) mainTy
    -- Check if main returns IO (a function World → Pair World a)
    let effectiveMainTy := match mainTy.piDomain? with
      | some _ => mainTy
      | none => unfoldValue mainTy ctx.abbrevEnv
    let resultTy := match effectiveMainTy.piApply (Value.vPrimTy .world) with
      | some codTy => codTy
      | none => mainTy
    match effectiveMainTy.piDomain? with
    | some _ =>
      -- main : IO a = World → Pair World a
      let worldNum ← LowerM.addNode (.num .u64 0) (Value.vPrimTy .world)
      let app ← LowerM.addNode .app resultTy
      LowerM.connect ⟨app, ⟨1⟩⟩ (PortId.principal alo)
      LowerM.connect ⟨app, ⟨2⟩⟩ (PortId.principal worldNum)
      let era ← LowerM.addNode .era unitTy
      LowerM.connect (PortId.principal era) (PortId.principal app)
      LowerM.setRoot (PortId.principal era)
    | none =>
      -- main : pure value, just ERA it
      let era ← LowerM.addNode .era unitTy
      LowerM.connect (PortId.principal era) (PortId.principal alo)
      LowerM.setRoot (PortId.principal era)
  | none =>
    let era ← LowerM.addNode .era unitTy
    LowerM.setRoot (PortId.principal era)

/-- Lower typed functions to Circuit IR -/
def lower (types : Array Soma.Core.TypeDef)
    (typedFunctions : TypedFunctionMap)
    (usageMap : UsageMap)
    (globals : Option Soma.Dependent.Globals := none)
    (instanceEnv : Soma.Dependent.InstanceEnv := .empty)
    (metas : Soma.Core.MetaState := .empty)
    (abbrevEnv : Soma.Dependent.AbbrevEnv := {}) : Graph :=
  LowerM.build (lowerModule types typedFunctions globals instanceEnv metas abbrevEnv) usageMap

end Somac.Circuit.Lower
