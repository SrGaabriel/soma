import Somac.Circuit.Graph
import Somac.Circuit.Node
import Somac.Circuit.Term
import Somac.Circuit.PatternMatch
import Soma.Core.Module
import Soma.Core.Function
import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Expr
import Soma.Core.Intrinsic
import Soma.Core.Literal
import Soma.Dependent.Monad
import Soma.Unique
import Std.Data.HashMap

namespace Somac.Circuit.Lower

open Somac.Circuit.Graph (Graph GraphM enumList)
open Somac.Circuit.Node (Node NodeId PortId PortIdx Label)
open Somac.Circuit.Term (Op1Code Op2Code PrimType)
open Somac.Circuit.Term (PrimType)
open Soma.Core (Literal Value Quantity PrimOp FFIOp Intrinsic QualifiedName)
open Soma (Unique)

/-- Usage map: maps local unique id to exact usage count from type checking -/
abbrev UsageMap := Std.HashMap Unique Nat

/-- Convert TCState.usages to UsageMap for clear boundaries -/
def UsageMap.fromTCUsages (usages : Std.HashMap Unique Nat) : UsageMap := usages

/-- A port allocation for a variable binding -/
structure VarAlloc where
  /-- Ports available for use (one per remaining use) -/
  ports : Array PortId
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

/-- Lowering context tracks variable bindings -/
structure LowerCtx where
  /-- Variable allocations by local unique id -/
  bindings : Std.HashMap Nat VarAlloc := {}
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
  deriving Inhabited

namespace LowerCtx

def empty : LowerCtx := {}

/-- Register a variable binding with pre-allocated ports -/
def bindVar (ctx : LowerCtx) (id : Unique) (name : String) (ports : Array PortId) (ty : Value)
    (erased : Bool := false) : LowerCtx :=
  { ctx with bindings := ctx.bindings.insert id.id ⟨ports, name, ty, erased⟩ }

/-- Check if a binding is erased -/
def isBindingErased (ctx : LowerCtx) (id : Unique) : Bool :=
  match ctx.bindings.get? id.id with
  | some alloc => alloc.erased
  | none => false

/-- Consume one use of a variable, returning the port and type for that use -/
def useVar (ctx : LowerCtx) (id : Unique) : Option (PortId × Value × LowerCtx) :=
  match ctx.bindings.get? id.id with
  | none => none
  | some alloc =>
    if alloc.erased then none
    else if alloc.ports.isEmpty then none
    else
      let port := alloc.ports[0]!
      let remaining := alloc.ports.extract 1 alloc.ports.size
      let newAlloc : VarAlloc := ⟨remaining, alloc.name, alloc.ty, alloc.erased⟩
      let ctx' := { ctx with bindings := ctx.bindings.insert id.id newAlloc }
      some (port, alloc.ty, ctx')

/-- Look up type for a binding -/
def getVarType (ctx : LowerCtx) (id : Unique) : Option Value :=
  ctx.bindings.get? id.id |>.map (·.ty)

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

/-- Look up usage count for a binding. Returns 1 if not found (safe default) -/
def getUsageCount (ctx : LowerCtx) (id : Unique) : Nat :=
  ctx.usageMap.getD id 1

/-- Create context with a usage map -/
def withUsageMap (usageMap : UsageMap) : LowerCtx :=
  { empty with usageMap := usageMap }

end LowerCtx

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

/-- Add a definition to the book -/
def addDefinition (name : QualifiedName) (root : NodeId) (arity : Nat) (ty : Value)
    (isExternal : Bool := false) : LowerM Nat :=
  liftGraph (GraphM.addDefinition name root arity ty isExternal)

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
    -- Use two's complement for proper signed integer representation
    let encoded := encodeSignedInt n
    let node := Node.num .i32 encoded
    let nid ← LowerM.addNode node intTy
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
    match ctx.useVar bindingId with
    | some (port, _ty, ctx') =>
      LowerM.setCtx ctx'
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

/-- Convert UsageMap (keyed by Unique) to Std.HashMap Nat Nat (keyed by raw id) -/
def usageMapToNatMap (usageMap : UsageMap) : Std.HashMap Nat Nat :=
  usageMap.fold (init := {}) fun acc bindingId count =>
    acc.insert bindingId.id count

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
  | .const qn =>
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

/-- Lower a Core.Expr variable (fvar) by looking up its Unique.id in the bindings map -/
private def lowerCoreVar (u : Unique) : LowerM (Option PortId) := do
  lowerVar u

mutual

/-- Lower a Core.Expr to a Circuit IR subgraph. -/
partial def lowerCoreExpr (e : Soma.Core.Expr) (ty : Value) : LowerM (Option PortId) := do
  match e with
  | .fvar u => lowerCoreVar u

  | .lit lit => some <$> lowerLiteral lit

  | .app fn arg => lowerCoreApp fn arg ty

  | .lam info name _domain body => some <$> lowerCoreLam info name body ty

  | .construct _qn tag args => lowerCoreConstruct tag args ty

  | .if_ cond then_ else_ => lowerCoreIf cond then_ else_ ty

  | .«case» scruts arms => lowerCoreCase scruts arms ty

  | .const qn => some <$> lowerGlobal qn ty

  | .fieldAccess expr _field idx => lowerCoreFieldAccess expr idx ty

  | .record fields => lowerCoreRecord fields ty

  | .tuple elems => lowerCoreTuple elems ty

  | .pair fst snd => lowerCorePair fst snd ty

  | .projFst e => lowerCoreProj e 0 ty

  | .projSnd e => lowerCoreProj e 1 ty

  | .panic msg =>
    let word64Ty := Value.vPrimTy .word64
    let word32Ty := Value.vPrimTy .word32
    let msgNode ← LowerM.addNode (Node.num .u64 msg.hash.toUInt32) word64Ty
    let msgPort := PortId.principal msgNode
    let lineNode ← LowerM.addNode (Node.num .u32 0) word32Ty
    let panicTag := 0xFFFFFF
    let panicCtor ← LowerM.addNode (.ctor panicTag 2) ty
    LowerM.connect ⟨panicCtor, ⟨1⟩⟩ msgPort
    LowerM.connect ⟨panicCtor, ⟨2⟩⟩ (PortId.principal lineNode)
    pure (some (PortId.principal panicCtor))

  | .ann expr _ty => lowerCoreExpr expr ty

  | .closure qn captures => lowerCoreClosure qn captures ty

  | .array elems => lowerCoreArray elems ty

  | .proj _typeName _field idx => some <$> lowerFirstClassProj idx ty

  | .inject label args => lowerCoreInject label args ty

  | .recordUpdate base updates => lowerCoreRecordUpdate base updates ty

  | .let_ _name _ty val body => do
    -- Lower let as immediate application: (λx. body) val
    -- Bind val, then lower body
    lowerCoreExpr (.app (.lam .explicit _name _ty body) val) ty

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
  -- Check for binary primop: f x y where f is a primop
  match fn with
  | .app innerFn innerArg =>
    match ← getCoreExprPrimOp innerFn with
    | some primOp =>
      match primOpToOp2Code primOp with
      | some op2 =>
        let arg1Port? ← lowerCoreExpr innerArg unitTy
        let arg2Port? ← lowerCoreExpr arg unitTy
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
        let argPort? ← lowerCoreExpr arg unitTy
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
  let fnPort? ← lowerCoreExpr fn unitTy
  match fnPort? with
  | none => pure none
  | some fnPort =>
    let argPort? ← lowerCoreExpr arg unitTy
    match argPort? with
    | some argPort =>
      let app ← LowerM.addNode .app ty
      LowerM.connect ⟨app, ⟨1⟩⟩ fnPort
      LowerM.connect ⟨app, ⟨2⟩⟩ argPort
      pure (some (PortId.principal app))
    | none =>
      -- Arg is erased, just return fn
      pure (some fnPort)

/-- Lower a Core.Expr lambda -/
partial def lowerCoreLam (_info : Soma.Core.BinderInfo) (name : String)
    (body : Soma.Core.Expr) (ty : Value) : LowerM PortId := do
  -- The body uses bvar(0) for the lambda parameter (locally nameless).
  -- Instantiate bvar(0) with fvar(u) so it can be looked up during lowering.
  let paramUnique : Unique := { id := name.hash.toNat, module := "$lam", original := name }
  let openBody := Soma.Core.Expr.instantiate body (.fvar paramUnique)

  -- Count how many times the param is actually used in the opened body
  let usageCount := if openBody.hasFVar paramUnique then
    -- Conservative: count occurrences. hasFVar just tells us it's used at all.
    1
  else
    0
  let erased := usageCount == 0

  let lam ← LowerM.addNode (.lam erased) ty
  let paramTy := ty.piDomain?.getD unitTy

  let paramBinding : Unique := { id := paramUnique.id, module := paramUnique.module, original := name }
  let varPort : PortId := ⟨lam, ⟨1⟩⟩
  let (usePorts, isErased) ← buildDupChain varPort usageCount paramTy
  LowerM.modifyCtx fun ctx => ctx.bindVar paramBinding name usePorts paramTy isErased

  -- Lower the opened body
  let bodyPort? ← lowerCoreExpr openBody (ty.piCodomain?.getD unitTy)
  let bodyPort := bodyPort?.getD ⟨lam, ⟨1⟩⟩
  LowerM.connect ⟨lam, ⟨2⟩⟩ bodyPort

  pure (PortId.principal lam)

/-- Lower a Core.Expr constructor application -/
partial def lowerCoreConstruct (tag : Nat) (args : Array Soma.Core.Expr)
    (ty : Value) : LowerM (Option PortId) := do
  let mut argPorts : Array PortId := #[]
  for arg in args do
    let port? ← lowerCoreExpr arg unitTy
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
  let condPort? ← lowerCoreExpr cond unitTy
  match condPort? with
  | none => pure none
  | some condPort =>
    let thenPort? ← lowerCoreExpr then_ ty
    let elsePort? ← lowerCoreExpr else_ ty

    let thenPort := match thenPort? with
      | some p => p
      | none => condPort -- Fallback
    let elsePort := match elsePort? with
      | some p => p
      | none => condPort -- Fallback

    let mat ← LowerM.addNode (.mat 2) ty
    LowerM.connect (PortId.principal mat) condPort
    LowerM.connect ⟨mat, ⟨1⟩⟩ elsePort -- Branch 0 (false)
    LowerM.connect ⟨mat, ⟨2⟩⟩ thenPort -- Branch 1 (true)
    pure (some (PortId.principal mat))

/-- Lower a Core.Expr case expression using existing PatternMatch infrastructure -/
partial def lowerCoreCase (scruts : Array Soma.Core.Expr) (arms : Array Soma.Core.Arm)
    (ty : Value) : LowerM (Option PortId) := do
  -- Lower scrutinees
  let mut scrutPorts : Array PortId := #[]
  let mut scrutTypes : Array Value := #[]
  for scrut in scruts do
    let port? ← lowerCoreExpr scrut unitTy
    match port? with
    | some port =>
      scrutPorts := scrutPorts.push port
      scrutTypes := scrutTypes.push unitTy
    | none => pure ()

  if scrutPorts.isEmpty then
    pure none
  else
    let ctx ← LowerM.getCtx
    let simplifyCtx : PatternMatch.SimplifyCtx := {}
    let matrix := PatternMatch.buildMatrixFromArms simplifyCtx arms
    let tree := PatternMatch.compileMatrix matrix ctx.ctorTypeRegistry scrutTypes
    let usageCounts := usageMapToNatMap ctx.usageMap

    let result ← PatternMatch.lower tree scrutPorts scrutTypes ctx.ctorTypeRegistry ty
      (fun armIndex armCtx => lowerCoreArmBodyByIndex arms armIndex armCtx)
      usageCounts
    pure (some result)
where
  /-- Lower the body of a case arm by index -/
  lowerCoreArmBodyByIndex (arms : Array Soma.Core.Arm) (idx : Nat)
      (armCtx : PatternMatch.ArmContext) : LowerM PortId := do
    if h : idx < arms.size then
      let arm := arms[idx]
      -- Install bindings from armCtx into the context
      for (bindingId, name, ports, varTy) in armCtx.bindings do
        LowerM.modifyCtx fun ctx => ctx.bindVar bindingId name ports varTy
      -- Lower the arm body
      match ← lowerCoreExpr arm.body unitTy with
      | some port => pure port
      | none =>
        let era ← LowerM.addNode .era unitTy
        pure (PortId.principal era)
    else
      let era ← LowerM.addNode .era unitTy
      pure (PortId.principal era)

/-- Lower a Core.Expr field access -/
partial def lowerCoreFieldAccess (expr : Soma.Core.Expr) (idx : Nat)
    (ty : Value) : LowerM (Option PortId) := do
  let exprPort? ← lowerCoreExpr expr unitTy
  match exprPort? with
  | none => pure none
  | some exprPort =>
    let proj ← LowerM.addNode (.proj idx) ty
    LowerM.connect ⟨proj, ⟨1⟩⟩ exprPort
    pure (some (PortId.principal proj))

/-- Lower a Core.Expr record literal -/
partial def lowerCoreRecord (fields : Array (String × Soma.Core.Expr))
    (ty : Value) : LowerM (Option PortId) := do
  let mut fieldPorts : Array PortId := #[]
  for (_, e) in fields do
    let port? ← lowerCoreExpr e unitTy
    match port? with
    | some port => fieldPorts := fieldPorts.push port
    | none => pure ()

  let rec_ ← LowerM.addNode (.record fieldPorts.size) ty
  for i in [:fieldPorts.size] do
    LowerM.connect ⟨rec_, ⟨i + 1⟩⟩ fieldPorts[i]!
  pure (some (PortId.principal rec_))

/-- Lower a Core.Expr record update -/
partial def lowerCoreRecordUpdate (base : Soma.Core.Expr)
    (_updates : Array (String × Soma.Core.Expr)) (ty : Value)
    : LowerM (Option PortId) := do
  -- Record update requires knowing field names from the record type
  lowerCoreExpr base ty

/-- Lower a Core.Expr tuple -/
partial def lowerCoreTuple (elems : Array Soma.Core.Expr)
    (ty : Value) : LowerM (Option PortId) := do
  let mut elemPorts : Array PortId := #[]
  for e in elems do
    let port? ← lowerCoreExpr e unitTy
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
  let fstPort? ← lowerCoreExpr fst unitTy
  let sndPort? ← lowerCoreExpr snd unitTy
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
  let exprPort? ← lowerCoreExpr expr unitTy
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
    let port? ← lowerCoreExpr cap unitTy
    match port? with
    | some port => capturePairs := capturePairs.push (port, unitTy)
    | none => pure ()

  let envPort ← if capturePairs.isEmpty then do
    let ctor ← LowerM.addNode (.ctor 0 0) unitTy
    pure (PortId.principal ctor)
  else do
    let captureTypes := capturePairs.map (·.2)
    let envTy := Value.tuple captureTypes
    let ctor ← LowerM.addNode (.ctor 0 capturePairs.size) envTy
    for i in [:capturePairs.size] do
      LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ capturePairs[i]!.1
    pure (PortId.principal ctor)

  let closureCtor ← LowerM.addNode (.ctor 0xFFFFFE 2) ty
  LowerM.connect ⟨closureCtor, ⟨1⟩⟩ fnPort
  LowerM.connect ⟨closureCtor, ⟨2⟩⟩ envPort
  pure (some (PortId.principal closureCtor))

/-- Lower a Core.Expr array literal -/
partial def lowerCoreArray (elems : Array Soma.Core.Expr)
    (ty : Value) : LowerM (Option PortId) := do
  let mut elemPorts : Array PortId := #[]
  for e in elems do
    let port? ← lowerCoreExpr e unitTy
    match port? with
    | some port => elemPorts := elemPorts.push port
    | none => pure ()

  let len := elemPorts.size
  let elemTy := ty.dataTypeFirstParam?.getD intTy
  let word64Ty := Value.vPrimTy .word64
  let lenNode ← LowerM.addNode (.num .u64 len.toUInt32) word64Ty
  let backingTy := Value.tuple (List.replicate len elemTy).toArray
  let dataNode ← LowerM.addNode (.ctor 0xFFFFFD len) backingTy
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
    let port? ← lowerCoreExpr arg unitTy
    match port? with
    | some port => argPorts := argPorts.push port
    | none => pure ()

  let tag := label.hash.toNat % 0xFFFFFF
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
  let ctx ← LowerM.getCtx
  let mut currentTy := fn.fnType

  for param in paramList do
    let (bindingId, name) := param
    -- Look up actual usage count from type checking
    let usageCount := ctx.getUsageCount bindingId
    let erased := usageCount == 0
    let lam ← LowerM.addNode (.lam erased) currentTy
    lamNodes := lamNodes.push lam

    let paramTy := currentTy.piDomain?.getD unitTy
    currentTy := currentTy.piCodomain?.getD unitTy

    -- Build DUP chain based on actual usage
    let varPort : PortId := ⟨lam, ⟨1⟩⟩
    let (usePorts, isErased) ← buildDupChain varPort usageCount paramTy
    -- Bind the variable with its erasure status
    LowerM.modifyCtx fun ctx => ctx.bindVar bindingId name usePorts paramTy isErased

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
    | .algebraic typeName _tvars ctors =>
      let mut usedMetadata := false
      if let some g := globals then
        if let some indInfo := g.lookupInductive typeName.display then
          usedMetadata := true
          for ctor in indInfo.ctors do
            LowerM.modifyCtx fun ctx =>
              ctx.registerCtor ctor.name typeName ctor.tag ctor.arity
            LowerM.modifyCtx fun ctx =>
              ctx.registerCtorType indInfo.unique ctor.tag ctor.type
      if !usedMetadata then
        -- Legacy fallback path
        let uniqueOpt := globals.bind fun g => g.lookupUnique typeName.display
        for ctor in ctors do
          let arity := ctor.fieldTypeSyntax.size
          LowerM.modifyCtx fun ctx =>
            ctx.registerCtor ctor.name typeName ctor.tag arity

          if let (some g, some unique) := (globals, uniqueOpt) then
            let ctorSimpleName := ctor.name.id.original
            if let some ctorInfo := g.lookupInChild typeName.display ctorSimpleName then
              LowerM.modifyCtx fun ctx =>
                ctx.registerCtorType unique ctor.tag ctorInfo.type

    | .struct structName _tvars ctorName fields =>
      let mut usedMetadata := false
      if let some g := globals then
        if let some indInfo := g.lookupInductive structName.display then
          usedMetadata := true
          for ctor in indInfo.ctors do
            LowerM.modifyCtx fun ctx =>
              ctx.registerCtor ctor.name structName ctor.tag ctor.arity
            LowerM.modifyCtx fun ctx =>
              ctx.registerCtorType indInfo.unique ctor.tag ctor.type
      if !usedMetadata then
        let arity := fields.size
        LowerM.modifyCtx fun ctx =>
          ctx.registerCtor ctorName structName 0 arity

        if let some g := globals then
          if let some unique := g.lookupUnique structName.display then
            if let some ctorInfo := g.lookupInChild structName.display "new" then
              LowerM.modifyCtx fun ctx =>
                ctx.registerCtorType unique 0 ctorInfo.type

    | .record name _tvars fields =>
      let mut usedMetadata := false
      if let some g := globals then
        if let some indInfo := g.lookupInductive name.display then
          usedMetadata := true
          for ctor in indInfo.ctors do
            LowerM.modifyCtx fun ctx =>
              ctx.registerCtor ctor.name name ctor.tag ctor.arity
            LowerM.modifyCtx fun ctx =>
              ctx.registerCtorType indInfo.unique ctor.tag ctor.type
      if !usedMetadata then
        let arity := fields.size
        LowerM.modifyCtx fun ctx =>
          ctx.registerCtor name name 0 arity

/-- Map from function name to typed function -/
abbrev TypedFunctionMap := Std.HashMap String Soma.Core.TypedFunction

/-- Check if a function should be lowered to actual code -/
def shouldLowerBody (fn : Soma.Core.TypedFunction) : Bool :=
  not fn.attrs.intrinsic && fn.attrs.extern.isNone

/-- Lower an entire module using typed functions from type checking -/
def lowerModule (types : Array Soma.Core.TypeDef)
    (typedFunctions : TypedFunctionMap)
    (globals : Option Soma.Dependent.Globals := none) : LowerM Unit := do
  -- Load intrinsic dispatch metadata from elaboration/type checking.
  if let some g := globals then
    LowerM.modifyCtx fun ctx => { ctx with intrinsics := g.intrinsics }

  -- Register type constructors from current module
  registerTypes types globals

  -- Register constructors from external dependencies
  if let some g := globals then
    for (_, info) in g.allDecls do
      if info.isConstructor then
        let ctx ← LowerM.getCtx
        let ctorQN := info.name
        if ctx.lookupCtor ctorQN |>.isNone then
          let arity := info.type.explicitArity
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
    let externals := g.allDecls.filter fun (name, info) =>
      !typedFunctions.contains name &&
      !info.isConstructor
    for (i, (_, info)) in enumList externals do
      LowerM.modifyCtx fun ctx =>
        ctx.registerGlobal info.name (localCount + intrinsicCount + i)

  -- Fourth pass: lower each function body and add to book
  for (_, fn) in functions do
    let root ← lowerFunction fn
    let arity := fn.params.size
    let _ ← LowerM.addDefinition fn.name root arity fn.fnType

  -- Fifth pass: add placeholder definitions for intrinsic/extern functions from current module
  for (_, fn) in intrinsics do
    let era ← LowerM.addNode .era unitTy
    let _ ← LowerM.addDefinition fn.name era 0 fn.fnType (isExternal := true)

  -- Sixth pass: add placeholder definitions for external functions from dependencies
  if let some g := globals then
    let externals := g.allDecls.filter fun (name, info) =>
      !typedFunctions.contains name && -- Not in current module
      !info.isConstructor
    for (_, info) in externals do
      let era ← LowerM.addNode .era unitTy
      let _ ← LowerM.addDefinition info.name era 0 info.type
        (isExternal := true)

  -- Set root to main function if it exists
  -- Use ALO (allocation/instantiation) instead of REF because we want to actually exec
  let ctx ← LowerM.getCtx
  let mainEntry := ctx.globals.toList.find? fun (name, _) => name.id.original == "main"
  match mainEntry with
  | some (_, idx) =>
    let mainTy := match typedFunctions.get? "main" with
      | some typedFn => typedFn.fnType
      | none => unitTy
    let alo ← LowerM.addNode (.alo idx) mainTy
    LowerM.setRoot (PortId.principal alo)
  | none =>
    let era ← LowerM.addNode .era unitTy
    LowerM.setRoot (PortId.principal era)

/-- Lower typed functions to Circuit IR -/
def lower (types : Array Soma.Core.TypeDef)
    (typedFunctions : TypedFunctionMap)
    (usageMap : UsageMap)
    (globals : Option Soma.Dependent.Globals := none) : Graph :=
  LowerM.build (lowerModule types typedFunctions globals) usageMap

end Somac.Circuit.Lower
