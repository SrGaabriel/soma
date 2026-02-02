import Somac.Circuit.Graph
import Somac.Circuit.Node
import Somac.Circuit.Term
import Somac.Circuit.PatternMatch
import Soma.Metal.Expr
import Soma.Metal.Module
import Soma.Metal.Function
import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Dependent.Monad
import Std.Data.HashMap

namespace Somac.Circuit.Lower

open Somac.Circuit.Graph (Graph GraphM enumList)
open Somac.Circuit.Node (Node NodeId PortId PortIdx Label)
open Somac.Circuit.Term (Op1Code Op2Code PrimType)
open Somac.Circuit.Term (PrimType)
open Soma.Metal (Expr ExprList Literal Name BindingId)
open Soma.Core (Value Quantity PrimOp FFIOp Intrinsic)

/-- Usage map: maps BindingId to exact usage count from type checkings -/
abbrev UsageMap := Std.HashMap BindingId Nat

/-- Convert TCState.usages to UsageMap for clear boundaries -/
def UsageMap.fromTCUsages (usages : Std.HashMap BindingId Nat) : UsageMap := usages

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
  /-- Variable allocations by BindingId -/
  bindings : Std.HashMap Nat VarAlloc := {}
  /-- Global function Name → book index -/
  globals : Std.HashMap Name Nat := {}
  /-- Constructor Name → (type Name, tag, arity) -/
  constructors : Std.HashMap Name (Name × Nat × Nat) := {}
  /-- Constructor type registry for field type lookup during pattern matching -/
  ctorTypeRegistry : PatternMatch.ConstructorTypeRegistry := {}
  /-- Current function Name (for recursion detection) -/
  currentFn : Option Name := none
  /-- Usage counts from type checking (BindingId → exact count) -/
  usageMap : UsageMap := {}
  deriving Inhabited

namespace LowerCtx

def empty : LowerCtx := {}

/-- Register a variable binding with pre-allocated ports -/
def bindVar (ctx : LowerCtx) (id : BindingId) (name : String) (ports : Array PortId) (ty : Value)
    (erased : Bool := false) : LowerCtx :=
  { ctx with bindings := ctx.bindings.insert id.id ⟨ports, name, ty, erased⟩ }

/-- Check if a binding is erased -/
def isBindingErased (ctx : LowerCtx) (id : BindingId) : Bool :=
  match ctx.bindings.get? id.id with
  | some alloc => alloc.erased
  | none => false

/-- Consume one use of a variable, returning the port and type for that use -/
def useVar (ctx : LowerCtx) (id : BindingId) : Option (PortId × Value × LowerCtx) :=
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
def getVarType (ctx : LowerCtx) (id : BindingId) : Option Value :=
  ctx.bindings.get? id.id |>.map (·.ty)

/-- Register a global function -/
def registerGlobal (ctx : LowerCtx) (name : Name) (idx : Nat) : LowerCtx :=
  { ctx with globals := ctx.globals.insert name idx }

/-- Look up a global function's book index -/
def lookupGlobal (ctx : LowerCtx) (name : Name) : Option Nat :=
  ctx.globals.get? name

/-- Register a constructor -/
def registerCtor (ctx : LowerCtx) (name : Name) (typeName : Name) (tag arity : Nat) : LowerCtx :=
  { ctx with constructors := ctx.constructors.insert name (typeName, tag, arity) }

/-- Register a constructor with its elaborated type (for pattern matching field type lookup) -/
def registerCtorType (ctx : LowerCtx) (typeId : Soma.Core.TypeId) (tag : Nat)
    (ctorType : Value) : LowerCtx :=
  let info := PatternMatch.ConstructorTypeRegistry.fromElaboratedType ctorType
  { ctx with ctorTypeRegistry := ctx.ctorTypeRegistry.register typeId tag info }

/-- Look up constructor info -/
def lookupCtor (ctx : LowerCtx) (name : Name) : Option (Name × Nat × Nat) :=
  ctx.constructors.get? name

/-- Look up usage count for a binding. Returns 1 if not found (safe default) -/
def getUsageCount (ctx : LowerCtx) (id : BindingId) : Nat :=
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
def addDefinition (name : Name) (root : NodeId) (arity : Nat) (ty : Value)
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
def lowerVar (bindingId : BindingId) : LowerM (Option PortId) := do
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

/-- Check if an expression is a type-level argument (erased at runtime) -/
def isTypeLevelArg (e : Expr Value scope) : Bool :=
  match e with
  | .typeApp _ _ _ => true
  | .mvar _ _ _ => true
  | _ => false

/-- Check if all arguments in a list are type-level (erased at runtime) -/
def allTypeLevelArgs (args : ExprList Value scope) : Bool :=
  match args with
  | .nil => true
  | .cons e rest => isTypeLevelArg e && allTypeLevelArgs rest

/-- Check if an expression is a primitive operation global reference -/
partial def getPrimOp : Expr Value scope → Option PrimOp
  | .global name _ _ =>
    match name with
    | .intrinsic (.primOp op) => some op
    | _ => none
  | .call fn args _ _ =>
    if allTypeLevelArgs args then getPrimOp fn else none
  | _ => none

/-- Extract field names from a record row type
    Returns field names in order (outermost extension first) -/
def extractRowFieldNames : Value → Array String
  | .vRowExtend (.vLabelLit name) _ tail => #[name] ++ extractRowFieldNames tail
  | .vRowExtend _ _ tail => extractRowFieldNames tail -- Non-label (shouldn't happen)
  | .vRowEmpty => #[]
  | _ => #[] -- Not a row type

/-- Extract field names from a record type (vRecord row) -/
def extractRecordFieldNames : Value → Array String
  | .vRecord row => extractRowFieldNames row
  | _ => #[]

/-- Get the type of an expression, falling back to unit for erased/untyped expressions -/
def exprType (e : Expr Value scope) : Value :=
  e.getInfo.getD unitTy

/-- Convert UsageMap (keyed by BindingId) to Std.HashMap Nat Nat (keyed by raw id) -/
def usageMapToNatMap (usageMap : UsageMap) : Std.HashMap Nat Nat :=
  usageMap.fold (init := {}) fun acc bindingId count =>
    acc.insert bindingId.id count

mutual

/-- Lower an expression to a Circuit IR subgraph -/
partial def lowerExpr (e : Expr Value scope) : LowerM (Option PortId) := do
  -- Extract the type info from the Metal expression
  let ty := exprType e
  match e with
  | .var v _info _span =>
    lowerVar v.binding

  | .lit lit _span =>
    some <$> lowerLiteral lit

  | .call fn args _info _span =>
    lowerApp fn args ty

  | .lam params body _info _span =>
    some <$> lowerLam params body ty

  | .construct name tag args _info _span =>
    lowerConstruct name tag args ty

  | .if_ cond then_ else_ _info _span =>
    lowerIf cond then_ else_ ty

  | .case scrutinees arms _info _span =>
    lowerCase scrutinees arms ty

  | .global name _info _span =>
    some <$> lowerGlobal name ty

  | .fieldAccess expr _fieldName fieldIdx _info _span =>
    lowerFieldAccess expr fieldIdx ty

  | .record fields _info _span =>
    lowerRecord fields ty

  | .tuple elems _info _span =>
    lowerTuple elems ty

  | .pair fst snd _info _span =>
    lowerPair fst snd ty

  | .fst e _info _span =>
    lowerProj e 0 ty

  | .snd e _info _span =>
    lowerProj e 1 ty

  | .panic msg _info span =>
    -- Panic: emit a call to the runtime panic function (soma_panic)
    let word64Ty := Value.vPrimTy .word64
    let word32Ty := Value.vPrimTy .word32
    let msgNode ← LowerM.addNode (Node.num .u64 msg.hash.toUInt32) word64Ty
    let msgPort := PortId.principal msgNode

    -- Create a marker node that indicates panic with source location info
    -- We use a CTOR with a special tag (maxNat) to mark it as panic
    -- The arity is 2: (message_hash, line_number)
    let lineNum := span.start.line.toUInt32
    let lineNode ← LowerM.addNode (Node.num .u32 lineNum) word32Ty

    -- Build panic info as a 2-field constructor with reserved tag
    let panicTag := 0xFFFFFF -- Reserved tag for panic
    let panicCtor ← LowerM.addNode (.ctor panicTag 2) ty
    LowerM.connect ⟨panicCtor, ⟨1⟩⟩ msgPort
    LowerM.connect ⟨panicCtor, ⟨2⟩⟩ (PortId.principal lineNode)

    pure (some (PortId.principal panicCtor))

  | .ann expr _ty _info _span =>
    lowerExpr expr

  | .closure name captures _info _span =>
    lowerClosure name captures ty

  | .array elems _info _span =>
    lowerArray elems ty

  | .proj _typeName _fieldName fieldIdx _info _span =>
    some <$> lowerFirstClassProj fieldIdx ty

  | .inject label args _info _span =>
    lowerInject label args ty

  | .recordUpdate base updates _info _span =>
    lowerRecordUpdate base updates ty

  -- Type-level constructs (erased at runtime)
  | .type _ _ | .pi _ _ _ _ _ _ | .sigma _ _ _ _ _
  | .primTy _ _ | .higherPrimTy _ _ | .rowEmpty _
  | .rowExtend _ _ _ _ | .recordTy _ _ | .variantTy _ _
  | .labelLit _ _ | .dataTy _ _ _ | .eq _ _ _ _ _
  | .refl _ _ _ | .transport _ _ _ _ _ _ _ _
  | .hole _ _ | .mvar _ _ _ | .typeApp _ _ _ =>
    pure none

/-- Lower an expression with an explicit type override -/
partial def lowerExprWithType (e : Expr Value scope) (overrideTy : Value) : LowerM (Option PortId) := do
  match e with
  | .global name _ _ =>
    -- Global reference: use the override type instead of the declared type
    some <$> lowerGlobal name overrideTy
  | .call fn args _ _ =>
    -- Nested call: if all args are type-level, continue passing override through
    if allTypeLevelArgs args then
      lowerExprWithType fn overrideTy
    else
      -- The override type is for the outermost type application, not intermediate calls.
      let callTy := exprType e
      lowerApp fn args callTy
  | _ =>
    -- Other expressions: fall back to normal lowering
    lowerExpr e

/-- Lower an expression list -/
partial def lowerExprList (es : ExprList Value scope) : LowerM (Array PortId) := do
  match es with
  | .nil => pure #[]
  | .cons e rest =>
    let port? ← lowerExpr e
    let restPorts ← lowerExprList rest
    match port? with
    | some port => pure (#[port] ++ restPorts)
    | none => pure restPorts

/-- Lower a capture list to an array of (port, type) pairs -/
partial def lowerCaptureList (caps : Soma.Metal.CaptureList Value scope)
    : LowerM (Array (PortId × Value)) := do
  match caps with
  | .nil => pure #[]
  | .cons scopedVar captureType rest =>
    -- Look up the captured variable in current bindings
    let port? ← lowerVar scopedVar.binding
    let restPairs ← lowerCaptureList rest
    match port? with
    | some port => pure (#[(port, captureType)] ++ restPairs)
    | none => pure restPairs

/-- Lower a closure to a pair of (function_ref, environment).

    Closures are represented as a 2-field CTOR where:
    - Field 0: REF node pointing to the lifted function
    - Field 1: CTOR containing captured values (or nullary CTOR if no captures)

    This encoding allows closures to be first-class values that carry both
    the function pointer and their captured environment. When a closure is
    applied, the caller extracts the function ref and environment, then
    calls the function with the environment as an implicit first argument. -/
partial def lowerClosure (fnName : Name) (captures : Soma.Metal.CaptureList Value scope)
    (ty : Value) : LowerM (Option PortId) := do
  -- Get REF to the lifted function
  let fnPort ← lowerGlobal fnName ty

  -- Build environment CTOR from captures
  let capturePairs ← lowerCaptureList captures
  let envPort ← if capturePairs.isEmpty then do
    -- No captures: empty environment (nullary CTOR)
    let ctor ← LowerM.addNode (.ctor 0 0) unitTy
    pure (PortId.principal ctor)
  else do
    -- Build CTOR with captured values as fields
    -- Environment type is a tuple of capture types
    let captureTypes := capturePairs.map (·.2)
    let envTy := Value.tuple captureTypes
    let ctor ← LowerM.addNode (.ctor 0 capturePairs.size) envTy
    for i in [:capturePairs.size] do
      LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ capturePairs[i]!.1
    pure (PortId.principal ctor)

  -- Build closure pair: (fn_ref, env)
  let closureCtor ← LowerM.addNode (.ctor 0xFFFFFE 2) ty
  LowerM.connect ⟨closureCtor, ⟨1⟩⟩ fnPort
  LowerM.connect ⟨closureCtor, ⟨2⟩⟩ envPort
  pure (some (PortId.principal closureCtor))

/-- Lower a function application -/
partial def lowerApp (fn : Expr Value scope) (args : ExprList Value scope)
    (ty : Value) : LowerM (Option PortId) := do
  -- Check if all arguments are type-level (erased at runtime)
  if allTypeLevelArgs args then
    -- Pure type app, pass result ty through
    lowerExprWithType fn ty
  else
    match fn with
    | .call innerFn innerArgs _ _ =>
      match getPrimOp innerFn with
      | some primOp =>
        match primOpToOp2Code primOp with
        | some op2 =>
          -- Lower operands directly without creating intermediate APP nodes
          let innerArgPorts ← lowerExprList innerArgs
          let outerArgPorts ← lowerExprList args
          match innerArgPorts.toList, outerArgPorts.toList with
          | [arg1Port], [arg2Port] =>
            -- Both operands available: create Op2 node
            let op2Node ← LowerM.addNode (.op2 op2) ty
            LowerM.connect ⟨op2Node, ⟨1⟩⟩ arg1Port
            LowerM.connect ⟨op2Node, ⟨2⟩⟩ arg2Port
            pure (some (PortId.principal op2Node))
          | _, _ =>
            -- Operands erased or wrong arity: fall through to normal lowering
            lowerAppGeneric fn args ty
        | none =>
          lowerAppGeneric fn args ty
      | none =>
        lowerAppGeneric fn args ty
    | _ =>
      -- fn is not a .call: fall through
      lowerAppGeneric fn args ty
where
  /-- Generic application lowering -/
  lowerAppGeneric (fn : Expr Value scope) (args : ExprList Value scope)
      (ty : Value) : LowerM (Option PortId) := do
    let fnPort? ← lowerExpr fn
    match fnPort? with
    | none => pure none
    | some fnPort =>
      let argPorts ← lowerExprList args
      match fn, argPorts.toList with
      | _, [argPort] =>
        -- Single argument call (the normal case after elaboration)
        match getPrimOp fn with
        | some primOp =>
          match primOpToOp1Code primOp with
          | some op1 =>
            let op1Node ← LowerM.addNode (.op1 op1) ty
            LowerM.connect ⟨op1Node, ⟨1⟩⟩ argPort
            pure (some (PortId.principal op1Node))
          | none =>
            lowerSingleApp fnPort argPort ty
        | none =>
          lowerSingleApp fnPort argPort ty

      | _, [] =>
        pure (some fnPort)

      | _, argPortList =>
        let mut resultPort := fnPort
        for argPort in argPortList do
          let app ← LowerM.addNode .app ty
          LowerM.connect ⟨app, ⟨1⟩⟩ resultPort
          LowerM.connect ⟨app, ⟨2⟩⟩ argPort
          resultPort := PortId.principal app
        pure (some resultPort)
  /-- Lower a single-argument application using the type annotation from elaboration -/
  lowerSingleApp (fnPort : PortId) (argPort : PortId) (resultTy : Value) : LowerM (Option PortId) := do
    let app ← LowerM.addNode .app resultTy
    LowerM.connect ⟨app, ⟨1⟩⟩ fnPort
    LowerM.connect ⟨app, ⟨2⟩⟩ argPort
    pure (some (PortId.principal app))

/-- Lower a lambda expression -/
partial def lowerLam (params : Soma.Metal.ParamList Value)
    (body : Expr Value (params.bindingIds ++ scope))
    (ty : Value) : LowerM PortId := do
  let paramList := params.toList

  match paramList with
  | [] =>
    -- No parameters: just lower the body
    match ← lowerExpr body with
    | some bodyPort => pure bodyPort
    | none =>
      let era ← LowerM.addNode .era unitTy
      pure (PortId.principal era)

  | [(bindingId, name, _info)] =>
    -- Single parameter lambda (the normal case after elaboration)
    let ctx ← LowerM.getCtx
    let usageCount := ctx.getUsageCount bindingId
    let erased := usageCount == 0

    -- The LAM node gets the full function type from the expression annotation
    let lam ← LowerM.addNode (.lam erased) ty

    -- Extract parameter type from the Pi type's domain
    let paramTy := ty.piDomain?.getD unitTy

    -- Build DUP chain and bind the parameter
    let varPort : PortId := ⟨lam, ⟨1⟩⟩
    let (usePorts, isErased) ← buildDupChain varPort usageCount paramTy
    LowerM.modifyCtx fun ctx => ctx.bindVar bindingId name usePorts paramTy isErased

    -- Lower the body and wire to LAM
    let bodyPort? ← lowerExpr body
    let bodyPort := bodyPort?.getD ⟨lam, ⟨1⟩⟩
    LowerM.connect ⟨lam, ⟨2⟩⟩ bodyPort

    pure (PortId.principal lam)

  | _ =>
    -- todo: consider panicking
    let mut lamNodes : Array NodeId := #[]
    let ctx ← LowerM.getCtx
    let mut currentTy := ty

    for (bindingId, name, _info) in paramList do
      let usageCount := ctx.getUsageCount bindingId
      let erased := usageCount == 0

      let lam ← LowerM.addNode (.lam erased) currentTy
      lamNodes := lamNodes.push lam

      let paramTy := currentTy.piDomain?.getD unitTy
      currentTy := currentTy.piCodomain?.getD unitTy

      let varPort : PortId := ⟨lam, ⟨1⟩⟩
      let (usePorts, isErased) ← buildDupChain varPort usageCount paramTy
      LowerM.modifyCtx fun ctx => ctx.bindVar bindingId name usePorts paramTy isErased

    for j in [:lamNodes.size - 1] do
      let outer := lamNodes[j]!
      let inner := lamNodes[j + 1]!
      LowerM.connect ⟨outer, ⟨2⟩⟩ (PortId.principal inner)

    let bodyPort? ← lowerExpr body
    let bodyPort := bodyPort?.getD ⟨lamNodes[lamNodes.size - 1]!, ⟨1⟩⟩
    let innermost := lamNodes[lamNodes.size - 1]!
    LowerM.connect ⟨innermost, ⟨2⟩⟩ bodyPort

    pure (PortId.principal lamNodes[0]!)

/-- Lower a constructor application -/
partial def lowerConstruct (_name : Name) (tag : Nat) (args : ExprList Value scope)
    (ty : Value) : LowerM (Option PortId) := do
  let argPorts ← lowerExprList args
  let ctor ← LowerM.addNode (.ctor tag argPorts.size) ty

  -- Connect each field to the CTOR's aux ports
  for i in [:argPorts.size] do
    LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ argPorts[i]!

  pure (some (PortId.principal ctor))

/-- Lower an if-then-else (as a MAT on boolean) -/
partial def lowerIf (cond then_ else_ : Expr Value scope)
    (ty : Value) : LowerM (Option PortId) := do
  let condPort? ← lowerExpr cond
  match condPort? with
  | none =>
    -- Condition is erased, entire if is erased
    pure none
  | some condPort =>
    let thenPort? ← lowerExpr then_
    let elsePort? ← lowerExpr else_
    -- For branches, if they're erased we still need something to connect
    let thenPort := match thenPort? with
      | some p => p
      | none => condPort -- placeholder
    let elsePort := match elsePort? with
      | some p => p
      | none => condPort -- placeholder

    -- MAT on bool: tag 1 = true
    let mat ← LowerM.addNode (.mat 1) ty
    LowerM.connect ⟨mat, ⟨1⟩⟩ condPort -- scrutinee
    LowerM.connect ⟨mat, ⟨2⟩⟩ thenPort -- hit (true)
    LowerM.connect ⟨mat, ⟨3⟩⟩ elsePort -- miss (false)

    pure (some (PortId.principal mat))

/-- Lower a case expression using decision tree compilation -/
partial def lowerCase (scrutinees : ExprList Value scope)
    (arms : Soma.Metal.ArmList Value scope)
    (ty : Value) : LowerM (Option PortId) := do
  -- Lower scrutinees and collect their types
  let scrutPorts ← lowerExprList scrutinees
  let scrutTypes ← getExprListTypes scrutinees

  if scrutPorts.isEmpty then
    pure none
  else
    -- Build constructor table from current context
    let ctx ← LowerM.getCtx
    let ctorTable := buildCtorTable ctx.constructors
    let simplifyCtx : PatternMatch.SimplifyCtx := { ctorTable := ctorTable }

    -- Compile pattern matrix to decision tree
    let matrix := PatternMatch.buildMatrixFromArmList simplifyCtx arms
    let tree := PatternMatch.compileMatrix matrix ctx.ctorTypeRegistry scrutTypes

    -- Convert usage map to the format expected by PatternMatch
    let usageCounts := usageMapToNatMap ctx.usageMap

    -- Lower the decision tree
    let result ← PatternMatch.lower tree scrutPorts scrutTypes ctx.ctorTypeRegistry ty
      (fun armIndex armCtx => lowerArmBodyByIndex arms armIndex armCtx)
      usageCounts
    pure (some result)
where
  /-- Get types of an expression list -/
  getExprListTypes : ExprList Value scope → LowerM (Array Value)
    | .nil => pure #[]
    | .cons e rest => do
      let ty := exprType e
      let restTys ← getExprListTypes rest
      pure (#[ty] ++ restTys)

  /-- Build a constructor table from the LowerCtx format -/
  buildCtorTable (ctors : Std.HashMap Name (Name × Nat × Nat))
      : PatternMatch.ConstructorTable :=
    ctors.fold (init := {}) fun acc name (typeName, tag, arity) =>
      acc.insert name.display ⟨typeName.display, tag, arity⟩

  /-- Get arm body by index and lower it directly -/
  lowerArmBodyByIndex (arms : Soma.Metal.ArmList Value scope) (idx : Nat)
      (armCtx : PatternMatch.ArmContext) : LowerM PortId := do
    match arms, idx with
    | .nil, _ =>
      -- Should not happen with well-formed patterns
      let era ← LowerM.addNode .era unitTy
      pure (PortId.principal era)
    | .cons (.mk _pats body _span) _, 0 =>
      -- Install bindings from armCtx into the context
      for (bindingId, name, ports, varTy) in armCtx.bindings do
        LowerM.modifyCtx fun ctx => ctx.bindVar bindingId name ports varTy
      -- Lower the arm body directly here where we have access to its true scope
      match ← lowerExpr body with
      | some port => pure port
      | none =>
        let era ← LowerM.addNode .era unitTy
        pure (PortId.principal era)
    | .cons _ rest, n + 1 => lowerArmBodyByIndex rest n armCtx



/-- Lower a global reference.

    For function references, we distinguish between:
    1. **Self-recursive calls** (calling the currently-compiling function):
       Emit an ALO (allocation) node for lazy instantiation.
       This enables infinite unfolding without building infinite graphs.

    2. **Nullary function calls** (referencing a 0-arity function as a value):
       Emit an ALO node to call the function and get its result.
       Example: `def main = test` where `test :: Int` - we need to call test.

    3. **Other function references** (calling a different function):
       Emit a REF node pointing to the book entry.
       During reduction, when APP-REF interacts, an ALO is created.

    The key insight from the spec (Section 6.5):
    - REF is a static "address" of a definition in the book
    - ALO is the dynamic "instantiation" that expands lazily
    - For self-recursion, we know at compile time that instantiation is needed
-/
partial def lowerGlobal (name : Name) (ty : Value) : LowerM PortId := do
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
      -- Reference to another function: emit REF
      -- The reducer will create ALO when this REF interacts with APP
      let ref ← LowerM.addNode (.ref idx) ty
      pure (PortId.principal ref)
  | none =>
    -- Check if it's a constructor (nullary constructors show up as globals)
    match name.ctorTag? with
    | some tag =>
      -- It's a constructor with no arguments
      let ctor ← LowerM.addNode (.ctor tag 0) ty
      pure (PortId.principal ctor)
    | none =>
      -- Also check by looking up in the constructor registry (using Name)
      match ctx.lookupCtor name with
      | some (_, tag, arity) =>
        if arity == 0 then
          let ctor ← LowerM.addNode (.ctor tag 0) ty
          pure (PortId.principal ctor)
        else
          panic! s!"lowerGlobal: partial constructor application should have been desugared: {name.display}"
      | none =>
        panic! s!"lowerGlobal: unknown global '{name.display}' (not in globals, not a constructor)"

/-- Lower field access (projection) -/
partial def lowerFieldAccess (expr : Expr Value scope) (fieldIdx : Nat)
    (ty : Value) : LowerM (Option PortId) := do
  let exprPort? ← lowerExpr expr
  match exprPort? with
  | none => pure none -- Record is erased, projection is erased
  | some exprPort =>
    let proj ← LowerM.addNode (.proj fieldIdx) ty
    LowerM.connect ⟨proj, ⟨1⟩⟩ exprPort
    pure (some (PortId.principal proj))

/-- Lower a record literal -/
partial def lowerRecord (fields : Soma.Metal.RecordFieldList Value scope)
    (ty : Value) : LowerM (Option PortId) := do
  let fieldPorts ← lowerRecordFields fields
  let rec_ ← LowerM.addNode (.record fieldPorts.size) ty

  for i in [:fieldPorts.size] do
    LowerM.connect ⟨rec_, ⟨i + 1⟩⟩ fieldPorts[i]!

  pure (some (PortId.principal rec_))

/-- Lower record fields -/
partial def lowerRecordFields (fields : Soma.Metal.RecordFieldList Value scope) : LowerM (Array PortId) := do
  match fields with
  | .nil => pure #[]
  | .cons _name expr rest =>
    let port? ← lowerExpr expr
    let restPorts ← lowerRecordFields rest
    match port? with
    | some port => pure (#[port] ++ restPorts)
    | none => pure restPorts

/-- Lower a record update expression.

    Record update `{ base | field1 = val1, field2 = val2 }` is lowered as:
    1. Project all fields from the base record
    2. For each field in updates, use the new value instead
    3. Construct a new record with the combined fields

    The type info contains the record type, from which we extract field names -/
partial def lowerRecordUpdate (base : Expr Value scope)
    (updates : Soma.Metal.RecordFieldList Value scope)
    (ty : Value) : LowerM (Option PortId) := do
  -- Get the record type from base's type annotation
  let baseTy := exprType base
  let fieldNames := extractRecordFieldNames baseTy

  let numFields := fieldNames.size

  if numFields == 0 then
    -- Can't determine record structure, just lower base
    lowerExpr base

  else
    -- Build a map from field name to update expression
    let updateList := updates.toList
    let updateMap : Std.HashMap String (Expr Value scope) :=
      updateList.foldl (init := {}) fun m (name, expr) => m.insert name expr

    -- Lower the base expression
    let basePort? ← lowerExpr base
    match basePort? with
    | none => pure none
    | some basePort =>
      -- DUP the base for each field we need to project
      -- We need one copy per non-updated field
      let numNonUpdated := numFields - updateList.length
      let numCopies := if numNonUpdated > 0 then numNonUpdated else 1

      let (basePorts, _) ← buildDupChain basePort numCopies baseTy
      let mut basePortIdx := 0

      -- For each field, either project from base or use the update value
      let mut fieldPorts : Array PortId := #[]

      for i in [:numFields] do
        let fieldName := fieldNames[i]!
        match updateMap.get? fieldName with
        | some updateExpr =>
          -- Use the update value
          let updatePort? ← lowerExpr updateExpr
          match updatePort? with
          | some updatePort => fieldPorts := fieldPorts.push updatePort
          | none => pure ()
        | none =>
          -- Project from base
          let fieldTy := baseTy.recordFieldType i |>.getD unitTy
          if basePortIdx < basePorts.size then
            let proj ← LowerM.addNode (.proj i) fieldTy
            LowerM.connect ⟨proj, ⟨1⟩⟩ basePorts[basePortIdx]!
            fieldPorts := fieldPorts.push (PortId.principal proj)
            basePortIdx := basePortIdx + 1

      -- Construct the new record
      let rec_ ← LowerM.addNode (.record fieldPorts.size) ty
      for i in [:fieldPorts.size] do
        LowerM.connect ⟨rec_, ⟨i + 1⟩⟩ fieldPorts[i]!

      pure (some (PortId.principal rec_))

/-- Lower a variant injection expression.

    Variant injection `.Label(args)` is lowered as a CTOR node where:
    - The tag is derived from hashing the label name
    - The args become the constructor fields

    For nullary variants (.Label), we emit a 0-arity CTOR.
    For unary variants (.Label(val)), we emit a 1-arity CTOR.
    For multi-field variants, args are packed into fields. -/
partial def lowerInject (label : String) (args : ExprList Value scope)
    (ty : Value) : LowerM (Option PortId) := do
  let argPorts ← lowerExprList args

  -- Use label hash as the constructor tag
  -- This ensures consistent tags across compilation units
  let tag := label.hash.toNat % 0xFFFFFF  -- Keep within 24-bit range

  let ctor ← LowerM.addNode (.ctor tag argPorts.size) ty
  for i in [:argPorts.size] do
    LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ argPorts[i]!

  pure (some (PortId.principal ctor))

/-- Lower a first-class projection function.

    `.proj TypeName fieldName fieldIndex` is a first-class function that
    projects the given field from a record. It's equivalent to:

        λr. r.fieldIndex

    This is used for:
    - Σ-type projections (.1, .2)
    - Named record field accessors (Record.field)
    - Partial application of field access

    We lower this to: LAM → PROJ → (wire body to LAM)
    The LAM's variable receives the record, PROJ extracts the field. -/
partial def lowerFirstClassProj (fieldIdx : Nat) (ty : Value) : LowerM PortId := do
  -- Create LAM node (not erased - the parameter is used)
  let lam ← LowerM.addNode (.lam false) ty

  -- The LAM's aux0 (var port) will receive the record argument
  let varPort : PortId := ⟨lam, ⟨1⟩⟩

  -- Create PROJ node to extract the field
  -- The projected field type is the return type of the projection function
  let proj ← LowerM.addNode (.proj fieldIdx) ty

  -- Connect: LAM.var → PROJ.input
  LowerM.connect ⟨proj, ⟨1⟩⟩ varPort

  -- Connect: PROJ.principal → LAM.body
  LowerM.connect ⟨lam, ⟨2⟩⟩ (PortId.principal proj)

  -- Return the LAM's principal port (the function value)
  pure (PortId.principal lam)

/-- Lower a tuple -/
partial def lowerTuple (elems : ExprList Value scope)
    (ty : Value) : LowerM (Option PortId) := do
  let elemPorts ← lowerExprList elems
  -- Tuple as a 0-tagged constructor
  let ctor ← LowerM.addNode (.ctor 0 elemPorts.size) ty

  for i in [:elemPorts.size] do
    LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ elemPorts[i]!

  pure (some (PortId.principal ctor))

/-- Lower an array literal.

    Arrays are represented as ARRAY nodes with:
    - Aux 0: length (NUM node with the element count)
    - Aux 1: data pointer (for now, a CTOR containing the elements)

    The ARRAY node supports:
    - O(1) length access (just read aux0)
    - O(1) random access via INDEX node
    - DUP-ARRAY creates a shallow copy (shares backing data)
    - ERA-ARRAY frees the backing memory

    For small arrays, we inline the elements into a CTOR node as the data.
    The runtime can optimize large arrays to use heap-allocated contiguous memory. -/
partial def lowerArray (elems : ExprList Value scope)
    (ty : Value) : LowerM (Option PortId) := do
  let elemPorts ← lowerExprList elems
  let len := elemPorts.size

  -- Extract element type from the array type (Array T -> T)
  let elemTy := ty.dataTypeFirstParam?.getD intTy

  -- Create length node
  let word64Ty := Value.vPrimTy .word64
  let lenNode ← LowerM.addNode (.num .u64 len.toUInt32) word64Ty

  -- Create data node: for now, store elements in a CTOR
  -- Tag 0xFFFFFD is reserved for array backing storage
  -- The backing storage type is a tuple of element types
  let backingTy := Value.tuple (List.replicate len elemTy).toArray
  let dataNode ← LowerM.addNode (.ctor 0xFFFFFD len) backingTy
  for i in [:len] do
    LowerM.connect ⟨dataNode, ⟨i + 1⟩⟩ elemPorts[i]!

  -- Create ARRAY node with element type from ty if available
  let arrayNode ← LowerM.addNode (.array .i64) ty
  LowerM.connect ⟨arrayNode, ⟨1⟩⟩ (PortId.principal lenNode)   -- aux0 = length
  LowerM.connect ⟨arrayNode, ⟨2⟩⟩ (PortId.principal dataNode)  -- aux1 = data

  pure (some (PortId.principal arrayNode))

/-- Lower a pair -/
partial def lowerPair (fst snd : Expr Value scope)
    (ty : Value) : LowerM (Option PortId) := do
  let fstPort? ← lowerExpr fst
  let sndPort? ← lowerExpr snd

  match fstPort?, sndPort? with
  | none, none =>
    -- Both components erased, entire pair is erased
    pure none
  | some fstPort, some sndPort =>
    -- Both present, build normal pair
    let ctor ← LowerM.addNode (.ctor 0 2) ty
    LowerM.connect ⟨ctor, ⟨1⟩⟩ fstPort
    LowerM.connect ⟨ctor, ⟨2⟩⟩ sndPort
    pure (some (PortId.principal ctor))
  | some fstPort, none =>
    -- Only first component present, build pair with ERA for second
    let era ← LowerM.addNode .era unitTy
    let ctor ← LowerM.addNode (.ctor 0 2) ty
    LowerM.connect ⟨ctor, ⟨1⟩⟩ fstPort
    LowerM.connect ⟨ctor, ⟨2⟩⟩ (PortId.principal era)
    pure (some (PortId.principal ctor))
  | none, some sndPort =>
    -- Only second component present, build pair with ERA for first
    let era ← LowerM.addNode .era unitTy
    let ctor ← LowerM.addNode (.ctor 0 2) ty
    LowerM.connect ⟨ctor, ⟨1⟩⟩ (PortId.principal era)
    LowerM.connect ⟨ctor, ⟨2⟩⟩ sndPort
    pure (some (PortId.principal ctor))

/-- Lower a projection -/
partial def lowerProj (expr : Expr Value scope) (idx : Nat)
    (ty : Value) : LowerM (Option PortId) := do
  let exprPort? ← lowerExpr expr
  match exprPort? with
  | none => pure none
  | some exprPort =>
    let proj ← LowerM.addNode (.proj idx) ty
    LowerM.connect ⟨proj, ⟨1⟩⟩ exprPort
    pure (some (PortId.principal proj))

end

/-- Lower a function definition -/
def lowerFunction (fn : Soma.Metal.TypedFunction) : LowerM NodeId := do
  -- Set current function for recursion detection
  LowerM.modifyCtx fun ctx => { ctx with currentFn := some fn.name }

  let typedBody := fn.body

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

  -- Lower the body
  let bodyPort? ← lowerExpr typedBody

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
def registerTypes (types : Array Soma.Metal.TypeDef)
    (globals : Option Soma.Dependent.Globals := none) : LowerM Unit := do
  for typeDef in types do
    match typeDef with
    | .algebraic typeName _tvars ctors =>
      -- Look up the TypeId for this type
      let typeIdOpt := globals.bind fun g => g.lookupTypeId typeName.display
      for ctor in ctors do
        let arity := ctor.fieldTypeSyntax.size
        LowerM.modifyCtx fun ctx =>
          ctx.registerCtor ctor.name typeName ctor.tag arity

        -- If we have globals, register the constructor type for field type lookup
        if let (some g, some typeId) := (globals, typeIdOpt) then
          let ctorSimpleName := ctor.name.ctorSimpleName?.getD ctor.name.display
          let ctorQualifiedName := s!"{typeName.display}.{ctorSimpleName}"
          if let some ctorInfo := g.lookup ctorQualifiedName then
            LowerM.modifyCtx fun ctx =>
              ctx.registerCtorType typeId ctor.tag ctorInfo.type
          else if let some ctorInfo := g.lookup ctorSimpleName then
            LowerM.modifyCtx fun ctx =>
              ctx.registerCtorType typeId ctor.tag ctorInfo.type

    | .struct structName _tvars ctorName fields =>
      let arity := fields.size
      LowerM.modifyCtx fun ctx =>
        ctx.registerCtor ctorName structName 0 arity

      -- Register struct constructor type if available
      if let some g := globals then
        if let some typeId := g.lookupTypeId structName.display then
          let ctorSimpleName := ctorName.ctorSimpleName?.getD ctorName.display
          let ctorQualifiedName := s!"{structName.display}.{ctorSimpleName}"
          if let some ctorInfo := g.lookup ctorQualifiedName then
            LowerM.modifyCtx fun ctx =>
              ctx.registerCtorType typeId 0 ctorInfo.type

    | .record name _tvars fields =>
      let arity := fields.size
      LowerM.modifyCtx fun ctx =>
        ctx.registerCtor name name 0 arity

/-- Map from function name to typed function -/
abbrev TypedFunctionMap := Std.HashMap String Soma.Metal.TypedFunction

/-- Check if a function should be lowered to actual code -/
def shouldLowerBody (fn : Soma.Metal.TypedFunction) : Bool :=
  not fn.attrs.intrinsic && fn.attrs.extern.isNone

/-- Lower an entire module using typed functions from type checking -/
def lowerModule (types : Array Soma.Metal.TypeDef)
    (typedFunctions : TypedFunctionMap)
    (globals : Option Soma.Dependent.Globals := none) : LowerM Unit := do
  -- Register type constructors from current module
  registerTypes types globals

  -- Register constructors from external dependencies
  if let some g := globals then
    for (_, info) in g.defs.toList do
      if info.isConstructor then
        let ctx ← LowerM.getCtx
        if ctx.lookupCtor info.name |>.isNone then
          let arity := info.type.explicitArity
          LowerM.modifyCtx fun ctx =>
            ctx.registerCtor info.name info.name info.ctorTag arity

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
    let externals := g.defs.toList.filter fun (name, info) =>
      !typedFunctions.contains name &&
      !info.isConstructor
    for (i, (_, info)) in enumList externals do
      LowerM.modifyCtx fun ctx => ctx.registerGlobal info.name (localCount + intrinsicCount + i)

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
    let externals := g.defs.toList.filter fun (name, info) =>
      !typedFunctions.contains name && -- Not in current module
      !info.isConstructor
    for (_, info) in externals do
      let era ← LowerM.addNode .era unitTy
      let _ ← LowerM.addDefinition info.name era 0 info.type (isExternal := true)

  -- Set root to main function if it exists
  -- Use ALO (allocation/instantiation) instead of REF because we want to actually exec
  let ctx ← LowerM.getCtx
  let mainEntry := ctx.globals.toList.find? fun (name, _) => name.original == "main"
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
def lower (types : Array Soma.Metal.TypeDef)
    (typedFunctions : TypedFunctionMap)
    (usageMap : UsageMap)
    (globals : Option Soma.Dependent.Globals := none) : Graph :=
  LowerM.build (lowerModule types typedFunctions globals) usageMap

end Somac.Circuit.Lower
