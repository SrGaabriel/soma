import Soma.Circuit.Graph
import Soma.Circuit.Node
import Soma.Circuit.Term
import Soma.Circuit.PatternMatch
import Soma.Metal.Expr
import Soma.Metal.Module
import Soma.Metal.Function
import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Dependent.Monad
import Std.Data.HashMap

namespace Soma.Circuit.Lower

open Soma.Circuit.Graph (Graph GraphM enumList)
open Soma.Circuit.Node (Node NodeId PortId PortIdx Label)
open Soma.Circuit.Term (Op1Code Op2Code PrimType)
open Soma.Circuit.Term (PrimType)
open Soma.Metal (Expr ExprList Literal Name BindingId)
open Soma.Core (Value Quantity PrimOp Intrinsic)

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
  deriving Repr, Inhabited

/-- Default maximum recursion depth for pattern matching -/
def defaultMaxPatternDepth : Nat := 100

/-- Lowering context tracks variable bindings -/
structure LowerCtx where
  /-- Variable allocations by BindingId -/
  bindings : Std.HashMap Nat VarAlloc := {}
  /-- Global function Name → book index -/
  globals : Std.HashMap Name Nat := {}
  /-- Constructor Name → (type Name, tag, arity) -/
  constructors : Std.HashMap Name (Name × Nat × Nat) := {}
  /-- Current function Name (for recursion detection) -/
  currentFn : Option Name := none
  /-- Usage counts from type checking (BindingId → exact count) -/
  usageMap : UsageMap := {}
  /-- Maximum recursion depth for pattern matching -/
  maxPatternDepth : Nat := defaultMaxPatternDepth
  deriving Inhabited

namespace LowerCtx

def empty : LowerCtx := {}

/-- Register a variable binding with pre-allocated ports -/
def bindVar (ctx : LowerCtx) (id : BindingId) (name : String) (ports : Array PortId) : LowerCtx :=
  { ctx with bindings := ctx.bindings.insert id.id ⟨ports, name⟩ }

/-- Consume one use of a variable, returning the port for that use -/
def useVar (ctx : LowerCtx) (id : BindingId) : Option (PortId × LowerCtx) :=
  match ctx.bindings.get? id.id with
  | none => none
  | some alloc =>
    if alloc.ports.isEmpty then none
    else
      let port := alloc.ports[0]!
      let remaining := alloc.ports.extract 1 alloc.ports.size
      let ctx' := { ctx with bindings := ctx.bindings.insert id.id ⟨remaining, alloc.name⟩ }
      some (port, ctx')

/-- Register a global function -/
def registerGlobal (ctx : LowerCtx) (name : Name) (idx : Nat) : LowerCtx :=
  { ctx with globals := ctx.globals.insert name idx }

/-- Look up a global function's book index -/
def lookupGlobal (ctx : LowerCtx) (name : Name) : Option Nat :=
  ctx.globals.get? name

/-- Register a constructor -/
def registerCtor (ctx : LowerCtx) (name : Name) (typeName : Name) (tag arity : Nat) : LowerCtx :=
  { ctx with constructors := ctx.constructors.insert name (typeName, tag, arity) }

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
def addNode (n : Node) : LowerM NodeId :=
  liftGraph (GraphM.addNode n)

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
def addDefinition (name : String) (root : NodeId) (arity : Nat) : LowerM Nat :=
  liftGraph (GraphM.addDefinition name root arity)

end LowerM

/-- Build a DUP chain for n uses, returning an array of n ports (one per use)
    If n=0, connects an ERA to consume the value.
    If n=1, returns the source port directly (no DUP needed) -/
def buildDupChain (sourcePort : PortId) (n : Nat) : LowerM (Array PortId) := do
  if n == 0 then
    -- Erased: connect to ERA
    let era ← LowerM.addNode .era
    LowerM.connect (PortId.principal era) sourcePort
    pure #[]
  else if n == 1 then
    -- Linear: direct use
    pure #[sourcePort]
  else
    -- n > 1: build chain of n-1 DUP nodes
    let labels ← LowerM.freshLabels (n - 1)
    let mut usePorts : Array PortId := #[]
    let mut chainPort := sourcePort

    for i in [:n - 1] do
      let dup ← LowerM.addNode (.dup labels[i]!)
      -- Connect value to DUP's principal port
      LowerM.connect (PortId.principal dup) chainPort
      -- aux0 goes to a use
      usePorts := usePorts.push ⟨dup, ⟨1⟩⟩
      -- aux1 continues the chain
      chainPort := ⟨dup, ⟨2⟩⟩

    -- The final chainPort (last DUP's aux1) is the last use
    usePorts := usePorts.push chainPort
    pure usePorts

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
    let node := Node.num .i64 encoded
    let nid ← LowerM.addNode node
    pure (PortId.principal nid)
  | .bool b =>
    let node := Node.num .bool (if b then 1 else 0)
    let nid ← LowerM.addNode node
    pure (PortId.principal nid)
  | .string s =>
    -- String literals: use STRING node
    -- Length is the byte length of the UTF-8 encoded string
    let len := s.utf8ByteSize.toUInt32
    let lenNode ← LowerM.addNode (.num .u64 len)

    -- The codegen will intern strings and replace with actual pointers
    let hash := s.hash.toUInt32
    let dataNode ← LowerM.addNode (.num .u64 hash)

    -- Create STRING node
    let stringNode ← LowerM.addNode .string
    LowerM.connect ⟨stringNode, ⟨1⟩⟩ (PortId.principal lenNode) -- aux0 = length
    LowerM.connect ⟨stringNode, ⟨2⟩⟩ (PortId.principal dataNode) -- aux1 = data

    pure (PortId.principal stringNode)

/-- Lower a variable reference -/
def lowerVar (bindingId : BindingId) : LowerM PortId := do
  let ctx ← LowerM.getCtx
  match ctx.useVar bindingId with
  | some (port, ctx') =>
    LowerM.setCtx ctx'
    pure port
  | none =>
    -- todo: consider panicking here instead
    -- Return an ERA as error placeholder
    let era ← LowerM.addNode .era
    pure (PortId.principal era)

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

/-- Check if an expression is a primitive operation global reference -/
def getPrimOp : Expr Value scope → Option PrimOp
  | .global name _ _ =>
    match name with
    | .intrinsic (.primOp op) => some op
    | _ => none
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

mutual

/-- Lower an expression to a Circuit IR subgraph -/
partial def lowerExpr (e : Expr Value scope) : LowerM PortId := do
  match e with
  | .var v _info _span =>
    lowerVar v.binding

  | .lit lit _span =>
    lowerLiteral lit

  | .call fn args _info _span =>
    lowerApp fn args

  | .lam params body _info _span =>
    lowerLam params body

  | .construct name tag args _info _span =>
    lowerConstruct name tag args

  | .if_ cond then_ else_ _info _span =>
    lowerIf cond then_ else_

  | .case scrutinees arms _info _span =>
    lowerCase scrutinees arms

  | .global name _info _span =>
    lowerGlobal name

  | .fieldAccess expr _fieldName fieldIdx _info _span =>
    lowerFieldAccess expr fieldIdx

  | .record fields _info _span =>
    lowerRecord fields

  | .tuple elems _info _span =>
    lowerTuple elems

  | .pair fst snd _info _span =>
    lowerPair fst snd

  | .fst e _info _span =>
    lowerProj e 0

  | .snd e _info _span =>
    lowerProj e 1

  | .panic msg _info span =>
    -- Panic: emit a call to the runtime panic function (soma_panic)
    let msgNode ← LowerM.addNode (Node.num .u64 msg.hash.toUInt32)
    let msgPort := PortId.principal msgNode

    -- Create a marker node that indicates panic with source location info
    -- We use a CTOR with a special tag (maxNat) to mark it as panic
    -- The arity is 2: (message_hash, line_number)
    let lineNum := span.start.line.toUInt32
    let lineNode ← LowerM.addNode (Node.num .u32 lineNum)

    -- Build panic info as a 2-field constructor with reserved tag
    let panicTag := 0xFFFFFF -- Reserved tag for panic
    let panicCtor ← LowerM.addNode (.ctor panicTag 2)
    LowerM.connect ⟨panicCtor, ⟨1⟩⟩ msgPort
    LowerM.connect ⟨panicCtor, ⟨2⟩⟩ (PortId.principal lineNode)

    pure (PortId.principal panicCtor)

  | .ann expr _ty _info _span =>
    lowerExpr expr

  | .closure _name captures _info _span =>
    lowerClosure captures

  | .array elems _info _span =>
    lowerArray elems

  | .proj _typeName _fieldName fieldIdx _info _span =>
    lowerFirstClassProj fieldIdx

  | .inject label args _info _span =>
    lowerInject label args

  | .recordUpdate base updates _info _span =>
    lowerRecordUpdate base updates

  -- Type-level constructs (erased at runtime)
  | .type _ _ | .pi _ _ _ _ _ _ | .sigma _ _ _ _ _
  | .primTy _ _ | .higherPrimTy _ _ | .rowEmpty _
  | .rowExtend _ _ _ _ | .recordTy _ _ | .variantTy _ _
  | .labelLit _ _ | .dataTy _ _ _ | .eq _ _ _ _ _
  | .refl _ _ _ | .transport _ _ _ _ _ _ _ _
  | .hole _ _ | .mvar _ _ _ | .typeApp _ _ _ =>
    let era ← LowerM.addNode .era
    pure (PortId.principal era)

/-- Lower an expression list -/
partial def lowerExprList (es : ExprList Value scope) : LowerM (Array PortId) := do
  match es with
  | .nil => pure #[]
  | .cons e rest =>
    let port ← lowerExpr e
    let restPorts ← lowerExprList rest
    pure (#[port] ++ restPorts)

/-- Lower a capture list to an array of ports -/
partial def lowerCaptureList (caps : Soma.Metal.CaptureList Value scope)
    : LowerM (Array PortId) := do
  match caps with
  | .nil => pure #[]
  | .cons scopedVar _info rest =>
    -- Look up the captured variable in current bindings
    let port ← lowerVar scopedVar.binding
    let restPorts ← lowerCaptureList rest
    pure (#[port] ++ restPorts)

/-- Lower a closure to a CTOR node.

    Closures are represented as constructors where:
    - Tag 0 is used for all closure environments (distinguishes from user data types)
    - Each captured variable becomes a field of the constructor
    - The closure's lifted function is referenced separately when applied

    This encoding allows closures to participate in interaction net reduction
    naturally - when a closure is applied, the environment CTOR interacts
    with the function body to provide the captured values. -/
partial def lowerClosure (captures : Soma.Metal.CaptureList Value scope)
    : LowerM PortId := do
  let capturePorts ← lowerCaptureList captures
  if capturePorts.isEmpty then
    -- No captures: return unit (empty tuple / nullary CTOR)
    let ctor ← LowerM.addNode (.ctor 0 0)
    pure (PortId.principal ctor)
  else
    -- Build CTOR with captured values as fields
    let ctor ← LowerM.addNode (.ctor 0 capturePorts.size)
    for i in [:capturePorts.size] do
      LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ capturePorts[i]!
    pure (PortId.principal ctor)

/-- Lower a function application.

    For primitive unary operations (not, neg), we emit OP1 nodes directly.
    For primitive binary operations (add, sub, mul, etc.), we emit OP2 nodes
    directly instead of APP chains. This is more efficient and matches the
    semantics of interaction net primitive operations.

    For other function calls, we build a chain of APP nodes. -/
partial def lowerApp (fn : Expr Value scope) (args : ExprList Value scope) : LowerM PortId := do
  let argPorts ← lowerExprList args

  -- Check for primitive operation optimization
  match getPrimOp fn, argPorts.size with
  | some primOp, 1 =>
    -- Unary primitive operation: emit OP1 directly
    match primOpToOp1Code primOp with
    | some op1 =>
      let op1Node ← LowerM.addNode (.op1 op1)
      -- aux0 = operand
      LowerM.connect ⟨op1Node, ⟨1⟩⟩ argPorts[0]!
      pure (PortId.principal op1Node)
    | none =>
      -- Binary op with 1 arg: partial application, fall through to APP
      lowerAppGeneric fn argPorts
  | some primOp, 2 =>
    -- Binary primitive operation: emit OP2 directly
    match primOpToOp2Code primOp with
    | some op2 =>
      let op2Node ← LowerM.addNode (.op2 op2)
      -- aux0 = left operand, aux1 = right operand
      LowerM.connect ⟨op2Node, ⟨1⟩⟩ argPorts[0]!
      LowerM.connect ⟨op2Node, ⟨2⟩⟩ argPorts[1]!
      pure (PortId.principal op2Node)
    | none =>
      -- Unary op with 2 args: shouldn't happen, fall through to APP
      lowerAppGeneric fn argPorts
  | _, _ =>
    -- General case: build APP chain
    lowerAppGeneric fn argPorts
where
  /-- Generic APP chain lowering for non-primitive function calls -/
  lowerAppGeneric (fn : Expr Value scope) (argPorts : Array PortId) : LowerM PortId := do
    let fnPort ← lowerExpr fn

    -- Build a chain of APP nodes: ((fn arg₀) arg₁) ...
    let mut resultPort := fnPort
    for argPort in argPorts do
      let app ← LowerM.addNode .app
      -- aux0 = function, aux1 = argument, principal = result
      LowerM.connect ⟨app, ⟨1⟩⟩ resultPort -- function
      LowerM.connect ⟨app, ⟨2⟩⟩ argPort -- argument
      resultPort := PortId.principal app

    pure resultPort

/-- Lower a lambda expression -/
partial def lowerLam (params : Soma.Metal.ParamList Value)
    (body : Expr Value (params.bindingIds ++ scope)) : LowerM PortId := do
  let paramList := params.toList

  if paramList.isEmpty then
    -- No parameters: just lower the body
    lowerExpr body
  else
    -- Create LAM nodes (we'll wire them after lowering body)
    let mut lamNodes : Array NodeId := #[]
    let ctx ← LowerM.getCtx
    for (bindingId, name, _info) in paramList do
      -- This determines both erasure and DUP chain construction
      let usageCount := ctx.getUsageCount bindingId
      let erased := usageCount == 0
      let lam ← LowerM.addNode (.lam erased)
      lamNodes := lamNodes.push lam

      if usageCount > 0 then
        -- Build DUP chain from the LAM's var port
        let varPort : PortId := ⟨lam, ⟨1⟩⟩ -- aux0 = var
        let usePorts ← buildDupChain varPort usageCount
        LowerM.modifyCtx fun ctx => ctx.bindVar bindingId name usePorts

    -- Wire LAMs together: outer.body → inner.principal
    for i in [:lamNodes.size - 1] do
      let outer := lamNodes[i]!
      let inner := lamNodes[i + 1]!
      LowerM.connect ⟨outer, ⟨2⟩⟩ (PortId.principal inner) -- outer.body → inner

    -- Lower the body
    let bodyPort ← lowerExpr body

    -- Wire body to innermost LAM's body port
    let innermost := lamNodes[lamNodes.size - 1]!
    LowerM.connect ⟨innermost, ⟨2⟩⟩ bodyPort

    -- Return outermost LAM's principal port
    pure (PortId.principal lamNodes[0]!)

/-- Lower a constructor application -/
partial def lowerConstruct (_name : Name) (tag : Nat) (args : ExprList Value scope) : LowerM PortId := do
  let argPorts ← lowerExprList args
  let ctor ← LowerM.addNode (.ctor tag argPorts.size)

  -- Connect each field to the CTOR's aux ports
  for i in [:argPorts.size] do
    LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ argPorts[i]!

  pure (PortId.principal ctor)

/-- Lower an if-then-else (as a MAT on boolean) -/
partial def lowerIf (cond then_ else_ : Expr Value scope) : LowerM PortId := do
  let condPort ← lowerExpr cond
  let thenPort ← lowerExpr then_
  let elsePort ← lowerExpr else_

  -- MAT on bool: tag 1 = true
  let mat ← LowerM.addNode (.mat 1)
  LowerM.connect ⟨mat, ⟨1⟩⟩ condPort -- scrutinee
  LowerM.connect ⟨mat, ⟨2⟩⟩ thenPort -- hit (true)
  LowerM.connect ⟨mat, ⟨3⟩⟩ elsePort -- miss (false)

  pure (PortId.principal mat)

/-- Lower pattern matching to a chain of MAT nodes.

    Each arm is tested in order using MAT nodes. When a pattern matches,
    pattern variables are bound to projections from the scrutinee before
    evaluating the arm body.

    Architecture:
    - For multi-scrutinee matching, we identify which scrutinee has a constructor pattern
    - That scrutinee is used for MAT; others are just for variable binding
    - The MAT's hit/miss ports receive the arm body RESULTS, not the scrutinee
-/
partial def lowerCase (scrutinees : ExprList Value scope)
    (arms : Soma.Metal.ArmList Value scope) : LowerM PortId := do
  let scrutPorts ← lowerExprList scrutinees

  if scrutPorts.isEmpty then
    let era ← LowerM.addNode .era
    pure (PortId.principal era)
  else
    lowerArmsChainMulti scrutPorts arms
where
  /-- Check if arm list is empty -/
  isArmListEmpty : Soma.Metal.ArmList Value scope → Bool
    | .nil => true
    | .cons _ _ => false

  /-- Check if a pattern needs its scrutinee for bindings -/
  patternNeedsScrutinee : Soma.Metal.Pattern Value → Bool
    | .var _ _ _ _ => true
    | .wildcard _ _ => false
    | .lit _ _ => false
    | .ctor _ args _ _ => args.any patternNeedsScrutinee
    | .tuple elems _ _ => elems.any patternNeedsScrutinee
    | .array elems _ _ => elems.any patternNeedsScrutinee
    | .cons h t _ _ => patternNeedsScrutinee h || patternNeedsScrutinee t
    | .as _ _ _ _ _ => true
    | .variant _ arg _ _ => arg.map patternNeedsScrutinee |>.getD false

  /-- Check if a pattern is a constructor/literal that needs MAT -/
  patternNeedsMatch : Soma.Metal.Pattern Value → Bool
    | .ctor _ _ _ _ => true
    | .lit _ _ => true
    | .variant _ _ _ _ => true
    | .as _ _ inner _ _ => patternNeedsMatch inner
    | _ => false

  /-- Convert PatternList to Array -/
  patternListToArray : Soma.Metal.PatternList Value → Array (Soma.Metal.Pattern Value)
    | .nil => #[]
    | .cons p rest => #[p] ++ patternListToArray rest

  /-- Find which scrutinee index has a constructor pattern (for MAT) -/
  findMatchIndex (patterns : Array (Soma.Metal.Pattern Value)) : Option Nat :=
    patterns.findIdx? patternNeedsMatch

  /-- Get tag from a pattern -/
  getTagFromPattern (pat : Soma.Metal.Pattern Value) : Nat :=
    match pat with
    | .ctor name _ _ _ => name.ctorTag?.getD 0
    | .lit (.bool true) _ => 1
    | .lit (.bool false) _ => 0
    | .lit (.int n) _ => n.toNat
    | .as _ _ inner _ _ => getTagFromPattern inner
    | .tuple _ _ _ => 0
    | .variant label _ _ _ => label.hash.toNat
    | _ => 0

  /-- Count arms -/
  countArms : Soma.Metal.ArmList Value scope → Nat
    | .nil => 0
    | .cons _ rest => 1 + countArms rest

  /-- Lower arms with multiple scrutinees -/
  lowerArmsChainMulti (scrutPorts : Array PortId)
      : Soma.Metal.ArmList Value scope → LowerM PortId
    | .nil => do
      -- No arms so erase all scrutinees
      for port in scrutPorts do
        let era ← LowerM.addNode .era
        LowerM.connect (PortId.principal era) port
      let era ← LowerM.addNode .era
      pure (PortId.principal era)
    | .cons arm rest => do
      match arm with
      | .mk patterns body _span =>
        let patsArray := patternListToArray patterns

        if isArmListEmpty rest then
          -- Last arm: bind all patterns and evaluate body
          bindAllPatterns patsArray scrutPorts
          lowerExpr body
        else
          -- Find which pattern needs MAT
          match findMatchIndex patsArray with
          | none =>
            -- No constructor patterns, just bind and evaluate
            bindAllPatterns patsArray scrutPorts
            lowerExpr body
          | some matchIdx =>
            -- We need to MAT on scrutPorts[matchIdx]
            let matchPat := patsArray[matchIdx]!
            let tag := getTagFromPattern matchPat

            -- Count how many copies we need of the match scrutinee
            let numRemaining := countArms rest
            let matchPort := scrutPorts[matchIdx]!

            -- DUP the match scrutinee: one for MAT, one for bindings, plus copies for remaining arms
            let totalCopies := 2 + numRemaining
            let dupPorts ← buildDupChain matchPort totalCopies
            let matPort := dupPorts[0]!
            let bindPort := dupPorts[1]!
            let remainingMatchPorts := dupPorts.extract 2 dupPorts.size

            -- DUP all scrutinees: one for binding, rest for remaining arms
            let mut bindPorts := #[]
            let mut missPortsPerScrut : Array (Array PortId) := #[]

            for i in [:scrutPorts.size] do
              let port := scrutPorts[i]!
              if i == matchIdx then
                -- Already DUP'd above
                bindPorts := bindPorts.push bindPort
                missPortsPerScrut := missPortsPerScrut.push remainingMatchPorts
              else
                if numRemaining > 0 then
                  let totalNeeded := 1 + numRemaining
                  let dups ← buildDupChain port totalNeeded
                  bindPorts := bindPorts.push dups[0]!
                  missPortsPerScrut := missPortsPerScrut.push (dups.extract 1 dups.size)
                else
                  bindPorts := bindPorts.push port
                  missPortsPerScrut := missPortsPerScrut.push #[]

            -- Create MAT node
            let mat ← LowerM.addNode (.mat tag)
            LowerM.connect ⟨mat, ⟨1⟩⟩ matPort

            -- Bind all patterns using bindPorts
            bindAllPatterns patsArray bindPorts

            -- Lower body for hit case
            let hitBodyPort ← lowerExpr body
            LowerM.connect ⟨mat, ⟨2⟩⟩ hitBodyPort

            -- Build remaining scrutPorts for miss case (transpose missPortsPerScrut)
            let missScrutPortsList := transposePortArrays missPortsPerScrut numRemaining

            -- Lower remaining arms for miss case
            let missPort ← lowerArmsChainMultiWithPorts missScrutPortsList rest
            LowerM.connect ⟨mat, ⟨3⟩⟩ missPort

            pure (PortId.principal mat)

  /-- Transpose array of port arrays: [[a1,a2], [b1,b2]] -> [[a1,b1], [a2,b2]] -/
  transposePortArrays (arrays : Array (Array PortId)) (numArms : Nat) : Array (Array PortId) :=
    Array.mk <| (List.range numArms).map fun armIdx =>
      Array.mk <| arrays.toList.filterMap fun arr => arr[armIdx]?

  /-- Lower arms with pre-transposed port arrays per arm -/
  lowerArmsChainMultiWithPorts (scrutPortsPerArm : Array (Array PortId))
      : Soma.Metal.ArmList Value scope → LowerM PortId
    | .nil => do
      -- Erase any remaining ports
      for ports in scrutPortsPerArm do
        for port in ports do
          let era ← LowerM.addNode .era
          LowerM.connect (PortId.principal era) port
      let era ← LowerM.addNode .era
      pure (PortId.principal era)
    | .cons arm rest => do
      match arm with
      | .mk patterns body _span =>
        let patsArray := patternListToArray patterns
        let scrutPorts := scrutPortsPerArm[0]?.getD #[]
        let remainingPortsPerArm := scrutPortsPerArm.extract 1 scrutPortsPerArm.size

        if isArmListEmpty rest then
          -- Last arm
          bindAllPatterns patsArray scrutPorts
          -- Erase unused remaining ports
          for ports in remainingPortsPerArm do
            for port in ports do
              let era ← LowerM.addNode .era
              LowerM.connect (PortId.principal era) port
          lowerExpr body
        else
          match findMatchIndex patsArray with
          | none =>
            bindAllPatterns patsArray scrutPorts
            lowerExpr body
          | some matchIdx =>
            let matchPat := patsArray[matchIdx]!
            let tag := getTagFromPattern matchPat
            let numRemaining := countArms rest

            -- DUP scrutinees for this arm's binding vs remaining arms
            let mut bindPorts := #[]
            let mut nextRemainingPorts : Array (Array PortId) := #[]

            for i in [:scrutPorts.size] do
              let port := scrutPorts[i]!
              if numRemaining > 0 then
                let dups ← buildDupChain port 2
                bindPorts := bindPorts.push dups[0]!
                -- Collect remaining ports for next arms
                if i == matchIdx then
                  nextRemainingPorts := nextRemainingPorts.push #[dups[1]!]
                else
                  nextRemainingPorts := nextRemainingPorts.push #[dups[1]!]
              else
                bindPorts := bindPorts.push port
                nextRemainingPorts := nextRemainingPorts.push #[]

            let matchPort := bindPorts[matchIdx]!
            -- Need another DUP for MAT vs binding
            let matDups ← buildDupChain matchPort 2
            let matPort := matDups[0]!
            let bindMatchPort := matDups[1]!
            let finalBindPorts := bindPorts.set! matchIdx bindMatchPort

            let mat ← LowerM.addNode (.mat tag)
            LowerM.connect ⟨mat, ⟨1⟩⟩ matPort

            bindAllPatterns patsArray finalBindPorts
            let hitBodyPort ← lowerExpr body
            LowerM.connect ⟨mat, ⟨2⟩⟩ hitBodyPort

            -- Combine with remaining ports from previous arms
            let combinedRemaining := combineRemainingPorts remainingPortsPerArm nextRemainingPorts
            let missPort ← lowerArmsChainMultiWithPorts combinedRemaining rest
            LowerM.connect ⟨mat, ⟨3⟩⟩ missPort

            pure (PortId.principal mat)

  /-- Combine remaining port arrays -/
  combineRemainingPorts (prev : Array (Array PortId)) (next : Array (Array PortId))
      : Array (Array PortId) :=
    next ++ prev

  /-- Bind all patterns to corresponding scrutinee ports -/
  bindAllPatterns (patterns : Array (Soma.Metal.Pattern Value))
      (scrutPorts : Array PortId) : LowerM Unit := do
    for i in [:patterns.size.min scrutPorts.size] do
      bindPatternRecursive patterns[i]! scrutPorts[i]! 0

  /-- Recursively bind variables in a pattern.

      This function uses the usage map from type checking to build appropriate
      DUP chains for pattern-bound variables. Each variable binding looks up
      its actual usage count and creates a DUP chain accordingly.

      For compound patterns (ctor, tuple, etc.), we DUP the scrutinee once
      per field to enable projection. The per-variable usage is then handled
      when recursing into each sub-pattern.

      The depth limit is configurable via LowerCtx.maxPatternDepth to prevent
      stack overflow on deeply nested patterns. -/
  bindPatternRecursive (pat : Soma.Metal.Pattern Value) (port : PortId) (depth : Nat)
      : LowerM Unit := do
    let ctx ← LowerM.getCtx
    if depth > ctx.maxPatternDepth then pure ()
    else
      match pat with
      | .var binding name _info _span =>
        -- Look up actual usage count from type checking
        let ctx ← LowerM.getCtx
        let usageCount := ctx.getUsageCount binding
        if usageCount == 0 then
          -- Variable is unused (erased) - connect to ERA
          let era ← LowerM.addNode .era
          LowerM.connect (PortId.principal era) port
        else
          -- Build DUP chain based on actual usage
          let usePorts ← buildDupChain port usageCount
          LowerM.modifyCtx fun ctx => ctx.bindVar binding name usePorts

      | .wildcard _info _span =>
        let era ← LowerM.addNode .era
        LowerM.connect (PortId.principal era) port

      | .ctor _name args _info _span =>
        if args.isEmpty then
          -- Nullary constructor - just erase the value
          let era ← LowerM.addNode .era
          LowerM.connect (PortId.principal era) port
        else
          -- DUP the scrutinee once per field for projection
          -- Per-variable usage is handled in the recursive calls
          let dupPorts ← buildDupChain port args.size
          for i in [:args.size] do
            let proj ← LowerM.addNode (.proj i)
            LowerM.connect ⟨proj, ⟨1⟩⟩ dupPorts[i]!
            bindPatternRecursive args[i]! (PortId.principal proj) (depth + 1)

      | .tuple elements _info _span =>
        if elements.isEmpty then
          let era ← LowerM.addNode .era
          LowerM.connect (PortId.principal era) port
        else
          -- DUP the scrutinee once per element for projection
          let dupPorts ← buildDupChain port elements.size
          for i in [:elements.size] do
            let proj ← LowerM.addNode (.proj i)
            LowerM.connect ⟨proj, ⟨1⟩⟩ dupPorts[i]!
            bindPatternRecursive elements[i]! (PortId.principal proj) (depth + 1)

      | .as binding name inner _info _span =>
        -- As-pattern: the binding gets its own usage, plus we need one copy for inner
        let ctx ← LowerM.getCtx
        let bindingUsage := ctx.getUsageCount binding
        -- Total copies needed: bindingUsage + 1 (for inner pattern)
        let totalNeeded := bindingUsage + 1
        let dupPorts ← buildDupChain port totalNeeded
        -- First `bindingUsage` ports go to the binding
        let bindingPorts := dupPorts.extract 0 bindingUsage
        if bindingUsage > 0 then
          LowerM.modifyCtx fun ctx => ctx.bindVar binding name bindingPorts
        -- Last port goes to inner pattern
        bindPatternRecursive inner dupPorts[bindingUsage]! (depth + 1)

      | .lit _lit _span =>
        let era ← LowerM.addNode .era
        LowerM.connect (PortId.principal era) port

      | .array elements _info _span =>
        if elements.isEmpty then
          let era ← LowerM.addNode .era
          LowerM.connect (PortId.principal era) port
        else
          -- DUP the scrutinee once per element for projection
          let dupPorts ← buildDupChain port elements.size
          for i in [:elements.size] do
            let proj ← LowerM.addNode (.proj i)
            LowerM.connect ⟨proj, ⟨1⟩⟩ dupPorts[i]!
            bindPatternRecursive elements[i]! (PortId.principal proj) (depth + 1)

      | .cons head tail _info _span =>
        -- Cons pattern: need to project head and tail
        let dupPorts ← buildDupChain port 2
        let projHead ← LowerM.addNode (.proj 0)
        LowerM.connect ⟨projHead, ⟨1⟩⟩ dupPorts[0]!
        bindPatternRecursive head (PortId.principal projHead) (depth + 1)

        let projTail ← LowerM.addNode (.proj 1)
        LowerM.connect ⟨projTail, ⟨1⟩⟩ dupPorts[1]!
        bindPatternRecursive tail (PortId.principal projTail) (depth + 1)

      | .variant _label arg _info _span =>
        match arg with
        | none =>
          let era ← LowerM.addNode .era
          LowerM.connect (PortId.principal era) port
        | some innerPat =>
          let proj ← LowerM.addNode (.proj 0)
          LowerM.connect ⟨proj, ⟨1⟩⟩ port
          bindPatternRecursive innerPat (PortId.principal proj) (depth + 1)

/-- Lower a global reference.

    For function references, we distinguish between:
    1. **Self-recursive calls** (calling the currently-compiling function):
       Emit an ALO (allocation) node for lazy instantiation.
       This enables infinite unfolding without building infinite graphs.

    2. **Other function references** (calling a different function):
       Emit a REF node pointing to the book entry.
       During reduction, when APP-REF interacts, an ALO is created.

    The key insight from the spec (Section 6.5):
    - REF is a static "address" of a definition in the book
    - ALO is the dynamic "instantiation" that expands lazily
    - For self-recursion, we know at compile time that instantiation is needed
-/
partial def lowerGlobal (name : Name) : LowerM PortId := do
  let ctx ← LowerM.getCtx
  -- First check if it's a known function
  match ctx.lookupGlobal name with
  | some idx =>
    -- Check if this is a self-recursive call
    let isSelfRecursive := ctx.currentFn == some name
    if isSelfRecursive then
      -- Self-recursive call: emit ALO for lazy instantiation
      let alo ← LowerM.addNode (.alo idx)
      pure (PortId.principal alo)
    else
      -- Reference to another function: emit REF
      -- The reducer will create ALO when this REF interacts with APP
      let ref ← LowerM.addNode (.ref idx)
      pure (PortId.principal ref)
  | none =>
    -- Check if it's a constructor (nullary constructors show up as globals)
    match name.ctorTag? with
    | some tag =>
      -- It's a constructor with no arguments
      let ctor ← LowerM.addNode (.ctor tag 0)
      pure (PortId.principal ctor)
    | none =>
      -- Also check by looking up in the constructor registry (using Name)
      match ctx.lookupCtor name with
      | some (_, tag, arity) =>
        if arity == 0 then
          let ctor ← LowerM.addNode (.ctor tag 0)
          pure (PortId.principal ctor)
        else
          -- Partial app, should've already been desugared (todo: consider panicking here) 
          let era ← LowerM.addNode .era
          pure (PortId.principal era)
      | none =>
        -- Unknown global: ERA placeholder
        let era ← LowerM.addNode .era
        pure (PortId.principal era)

/-- Lower field access (projection) -/
partial def lowerFieldAccess (expr : Expr Value scope) (fieldIdx : Nat) : LowerM PortId := do
  let exprPort ← lowerExpr expr
  let proj ← LowerM.addNode (.proj fieldIdx)
  LowerM.connect ⟨proj, ⟨1⟩⟩ exprPort
  pure (PortId.principal proj)

/-- Lower a record literal -/
partial def lowerRecord (fields : Soma.Metal.RecordFieldList Value scope) : LowerM PortId := do
  let fieldPorts ← lowerRecordFields fields
  let rec_ ← LowerM.addNode (.record fieldPorts.size)

  for i in [:fieldPorts.size] do
    LowerM.connect ⟨rec_, ⟨i + 1⟩⟩ fieldPorts[i]!

  pure (PortId.principal rec_)

/-- Lower record fields -/
partial def lowerRecordFields (fields : Soma.Metal.RecordFieldList Value scope) : LowerM (Array PortId) := do
  match fields with
  | .nil => pure #[]
  | .cons _name expr rest =>
    let port ← lowerExpr expr
    let restPorts ← lowerRecordFields rest
    pure (#[port] ++ restPorts)

/-- Lower a record update expression.

    Record update `{ base | field1 = val1, field2 = val2 }` is lowered as:
    1. Project all fields from the base record
    2. For each field in updates, use the new value instead
    3. Construct a new record with the combined fields

    The type info contains the record type, from which we extract field names -/
partial def lowerRecordUpdate (base : Expr Value scope)
    (updates : Soma.Metal.RecordFieldList Value scope) : LowerM PortId := do
  -- Get the record type from base's type annotation
  let fieldNames := match base.getInfo with
    | some ty => extractRecordFieldNames ty
    | none => #[]

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
    let basePort ← lowerExpr base

    -- DUP the base for each field we need to project
    -- We need one copy per non-updated field
    let numNonUpdated := numFields - updateList.length
    let numCopies := if numNonUpdated > 0 then numNonUpdated else 1

    let basePorts ← buildDupChain basePort numCopies
    let mut basePortIdx := 0

    -- For each field, either project from base or use the update value
    let mut fieldPorts : Array PortId := #[]

    for i in [:numFields] do
      let fieldName := fieldNames[i]!
      match updateMap.get? fieldName with
      | some updateExpr =>
        -- Use the update value
        let updatePort ← lowerExpr updateExpr
        fieldPorts := fieldPorts.push updatePort
      | none =>
        -- Project from base
        if basePortIdx < basePorts.size then
          let proj ← LowerM.addNode (.proj i)
          LowerM.connect ⟨proj, ⟨1⟩⟩ basePorts[basePortIdx]!
          fieldPorts := fieldPorts.push (PortId.principal proj)
          basePortIdx := basePortIdx + 1
        else
          -- Fallback: should not happen with correct typing
          let era ← LowerM.addNode .era
          fieldPorts := fieldPorts.push (PortId.principal era)

    -- Construct the new record
    let rec_ ← LowerM.addNode (.record numFields)
    for i in [:numFields] do
      LowerM.connect ⟨rec_, ⟨i + 1⟩⟩ fieldPorts[i]!

    pure (PortId.principal rec_)

/-- Lower a variant injection expression.

    Variant injection `.Label(args)` is lowered as a CTOR node where:
    - The tag is derived from hashing the label name
    - The args become the constructor fields

    For nullary variants (.Label), we emit a 0-arity CTOR.
    For unary variants (.Label(val)), we emit a 1-arity CTOR.
    For multi-field variants, args are packed into fields. -/
partial def lowerInject (label : String) (args : ExprList Value scope) : LowerM PortId := do
  let argPorts ← lowerExprList args

  -- Use label hash as the constructor tag
  -- This ensures consistent tags across compilation units
  let tag := label.hash.toNat % 0xFFFFFF  -- Keep within 24-bit range

  let ctor ← LowerM.addNode (.ctor tag argPorts.size)
  for i in [:argPorts.size] do
    LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ argPorts[i]!

  pure (PortId.principal ctor)

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
partial def lowerFirstClassProj (fieldIdx : Nat) : LowerM PortId := do
  -- Create LAM node (not erased - the parameter is used)
  let lam ← LowerM.addNode (.lam false)

  -- The LAM's aux0 (var port) will receive the record argument
  let varPort : PortId := ⟨lam, ⟨1⟩⟩

  -- Create PROJ node to extract the field
  let proj ← LowerM.addNode (.proj fieldIdx)

  -- Connect: LAM.var → PROJ.input
  LowerM.connect ⟨proj, ⟨1⟩⟩ varPort

  -- Connect: PROJ.principal → LAM.body
  LowerM.connect ⟨lam, ⟨2⟩⟩ (PortId.principal proj)

  -- Return the LAM's principal port (the function value)
  pure (PortId.principal lam)

/-- Lower a tuple -/
partial def lowerTuple (elems : ExprList Value scope) : LowerM PortId := do
  let elemPorts ← lowerExprList elems
  -- Tuple as a 0-tagged constructor
  let ctor ← LowerM.addNode (.ctor 0 elemPorts.size)

  for i in [:elemPorts.size] do
    LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ elemPorts[i]!

  pure (PortId.principal ctor)

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
    The runtime can optimize large arrays to use heap-allocated contiguous memory.

    Element type is inferred as i64 by default (polymorphic arrays would need
    type information from the elaborator). -/
partial def lowerArray (elems : ExprList Value scope) : LowerM PortId := do
  let elemPorts ← lowerExprList elems
  let len := elemPorts.size

  -- Create length node
  let lenNode ← LowerM.addNode (.num .u64 len.toUInt32)

  -- Create data node: for now, store elements in a CTOR
  -- Tag 0xFFFFFE is reserved for array backing storage
  let dataNode ← LowerM.addNode (.ctor 0xFFFFFE len)
  for i in [:len] do
    LowerM.connect ⟨dataNode, ⟨i + 1⟩⟩ elemPorts[i]!

  -- Create ARRAY node (default element type i64)
  let arrayNode ← LowerM.addNode (.array .i64)
  LowerM.connect ⟨arrayNode, ⟨1⟩⟩ (PortId.principal lenNode)   -- aux0 = length
  LowerM.connect ⟨arrayNode, ⟨2⟩⟩ (PortId.principal dataNode)  -- aux1 = data

  pure (PortId.principal arrayNode)

/-- Lower a pair -/
partial def lowerPair (fst snd : Expr Value scope) : LowerM PortId := do
  let fstPort ← lowerExpr fst
  let sndPort ← lowerExpr snd

  let ctor ← LowerM.addNode (.ctor 0 2)
  LowerM.connect ⟨ctor, ⟨1⟩⟩ fstPort
  LowerM.connect ⟨ctor, ⟨2⟩⟩ sndPort

  pure (PortId.principal ctor)

/-- Lower a projection -/
partial def lowerProj (expr : Expr Value scope) (idx : Nat) : LowerM PortId := do
  let exprPort ← lowerExpr expr
  let proj ← LowerM.addNode (.proj idx)
  LowerM.connect ⟨proj, ⟨1⟩⟩ exprPort
  pure (PortId.principal proj)

end

/-- Lower a function definition -/
def lowerFunction (fn : Soma.Metal.UntypedFunction) : LowerM NodeId := do
  -- Set current function for recursion detection
  LowerM.modifyCtx fun ctx => { ctx with currentFn := some fn.name }

  -- Convert untyped body to Value-annotated (using placeholder)
  let typedBody := fn.body.mapInfo (fun () => Value.vType Soma.Core.Level.zero)

  -- Create LAM nodes for parameters
  let paramList := fn.params.toList
  let mut lamNodes : Array NodeId := #[]
  let ctx ← LowerM.getCtx

  for param in paramList do
    let (bindingId, name) := param
    -- Look up actual usage count from type checking
    let usageCount := ctx.getUsageCount bindingId
    let erased := usageCount == 0
    let lam ← LowerM.addNode (.lam erased)
    lamNodes := lamNodes.push lam

    -- Build DUP chain based on actual usage
    let varPort : PortId := ⟨lam, ⟨1⟩⟩
    if usageCount == 0 then
      -- Erased parameter so we connect to ERA
      let era ← LowerM.addNode .era
      LowerM.connect (PortId.principal era) varPort
    else
      -- Build DUP chain for actual usage count
      let usePorts ← buildDupChain varPort usageCount
      LowerM.modifyCtx fun ctx => ctx.bindVar bindingId name usePorts

  -- Wire LAMs together
  for i in [:lamNodes.size - 1] do
    let outer := lamNodes[i]!
    let inner := lamNodes[i + 1]!
    LowerM.connect ⟨outer, ⟨2⟩⟩ (PortId.principal inner)

  -- Lower the body
  let bodyPort ← lowerExpr typedBody

  if lamNodes.isEmpty then
    -- No parameters: body is the root
    pure bodyPort.node
  else
    -- Wire body to innermost LAM
    let innermost := lamNodes[lamNodes.size - 1]!
    LowerM.connect ⟨innermost, ⟨2⟩⟩ bodyPort
    pure lamNodes[0]!

/-- Register type definitions (constructors) -/
def registerTypes (types : Array Soma.Metal.TypeDef) : LowerM Unit := do
  for typeDef in types do
    match typeDef with
    | .algebraic name _tvars ctors =>
      for ctor in ctors do
        let arity := ctor.fieldTypeSyntax.size
        LowerM.modifyCtx fun ctx =>
          ctx.registerCtor ctor.name name ctor.tag arity
    | .struct name _tvars ctorName fields =>
      let arity := fields.size
      LowerM.modifyCtx fun ctx =>
        ctx.registerCtor ctorName name 0 arity
    | .record name _tvars fields =>
      let arity := fields.size
      LowerM.modifyCtx fun ctx =>
        ctx.registerCtor name name 0 arity

/-- Lower an entire module -/
def lowerModule (module : Soma.Metal.Module) : LowerM Unit := do
  -- Register type constructors
  registerTypes module.types

  -- First pass: register all functions as globals
  let functions := module.functions.toList
  for (i, fn) in enumList functions do
    LowerM.modifyCtx fun ctx => ctx.registerGlobal fn.name i

  -- Second pass: lower each function
  for fn in functions do
    let root ← lowerFunction fn
    let arity := fn.params.size
    let _ ← LowerM.addDefinition fn.name.display root arity

  -- Set root to main function if it exists
  let ctx ← LowerM.getCtx
  let mainEntry := ctx.globals.toList.find? fun (name, _) => name.original == "main"
  match mainEntry with
  | some (_, idx) =>
    let ref ← LowerM.addNode (.ref idx)
    LowerM.setRoot (PortId.principal ref)
  | none =>
    -- todo: create a special node for this maybe?
    let era ← LowerM.addNode .era
    LowerM.setRoot (PortId.principal era)

/-- Lower a Metal module to Circuit IR -/
def lower (module : Soma.Metal.Module) (usageMap : UsageMap) : Graph :=
  LowerM.build (lowerModule module) usageMap

end Soma.Circuit.Lower
