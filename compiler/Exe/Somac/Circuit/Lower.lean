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
import Soma.Core.Quote
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

/-- Look up the canonical `Value` for a wired-in primitive type by kind -/
private def wiredPrimTy (globals : Soma.Core.GlobalEnv) (p : Soma.Core.PrimType) : Value :=
  globals.primTypeValue? p |>.getD (.vType .zero)

/-- Build the `ty` annotation for an internal CTOR node -/
def ctorFieldChain (globals : Soma.Core.GlobalEnv) (fieldTypes : Array Value) : Value :=
  fieldTypes.foldr Value.arrow (wiredPrimTy globals .unit)

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
  /-- Unique id of the wired-in `World` type -/
  worldUid? : Option Nat := none
  /-- Unique id of the wired-in `Pair` type -/
  pairUid? : Option Nat := none
  /-- Unique id of the wired-in `Bool` type -/
  boolUid? : Option Nat := none
  /-- Qualified name of `io_bind` for call-site inlining -/
  ioBindName? : Option QualifiedName := none
  /-- Qualified name of `pure_io` for call-site inlining -/
  pureIOName? : Option QualifiedName := none
  /-- Tag for the `Pair::Mk` constructor (when known) -/
  pairCtorTag? : Option Nat := none
  /-- The current "World" port for the IO function being lowered -/
  currentWorld? : Option PortId := none
  /-- Types of de Bruijn-bound variables in scope, ordered outermost first -/
  bvarCtx : Array Value := #[]
  /-- Evaluation environment paired with `bvarCtx` -/
  bvarEnv : Soma.Core.Env := .empty
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

/-- Push a new binder onto the bvar context -/
def pushBvar (ctx : LowerCtx) (name : String) (ty : Value) : LowerCtx :=
  let neutral : Value := .vNeutral ty (.nVar ⟨name, ctx.bvarEnv.level⟩)
  { ctx with
    bvarCtx := ctx.bvarCtx.push ty
    bvarEnv := ctx.bvarEnv.extend name neutral }

/-- Look up a wired-in primitive type's canonical `Value` -/
def primTy (ctx : LowerCtx) (p : Soma.Core.PrimType) : Value :=
  wiredPrimTy ctx.evalGlobalEnv p

/-- The unit type used for erased/void values -/
def unitTy (ctx : LowerCtx) : Value := ctx.primTy .unit

/-- The boolean type -/
def boolTy (ctx : LowerCtx) : Value := ctx.primTy .bool

/-- The 32-bit integer type -/
def intTy (ctx : LowerCtx) : Value := ctx.primTy .int

/-- The string type -/
def stringTy (ctx : LowerCtx) : Value := ctx.primTy .string

/-- Reverse lookup -/
def primTypeOf? (ctx : LowerCtx) (uid : Soma.Unique) : Option Soma.Core.PrimType :=
  ctx.evalGlobalEnv.primTyToInductiveId.fold (init := none) fun found p typeUid =>
    match found with
    | some _ => found
    | none => if typeUid == uid then some p else none

end LowerCtx

/-- Apply a list of arguments to a value by peeling vLam/vPi closures -/
private partial def applyArgs (v : Value) : List Value → Option Value
  | [] => some v
  | arg :: rest =>
    match v with
    | .vLam _ body => applyArgs (body.applyPure arg) rest
    | .vPi _ _ _ _ cod => applyArgs (cod.applyPure arg) rest
    | _ => none

/-- Resolve solved metavariables in a Value, substituting solutions at the head -/
partial def resolveMetas (v : Value) (metas : Soma.Core.MetaState) : Value :=
  match v with
  | .vNeutral _ neu =>
    if neu.isBareHead then
      match neu.head with
      | .hMeta m =>
        match metas.lookup m with
        | some info =>
          match info.solution with
          | some sol => resolveMetas sol metas
          | none => v
        | none => v
      | _ => v
    else v
  | .vPi qty binder name dom cod =>
    .vPi qty binder name (resolveMetas dom metas) cod
  | .vDataType dId params =>
    .vDataType dId (params.map (resolveMetas · metas))
  | .vConstructor tag arity args rty =>
    .vConstructor tag arity (args.map (resolveMetas · metas)) (resolveMetas rty metas)
  | .vRowExtend label fieldTy tail =>
    .vRowExtend (resolveMetas label metas) (resolveMetas fieldTy metas) (resolveMetas tail metas)
  | .vRecord row => .vRecord (resolveMetas row metas)
  | .vVariant row => .vVariant (resolveMetas row metas)
  | _ => v

/-- Unfold type abbreviations in a Value -/
partial def unfoldValue (v : Value) (abbrevEnv : Soma.Dependent.AbbrevEnv) : Value :=
  match v with
  | .vDataType dId params =>
    let qn : QualifiedName := ⟨dId⟩
    match abbrevEnv.get? qn with
    | some abbrevInfo =>
      if params.length <= abbrevInfo.arity then
        match applyArgs abbrevInfo.expansion params with
        | some result => unfoldValue result abbrevEnv
        | none => v
      else v
    | none => v
  | _ => v

namespace LowerCtx

/-- True iff `v` is the wired-in `World` type -/
partial def isWorldTy (ctx : LowerCtx) (v : Value) : Bool :=
  let v := unfoldValue v ctx.abbrevEnv
  match v with
  | .vDataType uid _ => ctx.worldUid?.any (· == uid.id)
  | _ => false

/-- True iff `v` is an IO `Pair World a` (wired-in Pair applied with World as its first parameter) -/
partial def isIOPairTy (ctx : LowerCtx) (v : Value) : Bool :=
  let v := unfoldValue v ctx.abbrevEnv
  match v with
  | .vDataType uid params =>
    ctx.pairUid?.any (· == uid.id) && match params with
      | fst :: _ :: _ => ctx.isWorldTy fst
      | _ => false
  | _ => false

/-- True iff a type mentions the wired-in world token -/
partial def mentionsWorldTy (ctx : LowerCtx) (v : Value) : Bool :=
  let v := unfoldValue v ctx.abbrevEnv
  if ctx.isWorldTy v then true else
  match v with
  | .vPi _ _ name dom cod =>
    ctx.mentionsWorldTy dom ||
      let neutral := Value.vNeutral dom (.nVar ⟨name, cod.level?.getD ⟨0⟩⟩)
      ctx.mentionsWorldTy (cod.applyPure neutral)
  | .vLam _ body =>
    let argTy := Value.vType .zero
    ctx.mentionsWorldTy (body.applyPure (Value.vNeutral argTy (.nVar ⟨"_", body.level?.getD ⟨0⟩⟩)))
  | .vNeutral ty _ => ctx.mentionsWorldTy ty
  | .vRowExtend label fieldTy tail =>
    ctx.mentionsWorldTy label || ctx.mentionsWorldTy fieldTy || ctx.mentionsWorldTy tail
  | .vRecord row | .vVariant row => ctx.mentionsWorldTy row
  | .vRecordVal fields => fields.any (fun (_, v) => ctx.mentionsWorldTy v)
  | .vDataType _ params => params.any ctx.mentionsWorldTy
  | .vConstructor _ _ args resultTy =>
    args.any ctx.mentionsWorldTy || ctx.mentionsWorldTy resultTy
  | .vEq _ ty lhs rhs =>
    ctx.mentionsWorldTy ty || ctx.mentionsWorldTy lhs || ctx.mentionsWorldTy rhs
  | .vRefl ty x => ctx.mentionsWorldTy ty || ctx.mentionsWorldTy x
  | .vTransport _ ty motive lhs rhs eq body =>
    ctx.mentionsWorldTy ty || ctx.mentionsWorldTy motive || ctx.mentionsWorldTy lhs ||
      ctx.mentionsWorldTy rhs || ctx.mentionsWorldTy eq || ctx.mentionsWorldTy body
  | _ => false

/-- Is this qualified name `io_bind` -/
def isIOBindName (ctx : LowerCtx) (qn : QualifiedName) : Bool :=
  ctx.ioBindName?.any (· == qn)

/-- Is this qualified name `pure_io` -/
def isPureIOName (ctx : LowerCtx) (qn : QualifiedName) : Bool :=
  ctx.pureIOName?.any (· == qn)

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

/-- Add a node to the graph. `World` and `Pair World X` flow through the Circuit IR as real types -/
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
    (reducibility : Reducibility := .reducible) (effectful : Bool := false) : LowerM Nat :=
  liftGraph (GraphM.addDefinition name root arity ty reducibility effectful)

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
    let unit := (← LowerM.getCtx).unitTy
    let era ← LowerM.addNode .era unit
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
  | .«case» scruts _ arms =>
    let scrutUses := scruts.foldl (init := {}) fun acc s => usageAdd acc (countUsesExpr s)
    let armUses := arms.foldl (init := {}) fun acc arm => usageAdd acc (countUsesExpr arm.body)
    usageAdd scrutUses armUses
  | .fieldAccess expr _ _
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
  | .closure _ captures _ =>
    captures.foldl (init := {}) fun acc cap => usageAdd acc (countUsesExpr cap)
  | .let_ _ _ val body => usageAdd (countUsesExpr val) (countUsesExpr body)
  | .panic _
  | .lit _
  | .const _ _
  | .sort _ | .pi _ _ _ _ _
  | .rowSort | .labelSort | .rowEmpty | .rowExtend _ _ _
  | .recordTy _ | .variantTy _ | .labelLit _ | .dataTy _ _
  | .eqTy _ _ _ _ | .refl _ _ | .transport _ _ _ _ _ _ _
  | .mvar _ | .bvar _ | .proj _ _ _ | .tyvar _ _ => {}

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

/-- Produce an erased runtime placeholder for a computationally absent term -/
def erasedRuntimePort : LowerM PortId := do
  let unit := (← getCtx).unitTy
  let era ← addNode .era unit
  pure (PortId.principal era)

/-- Explicitly consume an unused lambda parameter slot -/
def eraseParamPort (port : PortId) : LowerM Unit := do
  let unit := (← getCtx).unitTy
  let era ← addNode .era unit
  connect (PortId.principal era) port

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
def lowerLiteral (lit : Literal) (targetTy? : Option Value := none) : LowerM PortId := do
  let ctx ← LowerM.getCtx
  match lit with
  | .int n =>
    let encoded := encodeSignedInt n
    let targetPrim? : Option Soma.Core.PrimType :=
      match targetTy?.map (resolveMetas · ctx.metaState) with
      | some (.vDataType uid _) => ctx.primTypeOf? uid
      | _ => none
    let (primTy, valTy) : Somac.Circuit.Term.PrimType × Value :=
      match targetPrim? with
      | some .int64  => (.i64, ctx.primTy .int64)
      | some .int16  => (.i16, ctx.primTy .int16)
      | some .int8   => (.i8,  ctx.primTy .int8)
      | some .word   => (.u32, ctx.primTy .word)
      | some .word8  => (.u8,  ctx.primTy .word8)
      | some .word16 => (.u16, ctx.primTy .word16)
      | some .word64 => (.u64, ctx.primTy .word64)
      | _            => (.i32, ctx.intTy)
    let node := Node.num primTy encoded
    let nid ← LowerM.addNode node valTy
    pure (PortId.principal nid)
  | .float f =>
    let doubleTy := ctx.primTy .double
    let bits := f.toBits
    let lo := (bits &&& 0xFFFFFFFF).toUInt32
    let hi := (bits >>> 32).toUInt32
    let nid ← LowerM.addNode (.num64 .f64 lo hi) doubleTy
    pure (PortId.principal nid)
  | .string s =>
    -- String literals: use STRING node
    -- Length is the byte length of the UTF-8 encoded string
    let len := s.utf8ByteSize.toUInt32
    let word64Ty := ctx.primTy .word64
    let lenNode ← LowerM.addNode (.num .u64 len) word64Ty

    -- Intern the string and store its index (not hash) so Alloy can reference it
    let stringIdx ← LowerM.liftGraph (GraphM.internString s)
    let dataNode ← LowerM.addNode (.num .u64 stringIdx.toUInt32) word64Ty

    -- Create STRING node
    let stringNode ← LowerM.addNode .string ctx.stringTy
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
  let ty := resolveMetas ty ctx.metaState
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
      -- Theorem erasure
      let era ← LowerM.addNode .era ty
      pure (PortId.principal era)

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

/-- Check if a Core.Expr is syntactically type-level -/
private def isCoreTypeLevelExpr : Soma.Core.Expr → Bool
  | .sort _ | .pi _ _ _ _ _
  | .rowSort | .labelSort | .rowEmpty | .rowExtend _ _ _
  | .recordTy _ | .variantTy _ | .labelLit _ | .dataTy _ _
  | .eqTy _ _ _ _ | .refl _ _ | .transport _ _ _ _ _ _ _
  | .mvar _ | .bvar _ => true
  | _ => false

/-- Check if a Soma value is a type/row/label sort -/
private def isTypeSort (v : Value) : Bool :=
  match v with
  | .vType _ | .vRowSort | .vLabelSort => true
  | _ => false

/-- Runtime erasure for an application argument derived from the elaborated Pi binder -/
private def isRuntimeErasedBinder (ctx : LowerCtx) (qty : Quantity)
    (_binder : Soma.Core.BinderInfo) (dom : Value) : Bool :=
  qty == .zero || isTypeSort (unfoldValue dom ctx.abbrevEnv)

/-- Count binders that survive into runtime calling convention -/
private partial def runtimeArityFull (ctx : LowerCtx) (ty : Value) : Nat :=
  let ty := unfoldValue ty ctx.abbrevEnv
  match ty with
  | .vPi qty binder name dom cod =>
    let next := match cod with
      | .const _ body => body
      | .term _ env _ =>
        let neutral := Value.vNeutral dom (.nVar ⟨name, env.level⟩)
        cod.applyPure neutral
    let rest := runtimeArityFull ctx next
    if isRuntimeErasedBinder ctx qty binder dom then rest else rest + 1
  | _ => 0

/-- Is this Core.Expr a type-level argument in call-spine position? -/
private def isCoreTypeLevelArg (ctx : LowerCtx) : Soma.Core.Expr → Bool
  | .mvar id =>
    match ctx.metaState.lookup id with
    | some info => isTypeSort info.type
    | none => false
  | e => Soma.Core.Expr.isTypeLevelExpr e

/-- Compute the type of a Core expression -/
def getExprType (e : Soma.Core.Expr) : LowerM Value := do
  let ctx ← LowerM.getCtx
  let ty := Soma.Core.Expr.typeOfWith ctx.bvarCtx ctx.evalGlobalEnv
    (unfoldValue · ctx.abbrevEnv) ctx.bvarEnv ctx.metaState e
  let resolved := resolveMetas ty ctx.metaState
  pure resolved

/-- Evaluate a Core expression to a Value -/
def evalExprToValue (e : Soma.Core.Expr) : LowerM Value := do
  let ctx ← LowerM.getCtx
  let evalCtx : Soma.Core.EvalCtx := {
    env := ctx.bvarEnv
    globals := ctx.evalGlobalEnv
    metas := ctx.metaState
  }
  pure (Soma.Core.evalCoreExpr evalCtx e)

/-- Lower a Core.Expr variable (fvar) by looking up its Unique.id in the bindings map -/
private def lowerCoreVar (u : Unique) : LowerM (Option PortId) := do
  lowerVar u

/-- Reserved ctor tag for panic nodes in the Circuit encoding -/
private def panicTag : Nat := 0xFFFF

/-- Emit a panic-carrying ctor node: `ctor(panicTag, msgHash, line)` -/
private def emitPanicCtor (msg : String) (ty : Value) : LowerM PortId := do
  let ctx ← LowerM.getCtx
  let word64Ty := ctx.primTy .word64
  let word32Ty := ctx.primTy .word
  let msgNode ← LowerM.addNode (Node.num .u64 msg.hash.toUInt32) word64Ty
  let lineNode ← LowerM.addNode (Node.num .u32 0) word32Ty
  let panicCtor ← LowerM.addNode (.ctor panicTag 2) ty
  LowerM.connect ⟨panicCtor, ⟨1⟩⟩ (PortId.principal msgNode)
  LowerM.connect ⟨panicCtor, ⟨2⟩⟩ (PortId.principal lineNode)
  pure (PortId.principal panicCtor)

mutual

/-- Lower a Core.Expr to a Circuit IR subgraph. -/
partial def lowerCoreExpr (e : Soma.Core.Expr) (ty : Value) : LowerM (Option PortId) := do
  let ty := resolveMetas ty (← LowerM.getCtx).metaState
  match e with
  | .fvar u _ => lowerCoreVar u

  | .lit lit => some <$> lowerLiteral lit (some ty)

  | .app fn arg => lowerCoreApp fn arg ty

  | .lam info name _domain body => some <$> lowerCoreLam info name body ty

  | .construct _qn tag args _ =>
    let ctorTy ← getExprType e
    lowerCoreConstruct tag args ctorTy

  | .if_ cond then_ else_ => lowerCoreIf cond then_ else_ ty

  | .«case» scruts _ arms => lowerCoreCase scruts arms ty

  | .const qn _ => some <$> lowerGlobal qn ty

  | .fieldAccess expr _field idx => lowerCoreFieldAccess expr idx ty

  | .record fields => lowerCoreRecord fields ty

  | .tuple elems =>
    let tupleTy ← getExprType e
    lowerCoreTuple elems tupleTy

  | .panic msg =>
    some <$> emitPanicCtor msg ty

  | .ann expr _ty => lowerCoreExpr expr ty

  | .closure qn captures closureTyExpr =>
    let nodeTy ← evalExprToValue closureTyExpr
    lowerCoreClosure qn captures nodeTy

  | .array elems _ => lowerCoreArray elems (← getExprType e)

  | .proj _typeName _field idx => some <$> lowerFirstClassProj idx ty

  | .inject label args _ =>
    let injectTy ← getExprType e
    lowerCoreInject label args injectTy

  | .recordUpdate base updates => lowerCoreRecordUpdate base updates ty

  | .mvar id =>
    let ctx ← LowerM.getCtx
    match ctx.metaState.lookup id with
    | some info =>
      match info.solution with
      | some sol =>
        lowerCoreExpr (Soma.Core.quoteExpr0 sol) ty
      | none =>
        if isTypeSort (unfoldValue info.type ctx.abbrevEnv) then
          pure none
        else
          panic! s!"Circuit lowering found unsolved runtime metavariable ?{id.id} : {Soma.Core.valueToString info.type}"
    | none =>
      panic! s!"Circuit lowering found unknown runtime metavariable ?{id.id}"

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
          -- Body is type-level: still force val for effects
          let unit := (← LowerM.getCtx).unitTy
          let era ← LowerM.addNode .era unit
          LowerM.connect (PortId.principal era) valPort
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
  | .sort _ | .pi _ _ _ _ _
  | .rowSort | .labelSort | .rowEmpty
  | .rowExtend _ _ _ | .recordTy _ | .variantTy _
  | .labelLit _ | .dataTy _ _ | .eqTy _ _ _ _
  | .refl _ _ | .transport _ _ _ _ _ _ _
  | .bvar _ | .tyvar _ _ =>
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
      let explicitArgs := allArgs.filter (!isCoreTypeLevelArg ctx ·)
      if explicitArgs.size == arity then
        -- A fully-applied constructor is a value of the data-type head
        let fullApp := allArgs.foldl (init := baseFn) (fun acc a => .app acc a)
        let ctorTy ← getExprType fullApp
        lowerCoreConstruct tag explicitArgs ctorTy
      else
        lowerCoreAppDefault fn arg ty
    | none =>
      let typeArgExprs := allArgs.filter (isCoreTypeLevelArg ctx)
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
      let ctx ← LowerM.getCtx
      if isCoreTypeLevelArg ctx arg then
        lowerCoreExpr fn ty
      else
        lowerCoreAppGeneric fn arg ty

/-- Create a dummy neutral for piApply that uses the Pi codomain's closure env -/
private partial def dummyNeutralForPi (piTy : Value) (argTy : Value) : Value :=
  match piTy with
  | .vPi _ _ name _ cod =>
    Value.vNeutral argTy (.nVar ⟨name, cod.level?.getD ⟨0⟩⟩)
  | _ => Value.vNeutral argTy (.nVar ⟨"_", ⟨0⟩⟩)

/-- Generic application lowering for Core.Expr -/
partial def lowerCoreAppGeneric (fn arg : Soma.Core.Expr) (ty : Value)
    : LowerM (Option PortId) := do
  let fnTy ← getExprType fn
  let ctx ← LowerM.getCtx
  -- Unfold type abbreviations if needed
  let effectiveFnTy := match fnTy.piDomain? with
    | some _ => fnTy
    | none => unfoldValue fnTy ctx.abbrevEnv
  match effectiveFnTy with
  | .vPi qty binder _ argTy codomain =>
    -- Compute the actual result type from the Pi codomain
    let resultTy := codomain.applyPure (dummyNeutralForPi effectiveFnTy argTy)
    if isRuntimeErasedBinder ctx qty binder argTy then
      lowerCoreExpr fn resultTy
    else
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
  | _ =>
    let fnPort? ← lowerCoreExpr fn fnTy
    match fnPort? with
    | none => pure none
    | some fnPort =>
      let argTy ← getExprType arg
      let argPort? ← lowerCoreExpr arg argTy
      match argPort? with
      | some argPort =>
        let app ← LowerM.addNode .app ty
        LowerM.connect ⟨app, ⟨1⟩⟩ fnPort
        LowerM.connect ⟨app, ⟨2⟩⟩ argPort
        pure (some (PortId.principal app))
      | none =>
        pure (some fnPort)

/-- Lower a Core.Expr lambda -/
partial def lowerCoreLam (_info : Soma.Core.BinderInfo) (name : String)
    (body : Soma.Core.Expr) (ty : Value) : LowerM PortId := do
  -- The body uses bvar(0) for the lambda parameter (locally nameless).
  let paramUnique ← LowerM.freshSyntheticUnique name
  let paramTyExpr := match ty.piDomain? with
    | some d => Soma.Core.quoteExpr0 d
    | none => .sort .zero
  let openBody := Soma.Core.Expr.instantiate body (.fvar paramUnique paramTyExpr)

  let paramTy := match ty.piDomain? with
    | some d => d
    | none => panic! s!"lowerCoreLam: expected Pi type for parameter, got {ty}"

  let paramNeutral := Value.vNeutral paramTy (.nVar ⟨name, ⟨paramUnique.id⟩⟩)
  let codomainTy := match ty.piApply paramNeutral with
    | some t => t
    | none => panic! s!"lowerCoreLam: expected Pi type for codomain, got {ty}"

  let usageCount := (countUsesExpr openBody).getD paramUnique 0
  let erased := usageCount == 0
  let lam ← LowerM.addNode (.lam erased) ty
  let varPort : PortId := ⟨lam, ⟨1⟩⟩
  LowerM.modifyCtx fun ctx =>
    ctx.bindVarOwned paramUnique name varPort usageCount paramTy erased
  if erased then
    LowerM.eraseParamPort varPort

  let bodyPort? ← lowerCoreExpr openBody codomainTy
  let bodyPort ← match bodyPort? with
    | some port => pure port
    | none => LowerM.erasedRuntimePort
  LowerM.connect ⟨lam, ⟨2⟩⟩ bodyPort

  pure (PortId.principal lam)

/-- Lower a Core.Expr constructor application -/
partial def lowerCoreConstruct (tag : Nat) (args : Array Soma.Core.Expr)
    (ty : Value) : LowerM (Option PortId) := do
  let ctx ← LowerM.getCtx
  let resolvedTy := resolveMetas ty ctx.metaState
  let isBoolCtor : Bool :=
    match ctx.boolUid?, resolvedTy with
    | some bid, .vDataType uid _ => uid.id == bid && args.isEmpty
    | _, _ => false
  if isBoolCtor then
    let nid ← LowerM.addNode (.num .bool tag.toUInt32) resolvedTy
    pure (some (PortId.principal nid))
  else
    let mut argPorts : Array PortId := #[]
    for arg in args do
      let argTy ← getExprType arg
      let port? ← lowerCoreExpr arg argTy
      match port? with
      | some port => argPorts := argPorts.push port
      | none => pure ()

    let ctor ← LowerM.addNode (.ctor tag argPorts.size) resolvedTy
    for i in [:argPorts.size] do
      LowerM.connect ⟨ctor, ⟨i + 1⟩⟩ argPorts[i]!

    pure (some (PortId.principal ctor))

/-- Lower a Core.Expr if-then-else -/
partial def lowerCoreIf (cond then_ else_ : Soma.Core.Expr) (ty : Value)
    : LowerM (Option PortId) := do
  let bool := (← LowerM.getCtx).boolTy
  let condPort? ← lowerCoreExpr cond bool
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
  else if arms.isEmpty then
    for (scrutPort, scrutTy) in scrutPorts.zip scrutTypes do
      let era ← LowerM.addNode .era scrutTy
      LowerM.connect (PortId.principal era) scrutPort
    some <$> emitPanicCtor "unreachable: absurd match on uninhabited type" ty
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
      let unit := (← LowerM.getCtx).unitTy
      let era ← LowerM.addNode .era unit
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

  let ctx ← LowerM.getCtx
  let envPort ← if capturePairs.isEmpty then do
    let era ← LowerM.addNode .era ctx.unitTy
    pure (PortId.principal era)
  else if capturePairs.size == 1 then do
    pure capturePairs[0]!.1
  else do
    let captureTypes := capturePairs.map (·.2)
    let envTy := ctorFieldChain ctx.evalGlobalEnv captureTypes
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
  let ctx ← LowerM.getCtx
  let word64Ty := ctx.primTy .word64
  let lenNode ← LowerM.addNode (.num .u64 len.toUInt32) word64Ty
  let backingTy := ctorFieldChain ctx.evalGlobalEnv (List.replicate len elemTy).toArray
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

/-- Count the number of LAM nodes in a chain starting from a root node -/
def countLamChainArity (root : NodeId) : LowerM Nat := do
  let mut count := 0
  let mut current := root
  for _ in [:100] do
    let node? ← LowerM.liftGraph (get >>= fun g => pure (g.getNode current))
    match node? with
    | some entry =>
      match entry.node with
      | .lam _ =>
        count := count + 1
        match entry.getPort ⟨2⟩ with
        | some bodyPort => current := bodyPort.node
        | none => break
      | _ => break
    | none => break
  return count

/-- Advance past any leading implicit type-parameter Pi binders in a type value -/
private partial def skipImplicitTypeParams (ctx : LowerCtx) (ty : Value) : Value :=
  let ty := unfoldValue ty ctx.abbrevEnv
  match ty with
  | .vPi _ binder name dom cod =>
    let isErasedImplicit := match binder with
      | .implicit | .strictImplicit =>
        match dom with
        | .vType _ | .vRowSort | .vLabelSort => true
        | _ => false
      | _ => false
    if isErasedImplicit then
      let advanced := match cod with
        | .const _ body => body
        | .term _ env _ => cod.applyPure (Value.vNeutral dom (.nVar ⟨name, env.level⟩))
      skipImplicitTypeParams ctx advanced
    else ty
  | _ => ty

/-- Lower a function definition -/
def lowerFunction (fn : Soma.Core.TypedFunction) : LowerM NodeId := do
  LowerM.modifyCtx fun ctx => { ctx with currentFn := some fn.name }

  let paramList := fn.params.toList
  let mut lamNodes : Array NodeId := #[]
  let mut currentTy := fn.fnType
  let bodyUses := countUsesExpr fn.body

  for param in paramList do
    let ctx ← LowerM.getCtx
    currentTy := skipImplicitTypeParams ctx (unfoldValue currentTy ctx.abbrevEnv)
    let (bindingId, name) := param
    let paramTy := match currentTy.piDomain? with
      | some d => d
      | none => panic! s!"lowerFunction: expected Pi type for param '{name}' (fn={fn.name.id.module}::{fn.name.id.original}#{fn.name.id.id}, params={fn.params.size}, valueParams={fn.valueParams.size}, paramNames={fn.params.map (·.2)}), got {currentTy}"
    let paramNeutral := Value.vNeutral paramTy (.nVar ⟨name, ⟨bindingId.id⟩⟩)
    let nextTy := match currentTy.piApply paramNeutral with
      | some c => c
      | none => panic! s!"lowerFunction: expected Pi type for codomain after '{name}', got {currentTy}"

    let usageCount := bodyUses.getD bindingId 0
    let erased := usageCount == 0
    let lam ← LowerM.addNode (.lam erased) currentTy
    lamNodes := lamNodes.push lam
    let varPort : PortId := ⟨lam, ⟨1⟩⟩
    LowerM.modifyCtx fun ctx =>
      ctx.bindVarOwned bindingId name varPort usageCount paramTy erased
    if erased then
      LowerM.eraseParamPort varPort

    currentTy := nextTy

  let ctxAfterParams ← LowerM.getCtx
  currentTy := skipImplicitTypeParams ctxAfterParams
    (unfoldValue currentTy ctxAfterParams.abbrevEnv)
  let bodyTy := currentTy
  let mut etaApps : Array (PortId × Value) := #[]

  let mut etaTy := currentTy
  repeat
    let ctx ← LowerM.getCtx
    let unfolded := unfoldValue etaTy ctx.abbrevEnv
    match unfolded with
    | .vPi qty binder name dom cod =>
      let neutral := Value.vNeutral dom (.nVar ⟨name, cod.level?.getD ⟨0⟩⟩)
      let nextTy := cod.applyPure neutral
      if isRuntimeErasedBinder ctx qty binder dom then
        etaTy := nextTy
      else
        let lam ← LowerM.addNode (.lam false) etaTy
        lamNodes := lamNodes.push lam
        etaApps := etaApps.push (⟨lam, ⟨1⟩⟩, nextTy)
        etaTy := nextTy
    | _ => break

  if lamNodes.size > 1 then
    for i in [:lamNodes.size - 1] do
      let outer := lamNodes[i]!
      let inner := lamNodes[i + 1]!
      LowerM.connect ⟨outer, ⟨2⟩⟩ (PortId.principal inner)

  let bodyPort? ← lowerCoreExpr fn.body bodyTy
  let bodyPort? ← etaApps.foldlM (init := bodyPort?) fun acc (argPort, resultTy) => do
    match acc with
    | none => pure none
    | some fnPort =>
      let app ← LowerM.addNode .app resultTy
      LowerM.connect ⟨app, ⟨1⟩⟩ fnPort
      LowerM.connect ⟨app, ⟨2⟩⟩ argPort
      pure (some (PortId.principal app))

  if lamNodes.isEmpty then
    match bodyPort? with
    | some port => pure port.node
    | none =>
      let unit := (← LowerM.getCtx).unitTy
      let era ← LowerM.addNode .era unit
      pure era
  else
    let innermost := lamNodes[lamNodes.size - 1]!
    let bodyPort ← match bodyPort? with
      | some port => pure port
      | none => LowerM.erasedRuntimePort
    LowerM.connect ⟨innermost, ⟨2⟩⟩ bodyPort
    pure lamNodes[0]!

/-- Register type definitions and build the constructor type registry -/
def registerTypes (types : Array Soma.Core.TypeDef)
    (globals : Option Soma.Dependent.Globals := none) : LowerM Unit := do
  for typeDef in types do
    match typeDef with
    | .algebraic _attrs typeName _tvars _paramCount ctors _ _ =>
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

    | .record _attrs recordName _tvars ctorName fields _ =>
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

  if let some g := globals then
    for (typeQN, indInfo) in g.inductives.toList do
      for ctor in indInfo.ctors do
        LowerM.modifyCtx fun ctx =>
          if ctx.ctorTypeRegistry.contains ⟨typeQN.id, ctor.tag⟩ then ctx
          else
            let ctx := ctx.registerCtor ctor.name typeQN ctor.tag ctor.arity
            ctx.registerCtorType typeQN.id ctor.tag ctor.type

/-- Map from function name to typed function -/
abbrev TypedFunctionMap := Std.HashMap String Soma.Core.TypedFunction

/-- Check if a function should be lowered to actual code -/
def shouldLowerBody (fn : Soma.Core.TypedFunction) : Bool :=
  fn.attrs.intrinsic.isNone && fn.attrs.extern.isNone

/-- Generate a proper Circuit IR function body for a primitive operation -/
def generatePrimOpBody (op : PrimOp) (fnTy : Value) : LowerM (NodeId × Nat) := do
  let ctx ← LowerM.getCtx
  match primOpToOp2Code op with
  | some op2 =>
    -- Binary operation: 2 parameters
    let paramTy := fnTy.piDomain?.getD ctx.intTy
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
      let resultTy := match fnTy.piApply (Value.vNeutral ctx.unitTy (.nVar ⟨"x", ⟨0⟩⟩)) with
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
      let era ← LowerM.addNode .era ctx.unitTy
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
  -- Load intrinsic dispatch metadata, wired-in IO identifiers, and type-checking state
  if let some g := globals then
    LowerM.modifyCtx fun ctx => { ctx with
      intrinsics := g.intrinsics
      evalGlobalEnv := g.toGlobalEnvWithClasses instanceEnv
      metaState := metas
      worldUid?   := g.wiredIn.getUnique? .typeWorld |>.map (·.name.id.id)
      pairUid?    := g.wiredIn.getUnique? .typePair  |>.map (·.name.id.id)
      boolUid?    := g.wiredIn.getUnique? .typeBool  |>.map (·.name.id.id)
      ioBindName? := g.wiredIn.getUnique? .bindIO    |>.map (·.name)
      pureIOName? := g.wiredIn.getUnique? .pureIO    |>.map (·.name)
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
          let arity := info.type.explicitArityFull (some (unfoldValue · abbrevEnv))
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
    let ctx ← LowerM.getCtx
    let root ← lowerFunction fn
    let arity ← countLamChainArity root
    let red := if fn.attrs.irreducible then Reducibility.irreducible else .reducible
    let effectful := ctx.mentionsWorldTy fn.fnType
    let _ ← LowerM.addDefinition fn.name root arity fn.fnType
      (reducibility := red) (effectful := effectful)

  -- Fifth pass: add definitions for intrinsic/extern functions from current module
  for (_, fn) in intrinsics do
    let ctx ← LowerM.getCtx
    match ctx.intrinsics.get? fn.name with
    | some (.primOp op) =>
      let (root, arity) ← generatePrimOpBody op fn.fnType
      let _ ← LowerM.addDefinition fn.name root arity fn.fnType
        (effectful := ctx.mentionsWorldTy fn.fnType)
    | _ =>
      let era ← LowerM.addNode .era ctx.unitTy
      let arity := runtimeArityFull ctx fn.fnType
      let _ ← LowerM.addDefinition fn.name era arity fn.fnType
        (reducibility := .external) (effectful := ctx.mentionsWorldTy fn.fnType)

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
      let ctx ← LowerM.getCtx
      let era ← LowerM.addNode .era ctx.unitTy
      let arity := runtimeArityFull ctx info.type
      let _ ← LowerM.addDefinition info.name era arity info.type
        (reducibility := .external) (effectful := ctx.mentionsWorldTy info.type)

  -- Set root to main function if it exists
  -- Wire an ERA demand node to the root ALO so demand-driven evaluation can proceed
  let ctx ← LowerM.getCtx
  let mainEntry := ctx.globals.toList.find? fun (name, _) => name.id.original == "main"
  match mainEntry with
  | some (_, idx) =>
    let mainTy := match typedFunctions.get? "main" with
      | some typedFn => typedFn.fnType
      | none => ctx.unitTy
    let alo ← LowerM.addNode (.alo idx) mainTy
    let era ← LowerM.addNode .era ctx.unitTy
    LowerM.connect (PortId.principal era) (PortId.principal alo)
    LowerM.setRoot (PortId.principal era)
  | none =>
    let era ← LowerM.addNode .era ctx.unitTy
    LowerM.setRoot (PortId.principal era)

/-- Lower typed functions to Circuit IR -/
def lower (types : Array Soma.Core.TypeDef)
    (typedFunctions : TypedFunctionMap)
    (usageMap : UsageMap)
    (globals : Option Soma.Dependent.Globals := none)
    (instanceEnv : Soma.Dependent.InstanceEnv := .empty)
    (metas : Soma.Core.MetaState := .empty)
    (abbrevEnv : Soma.Dependent.AbbrevEnv := {}) : Graph :=
  LowerM.build
    (lowerModule types typedFunctions globals instanceEnv metas abbrevEnv)
    usageMap

/-- Resolve all metavariables in a Circuit graph's node types and definition types -/
def resolveGraphMetas (g : Graph) (metas : Soma.Core.MetaState) : Graph := Id.run do
  let mut graph := g
  -- Resolve metas in all node types
  for (nodeId, _) in graph.nodes.toList do
    graph := graph.updateNode ⟨nodeId⟩ fun e =>
      { e with ty := resolveMetas e.ty metas }
  -- Resolve metas in all definition types
  for i in List.range graph.book.size do
    if let some d := graph.book[i]? then
      let resolvedTy := resolveMetas d.ty metas
      graph := { graph with book := graph.book.set! i { d with ty := resolvedTy } }
  -- Resolve metas in resolved type arguments
  let mut newResolvedTypeArgs := graph.resolvedTypeArgs
  for (nodeId, args) in graph.resolvedTypeArgs.toList do
    let resolvedArgs := args.map (resolveMetas · metas)
    newResolvedTypeArgs := newResolvedTypeArgs.insert nodeId resolvedArgs
  { graph with resolvedTypeArgs := newResolvedTypeArgs }

end Somac.Circuit.Lower
