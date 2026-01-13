import Soma.Circuit.PatternMatch.Pattern
import Soma.Circuit.PatternMatch.Matrix
import Soma.Circuit.PatternMatch.Decision
import Soma.Circuit.PatternMatch.Compile
import Soma.Circuit.Graph
import Soma.Circuit.Node
import Soma.Metal.Expr
import Soma.Core.Value
import Std.Data.HashMap

namespace Soma.Circuit.PatternMatch

open Soma.Circuit.Graph (Graph GraphM)
open Soma.Circuit.Node (Node NodeId PortId PortIdx Label)
open Soma.Metal (BindingId Literal)
open Soma.Core (Value)

/-- The unit type -/
def unitTy : Value := Value.vPrimTy .unit

/-- Type class for monads that can perform graph operations -/
class MonadGraph (M : Type → Type) where
  /-- Add a node to the graph with its type -/
  addNode : Node → Value → M NodeId
  /-- Connect two ports -/
  connect : PortId → PortId → M Unit
  /-- Get a fresh DUP label -/
  freshLabel : M Label
  /-- Get n fresh labels -/
  freshLabels : Nat → M (Array Label)

/-- GraphM instance for MonadGraph -/
instance : MonadGraph GraphM where
  addNode := GraphM.addNode
  connect := GraphM.connect
  freshLabel := GraphM.freshLabel
  freshLabels := GraphM.freshLabels

/-- State for lowering -/
structure LowerState where
  /-- Maps occurrences to their corresponding (port, type) pairs -/
  occurrenceCache : Std.HashMap Occurrence (PortId × Value) := {}
  /-- The original scrutinee ports (one per column) -/
  scrutinees : Array PortId := #[]
  /-- The types of the original scrutinees (one per column) -/
  scrutineeTypes : Array Value := #[]
  /-- The result type of the match expression -/
  resultType : Value := unitTy
  deriving Inhabited

/-- Pattern match lowering monad, parameterized over the base monad -/
abbrev LowerT (M : Type → Type) := StateT LowerState M

namespace LowerT

variable {M : Type → Type} [Monad M] [MonadGraph M]

/-- Run the lowering monad -/
def run (m : LowerT M α) (scrutinees : Array PortId) (scrutineeTypes : Array Value) (resultType : Value)
    : M (α × LowerState) :=
  StateT.run m { scrutinees := scrutinees, scrutineeTypes := scrutineeTypes, resultType := resultType }

/-- Add a node to the graph with its type -/
def addNode (n : Node) (ty : Value) : LowerT M NodeId :=
  StateT.lift (MonadGraph.addNode n ty)

/-- Add an ERA node (eraser) -/
def addEra : LowerT M NodeId :=
  addNode .era unitTy

/-- Add a DUP node with a label and type -/
def addDup (label : Label) (ty : Value) : LowerT M NodeId :=
  addNode (.dup label) ty

/-- Add a PROJ node with the projected field's type -/
def addProj (fieldIdx : Nat) (ty : Value) : LowerT M NodeId :=
  addNode (.proj fieldIdx) ty

/-- Add a MAT node with the result type -/
def addMat (tag : Nat) (ty : Value) : LowerT M NodeId :=
  addNode (.mat tag) ty

/-- Connect two ports -/
def connect (p1 p2 : PortId) : LowerT M Unit :=
  StateT.lift (MonadGraph.connect p1 p2)

/-- Get a fresh DUP label -/
def freshLabel : LowerT M Label :=
  StateT.lift MonadGraph.freshLabel

/-- Get n fresh labels -/
def freshLabels (n : Nat) : LowerT M (Array Label) :=
  StateT.lift (MonadGraph.freshLabels n)

/-- Get the state -/
def getState : LowerT M LowerState := get

/-- Modify the state -/
def modifyState (f : LowerState → LowerState) : LowerT M Unit := modify f

/-- Get the result type -/
def getResultType : LowerT M Value := do
  let s ← getState
  pure s.resultType

/-- Cache an occurrence → (port, type) mapping -/
def cacheOccurrence (occ : Occurrence) (port : PortId) (ty : Value) : LowerT M Unit :=
  modifyState fun s => { s with occurrenceCache := s.occurrenceCache.insert occ (port, ty) }

/-- Look up a cached occurrence -/
def lookupOccurrence (occ : Occurrence) : LowerT M (Option (PortId × Value)) := do
  let s ← getState
  pure (s.occurrenceCache.get? occ)

/-- Get scrutinee type for a column -/
def getScrutineeType (column : Nat) : LowerT M Value := do
  let s ← getState
  pure (s.scrutineeTypes[column]?.getD unitTy)

end LowerT


/-- Get the type of a constructor field.
    For data types, we need to look up the constructor's field types.
    This is a simplified version - in practice, you'd look up the constructor info. -/
def getConstructorFieldType (dataType : Value) (fieldIdx : Nat) : Value :=
  match dataType with
  | .vSigma _ _ fst (Soma.Core.Closure.const _ snd) =>
    if fieldIdx == 0 then fst else snd
  | .vDataType _ params =>
    params.head?.getD unitTy
  | _ => unitTy

/-- Resolve an occurrence to a (port, type) pair, generating PROJ nodes as needed. -/
partial def resolveOccurrence {M : Type → Type} [Monad M] [MonadGraph M]
    (occ : Occurrence) : LowerT M (PortId × Value) := do
  match ← LowerT.lookupOccurrence occ with
  | some result => pure result
  | none =>
    let state ← LowerT.getState
    let rootPort := state.scrutinees[occ.column]!
    let rootType ← LowerT.getScrutineeType occ.column

    let (resultPort, resultType) ← occ.path.foldlM (init := (rootPort, rootType))
      fun (currentPort, currentType) fieldIdx => do
        let fieldType := getConstructorFieldType currentType fieldIdx
        let proj ← LowerT.addProj fieldIdx fieldType
        LowerT.connect ⟨proj, ⟨1⟩⟩ currentPort
        pure (PortId.principal proj, fieldType)

    LowerT.cacheOccurrence occ resultPort resultType
    pure (resultPort, resultType)

/-- Build a DUP chain for n uses of a value with its type. -/
def buildDupChain {M : Type → Type} [Monad M] [MonadGraph M]
    (sourcePort : PortId) (n : Nat) (ty : Value) : LowerT M (Array PortId) := do
  if n == 0 then
    let era ← LowerT.addEra
    LowerT.connect (PortId.principal era) sourcePort
    pure #[]
  else if n == 1 then
    pure #[sourcePort]
  else
    let labels ← LowerT.freshLabels (n - 1)
    let mut usePorts : Array PortId := #[]
    let mut chainPort := sourcePort

    for i in [:n - 1] do
      let dup ← LowerT.addDup labels[i]! ty
      LowerT.connect (PortId.principal dup) chainPort
      usePorts := usePorts.push ⟨dup, ⟨1⟩⟩
      chainPort := ⟨dup, ⟨2⟩⟩

    usePorts := usePorts.push chainPort
    pure usePorts

/-! ## Decision Tree Lowering -/

/-- Context passed to arm body lowering. -/
structure ArmContext where
  /-- Variable bindings: (id, name, ports, type). -/
  bindings : Array (BindingId × String × Array PortId × Value)

/-- Type of callback for lowering arm bodies -/
abbrev ArmCallback (M : Type → Type) := Nat → ArmContext → M PortId

/-! ## Mutually Recursive Lowering Functions -/

mutual

/-- Lower a decision tree to Circuit IR. -/
partial def lowerTree {M : Type → Type} [Monad M] [MonadGraph M]
    (tree : DecisionTree)
    (lowerArm : ArmCallback M)
    (usageCounts : Std.HashMap Nat Nat)
    : LowerT M PortId := do
  match tree with
  | .fail =>
    let era ← LowerT.addEra
    pure (PortId.principal era)

  | .leaf bindings armIndex =>
    let resolvedBindings ← bindings.mapM fun binding => do
      let (port, ty) ← resolveOccurrence binding.occurrence
      pure (binding.id, binding.name, port, ty)

    let finalBindings ← resolvedBindings.foldlM (init := #[]) fun acc (id, name, port, ty) =>
      let count := usageCounts.getD id.id 1
      if count == 0 then do
        let era ← LowerT.addEra
        LowerT.connect (PortId.principal era) port
        pure acc
      else do
        let dupPorts ← buildDupChain port count ty
        pure (acc.push (id, name, dupPorts, ty))

    -- Call the arm body lowering callback (lifted to LowerT)
    StateT.lift (lowerArm armIndex ⟨finalBindings⟩)

  | .switch occurrence kind cases default =>
    let (scrutPort, _scrutTy) ← resolveOccurrence occurrence

    match kind with
    | .constructor =>
      lowerConstructorSwitch scrutPort cases default lowerArm usageCounts
    | .literal lits =>
      lowerLiteralSwitch scrutPort lits cases default lowerArm usageCounts

/-- Lower a constructor switch (chain of MAT nodes) -/
partial def lowerConstructorSwitch {M : Type → Type} [Monad M] [MonadGraph M]
    (scrutPort : PortId)
    (cases : Array (Nat × DecisionTree))
    (default : Option DecisionTree)
    (lowerArm : ArmCallback M)
    (usageCounts : Std.HashMap Nat Nat)
    : LowerT M PortId := do
  if cases.isEmpty then
    match default with
    | some d => lowerTree d lowerArm usageCounts
    | none =>
      let era ← LowerT.addEra
      LowerT.connect (PortId.principal era) scrutPort
      pure (PortId.principal era)
  else
    lowerMATChain scrutPort cases.toList default lowerArm usageCounts

/-- Lower a literal switch using MAT nodes -/
partial def lowerLiteralSwitch {M : Type → Type} [Monad M] [MonadGraph M]
    (scrutPort : PortId)
    (lits : Array Literal)
    (cases : Array (Nat × DecisionTree))
    (default : Option DecisionTree)
    (lowerArm : ArmCallback M)
    (usageCounts : Std.HashMap Nat Nat)
    : LowerT M PortId := do
  if cases.isEmpty then
    match default with
    | some d => lowerTree d lowerArm usageCounts
    | none =>
      let era ← LowerT.addEra
      LowerT.connect (PortId.principal era) scrutPort
      pure (PortId.principal era)
  else
    let litCases := cases.filterMap fun (idx, tree) =>
      match lits[idx]? with
      | some lit => some (literalToTag lit, tree)
      | none => none
    lowerMATChain scrutPort litCases.toList default lowerArm usageCounts
where
  literalToTag : Literal → Nat
    | .bool true => 1
    | .bool false => 0
    | .int n => n.toNat
    | .string s => s.hash.toNat

/-- Build a chain of MAT nodes -/
partial def lowerMATChain {M : Type → Type} [Monad M] [MonadGraph M]
    (scrutPort : PortId)
    (cases : List (Nat × DecisionTree))
    (default : Option DecisionTree)
    (lowerArm : ArmCallback M)
    (usageCounts : Std.HashMap Nat Nat)
    : LowerT M PortId := do
  let resultTy ← LowerT.getResultType
  match cases with
  | [] =>
    match default with
    | some d => lowerTree d lowerArm usageCounts
    | none =>
      let era ← LowerT.addEra
      LowerT.connect (PortId.principal era) scrutPort
      pure (PortId.principal era)

  | [(tag, subtree)] =>
    let hitPort ← lowerTree subtree lowerArm usageCounts
    let missPort ← match default with
      | some d => lowerTree d lowerArm usageCounts
      | none =>
        let era ← LowerT.addEra
        pure (PortId.principal era)

    let mat ← LowerT.addMat tag resultTy
    LowerT.connect ⟨mat, ⟨1⟩⟩ scrutPort
    LowerT.connect ⟨mat, ⟨2⟩⟩ hitPort
    LowerT.connect ⟨mat, ⟨3⟩⟩ missPort
    pure (PortId.principal mat)

  | (tag, subtree) :: rest =>
    let hitPort ← lowerTree subtree lowerArm usageCounts
    let missPort ← lowerMATChain scrutPort rest default lowerArm usageCounts

    let mat ← LowerT.addMat tag resultTy
    LowerT.connect ⟨mat, ⟨1⟩⟩ scrutPort
    LowerT.connect ⟨mat, ⟨2⟩⟩ hitPort
    LowerT.connect ⟨mat, ⟨3⟩⟩ missPort
    pure (PortId.principal mat)

end

/-! ## Public API -/

/-- Lower a compiled decision tree to Circuit IR -/
def lowerIn {M : Type → Type} [Monad M] [MonadGraph M]
    (tree : DecisionTree)
    (scrutinees : Array PortId)
    (scrutineeTypes : Array Value)
    (resultType : Value)
    (lowerArm : ArmCallback M)
    (usageCounts : Std.HashMap Nat Nat := {})
    : M PortId := do
  let (result, _) ← LowerT.run (lowerTree tree lowerArm usageCounts) scrutinees scrutineeTypes resultType
  pure result

/-- Full compilation and lowering from Metal arms (generic version) -/
def compileAndLowerIn {M : Type → Type} [Monad M] [MonadGraph M]
    (ctx : SimplifyCtx)
    (arms : Soma.Metal.ArmList α scope)
    (scrutinees : Array PortId)
    (scrutineeTypes : Array Value)
    (resultType : Value)
    (lowerArm : ArmCallback M)
    (usageCounts : Std.HashMap Nat Nat := {})
    : M PortId := do
  let matrix := buildMatrixFromArmList ctx arms
  let tree := compileMatrix matrix
  lowerIn tree scrutinees scrutineeTypes resultType lowerArm usageCounts

end Soma.Circuit.PatternMatch
