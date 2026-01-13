import Soma.Circuit.PatternMatch.Pattern
import Soma.Circuit.PatternMatch.Matrix
import Soma.Circuit.PatternMatch.Decision
import Soma.Circuit.PatternMatch.Compile
import Soma.Circuit.PatternMatch.Types
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
  /-- Cache mapping occurrences to their (port, type) pairs -/
  occurrenceCache : Std.HashMap Occurrence (PortId × Value) := {}
  /-- Cache mapping occurrences to their known types (from bindings) -/
  typeCache : Std.HashMap Occurrence Value := {}
  /-- The original scrutinee ports (one per column) -/
  scrutinees : Array PortId := #[]
  /-- Constructor type registry for field type lookup -/
  registry : ConstructorTypeRegistry := {}
  /-- The types of the original scrutinees -/
  scrutineeTypes : Array Value := #[]
  /-- The result type of the match expression -/
  resultType : Value := unitTy
  deriving Inhabited

/-- Pattern match lowering monad, parameterized over the base monad -/
abbrev LowerT (M : Type → Type) := StateT LowerState M

namespace LowerT

variable {M : Type → Type} [Monad M] [MonadGraph M]

/-- Run the lowering monad -/
def run (m : LowerT M α) (scrutinees : Array PortId) (scrutineeTypes : Array Value)
    (registry : ConstructorTypeRegistry) (resultType : Value)
    : M (α × LowerState) :=
  StateT.run m {
    scrutinees := scrutinees,
    scrutineeTypes := scrutineeTypes,
    registry := registry,
    resultType := resultType
  }

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

/-- Get the constructor type registry -/
def getRegistry : LowerT M ConstructorTypeRegistry := do
  let s ← getState
  pure s.registry

/-- Cache an occurrence → (port, type) mapping -/
def cacheOccurrence (occ : Occurrence) (port : PortId) (ty : Value) : LowerT M Unit :=
  modifyState fun s => { s with occurrenceCache := s.occurrenceCache.insert occ (port, ty) }

/-- Cache just the type for an occurrence (used for pre-populating from bindings) -/
def cacheOccurrenceType (occ : Occurrence) (ty : Value) : LowerT M Unit :=
  modifyState fun s => { s with typeCache := s.typeCache.insert occ ty }

/-- Look up a cached occurrence -/
def lookupOccurrence (occ : Occurrence) : LowerT M (Option (PortId × Value)) := do
  let s ← getState
  pure (s.occurrenceCache.get? occ)

/-- Look up just the type for an occurrence -/
def lookupOccurrenceType (occ : Occurrence) : LowerT M (Option Value) := do
  let s ← getState
  -- First check the full cache, then the type-only cache
  match s.occurrenceCache.get? occ with
  | some (_, ty) => pure (some ty)
  | none => pure (s.typeCache.get? occ)

/-- Get scrutinee type for a column -/
def getScrutineeType (column : Nat) : LowerT M Value := do
  let s ← getState
  pure (s.scrutineeTypes[column]?.getD unitTy)

end LowerT

/-- Get the type of a field at a given index from a parent type -/
def getFieldType (registry : ConstructorTypeRegistry) (parentType : Value)
    (fieldIdx : Nat) : Value :=
  match parentType with
  | .vSigma _qty _name fst snd =>
    -- Sigma types: field 0 is fst, field 1 is snd
    if fieldIdx == 0 then fst
    else match snd with
      | .const _ v => v
      | .term _ _ _ => unitTy -- Can't evaluate dependent closure without argument

  | .vDataType _typeId _params =>
    -- todo: look up field types from registry (requires tag, which we don't have here)
    let fieldTypes := fallbackFieldTypes parentType (fieldIdx + 1)
    fieldTypes[fieldIdx]?.getD unitTy

  | .vRecord row =>
    -- Record types: extract from row
    extractRowFieldType row fieldIdx

  | .vPi _qty _binder _name dom _cod =>
    -- Pi types: field 0 is domain (for dependent tuple-like usage)
    if fieldIdx == 0 then dom else unitTy

  | .vRowExtend _ fieldTy tail =>
    -- Row types: navigate to the right field
    if fieldIdx == 0 then fieldTy
    else getFieldType registry tail (fieldIdx - 1)

  | _ => unitTy
where
  extractRowFieldType (row : Value) (idx : Nat) : Value :=
    match row, idx with
    | .vRowExtend _ fieldTy _, 0 => fieldTy
    | .vRowExtend _ _ tail, n + 1 => extractRowFieldType tail n
    | _, _ => unitTy

/-- Resolve an occurrence to a (port, type) pair, generating PROJ nodes as needed -/
partial def resolveOccurrence {M : Type → Type} [Monad M] [MonadGraph M]
    (occ : Occurrence) : LowerT M (PortId × Value) := do
  -- Check full cache first
  match ← LowerT.lookupOccurrence occ with
  | some result => pure result
  | none =>
    let state ← LowerT.getState
    let rootPort := state.scrutinees[occ.column]!
    let rootType ← LowerT.getScrutineeType occ.column

    -- Cache the root occurrence
    let rootOcc : Occurrence := ⟨occ.column, #[]⟩
    LowerT.cacheOccurrence rootOcc rootPort rootType

    -- Walk down the path, projecting at each step and caching intermediates
    let (resultPort, resultType, _) ← occ.path.foldlM
      (init := (rootPort, rootType, #[]))
      fun (currentPort, currentType, pathSoFar) fieldIdx => do
        let newPath := pathSoFar.push fieldIdx
        let intermediateOcc : Occurrence := ⟨occ.column, newPath⟩

        -- Check if this intermediate occurrence is already fully cached
        match ← LowerT.lookupOccurrence intermediateOcc with
        | some (cachedPort, cachedType) =>
          pure (cachedPort, cachedType, newPath)
        | none =>
          -- Determine field type: prefer pre-cached type, fall back to computation
          let fieldType ← match ← LowerT.lookupOccurrenceType intermediateOcc with
            | some ty => pure ty
            | none => pure (getFieldType state.registry currentType fieldIdx)
          let proj ← LowerT.addProj fieldIdx fieldType
          LowerT.connect ⟨proj, ⟨1⟩⟩ currentPort
          let projPort := PortId.principal proj
          -- Cache this intermediate for reuse
          LowerT.cacheOccurrence intermediateOcc projPort fieldType
          pure (projPort, fieldType, newPath)

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
    -- Pre-cache all binding occurrence types before resolution.
    -- This ensures that when we walk occurrence paths, we have accurate
    -- type information from compilation (which knew the constructor tags).
    for binding in bindings do
      match binding.ty with
      | .vPrimTy .unit => pure ()  -- No type info, skip
      | ty => LowerT.cacheOccurrenceType binding.occurrence ty

    -- Resolve all bindings to (port, type) pairs
    let resolvedBindings ← bindings.mapM fun binding => do
      let (port, ty) ← resolveOccurrence binding.occurrence
      -- The resolved type should now be accurate thanks to pre-caching
      pure (binding.id, binding.name, port, ty)

    -- Build DUP chains based on usage counts
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

/-- Lower a compiled decision tree to Circuit IR with type tracking. -/
def lower {M : Type → Type} [Monad M] [MonadGraph M]
    (tree : DecisionTree)
    (scrutinees : Array PortId)
    (scrutineeTypes : Array Value)
    (registry : ConstructorTypeRegistry)
    (resultType : Value)
    (lowerArm : ArmCallback M)
    (usageCounts : Std.HashMap Nat Nat := {})
    : M PortId := do
  let (result, _) ← LowerT.run
    (lowerTree tree lowerArm usageCounts)
    scrutinees scrutineeTypes registry resultType
  pure result

/-- Full compilation and lowering from Metal arms. -/
def compileAndLower {M : Type → Type} [Monad M] [MonadGraph M]
    (ctx : SimplifyCtx)
    (registry : ConstructorTypeRegistry)
    (arms : Soma.Metal.ArmList α scope)
    (scrutinees : Array PortId)
    (scrutineeTypes : Array Value)
    (resultType : Value)
    (lowerArm : ArmCallback M)
    (usageCounts : Std.HashMap Nat Nat := {})
    : M PortId := do
  let matrix := buildMatrixFromArmList ctx arms
  let tree := compileMatrix matrix registry scrutineeTypes
  lower tree scrutinees scrutineeTypes registry resultType lowerArm usageCounts

end Soma.Circuit.PatternMatch
