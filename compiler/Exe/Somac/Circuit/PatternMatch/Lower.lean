import Somac.Circuit.PatternMatch.Pattern
import Somac.Circuit.PatternMatch.Matrix
import Somac.Circuit.PatternMatch.Decision
import Somac.Circuit.PatternMatch.Compile
import Somac.Circuit.PatternMatch.Types
import Somac.Circuit.Graph
import Somac.Circuit.Node
import Soma.Core.Literal
import Soma.Core.Value
import Soma.Core.Expr
import Std.Data.HashMap

namespace Somac.Circuit.PatternMatch

open Somac.Circuit.Graph (Graph GraphM)
open Somac.Circuit.Node (Node NodeId PortId PortIdx Label)
open Soma.Core (Value)
open Soma (Unique)
open Soma.Core (Literal)

/-- Placeholder used where the pattern-match lowering pipeline (TODO: rename) -/
def unitTy : Value := Value.vType Soma.Core.Level.zero

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

/-- Add a USE (strict evaluation point) node with the continuation's result type -/
def addUse (ty : Value) : LowerT M NodeId :=
  addNode .use ty

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
  | .vDataType unique params =>
    let matchingCtors := registry.fold (init := (#[] : Array ConstructorTypeInfo))
      fun acc key info => if key.unique == unique then acc.push info else acc
    if matchingCtors.size == 1 then
      let info := matchingCtors[0]!
      let instantiated := instantiateFieldTypes info.fieldTypes params.toArray unique
      instantiated[fieldIdx]?.getD unitTy
    else
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

/-- Context passed to arm body lowering. -/
structure ArmContext where
  /-- Variable bindings: (id, name, source port, use count, type). -/
  bindings : Array (Unique × String × PortId × Nat × Value)

/-- Type of callback for lowering arm bodies -/
abbrev ArmCallback (M : Type → Type) := Nat → ArmContext → M PortId

mutual

/-- Lower a decision tree to Circuit IR. -/
partial def lowerTree {M : Type → Type} [Monad M] [MonadGraph M]
    (tree : DecisionTree)
    (lowerArm : ArmCallback M)
  (usageCounts : Std.HashMap Unique Nat)
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
      | .vType .zero => pure ()
      | ty => LowerT.cacheOccurrenceType binding.occurrence ty

    -- Resolve all bindings to (port, type) pairs
    let resolvedBindings ← bindings.mapM fun binding => do
      let (port, ty) ← resolveOccurrence binding.occurrence
      -- The resolved type should now be accurate thanks to pre-caching
      pure (binding.id, binding.name, port, ty)

    let stBefore ← LowerT.getState
    let mut unconsumedPorts : Array PortId := #[]
    for column in [:stBefore.scrutinees.size] do
      let rootOcc : Occurrence := ⟨column, #[]⟩
      match stBefore.occurrenceCache.get? rootOcc with
      | some _ => pure ()
      | none =>
        let scrutPort := stBefore.scrutinees[column]!
        unconsumedPorts := unconsumedPorts.push scrutPort
        LowerT.cacheOccurrence rootOcc scrutPort unitTy

    -- Compute ownership budgets per binding, duplication stays lazy in caller lowering
    let finalBindings ← resolvedBindings.foldlM (init := #[]) fun acc (id, name, port, ty) =>
      let count := usageCounts.getD id 1
      if count == 0 then do
        let era ← LowerT.addEra
        LowerT.connect (PortId.principal era) port
        pure acc
      else do
        pure (acc.push (id, name, port, count, ty))

    -- Call the arm body lowering callback (lifted to LowerT)
    let armPort ← StateT.lift (lowerArm armIndex ⟨finalBindings⟩)

    let resultTy ← LowerT.getResultType
    let mut currentPort := armPort
    for scrutPort in unconsumedPorts do
      let useNode ← LowerT.addUse resultTy
      LowerT.connect ⟨useNode, ⟨1⟩⟩ scrutPort
      LowerT.connect ⟨useNode, ⟨2⟩⟩ currentPort
      currentPort := PortId.principal useNode
    pure currentPort

  | .switch occurrence kind cases default =>
    let (scrutPort, scrutTy) ← resolveOccurrence occurrence

    match kind with
    | .constructor =>
      lowerConstructorSwitch scrutPort scrutTy cases default lowerArm usageCounts
    | .literal lits =>
      lowerLiteralSwitch scrutPort scrutTy lits cases default lowerArm usageCounts

/-- Lower a constructor switch (chain of MAT nodes) -/
partial def lowerConstructorSwitch {M : Type → Type} [Monad M] [MonadGraph M]
    (scrutPort : PortId)
    (scrutTy : Value)
    (cases : Array (Nat × DecisionTree))
    (default : Option DecisionTree)
    (lowerArm : ArmCallback M)
  (usageCounts : Std.HashMap Unique Nat)
    : LowerT M PortId := do
  if cases.isEmpty then
    match default with
    | some d => lowerTree d lowerArm usageCounts
    | none =>
      let era ← LowerT.addEra
      LowerT.connect (PortId.principal era) scrutPort
      pure (PortId.principal era)
  else
    lowerMATChain scrutPort scrutTy cases.toList default lowerArm usageCounts

/-- Lower a literal switch using MAT nodes -/
partial def lowerLiteralSwitch {M : Type → Type} [Monad M] [MonadGraph M]
    (scrutPort : PortId)
  (scrutTy : Value)
    (lits : Array Literal)
    (cases : Array (Nat × DecisionTree))
    (default : Option DecisionTree)
    (lowerArm : ArmCallback M)
  (usageCounts : Std.HashMap Unique Nat)
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
    lowerMATChain scrutPort scrutTy litCases.toList default lowerArm usageCounts
where
  literalToTag : Literal → Nat
    | .int n => n.toNat
    | .float f => f.toBits.toNat
    | .string s => s.hash.toNat

/-- Build a chain of MAT nodes -/
partial def lowerMATChain {M : Type → Type} [Monad M] [MonadGraph M]
    (scrutPort : PortId)
    (scrutTy : Value)
    (cases : List (Nat × DecisionTree))
    (default : Option DecisionTree)
    (lowerArm : ArmCallback M)
  (usageCounts : Std.HashMap Unique Nat)
    : LowerT M PortId := do
  let resultTy ← LowerT.getResultType

  let rec lowerWithPorts (ports : List PortId) (work : List (Nat × DecisionTree))
      : LowerT M PortId := do
    match work, ports with
    | [], _ =>
      match default with
      | some d => lowerTree d lowerArm usageCounts
      | none =>
        let era ← LowerT.addEra
        LowerT.connect (PortId.principal era) scrutPort
        pure (PortId.principal era)

    | [(tag, subtree)], [currentScrut] =>
      match default with
      | some d =>
        let hitPort ← lowerTree subtree lowerArm usageCounts
        let missPort ← lowerTree d lowerArm usageCounts
        let mat ← LowerT.addMat tag resultTy
        LowerT.connect ⟨mat, ⟨1⟩⟩ currentScrut
        LowerT.connect ⟨mat, ⟨2⟩⟩ hitPort
        LowerT.connect ⟨mat, ⟨3⟩⟩ missPort
        pure (PortId.principal mat)
      | none =>
        let era ← LowerT.addEra
        LowerT.connect (PortId.principal era) currentScrut
        lowerTree subtree lowerArm usageCounts

    | (tag, subtree) :: rest, currentScrut :: restScruts =>
      let hitPort ← lowerTree subtree lowerArm usageCounts
      let missPort ← lowerWithPorts restScruts rest

      let mat ← LowerT.addMat tag resultTy
      LowerT.connect ⟨mat, ⟨1⟩⟩ currentScrut
      LowerT.connect ⟨mat, ⟨2⟩⟩ hitPort
      LowerT.connect ⟨mat, ⟨3⟩⟩ missPort
      pure (PortId.principal mat)

    | _, _ =>
      panic! s!"lowerMATChain: internal arity mismatch (cases={work.length}, ports={ports.length})"

  match cases with
  | [] =>
    match default with
    | some d => lowerTree d lowerArm usageCounts
    | none =>
      let era ← LowerT.addEra
      LowerT.connect (PortId.principal era) scrutPort
      pure (PortId.principal era)
  | _ =>
    let caseCount := cases.length
    let scrutPorts ←
      if caseCount == 1 then
        pure #[scrutPort]
      else
        buildDupChain scrutPort caseCount scrutTy
    lowerWithPorts scrutPorts.toList cases

end

/-- Lower a compiled decision tree to Circuit IR with type tracking. -/
def lower {M : Type → Type} [Monad M] [MonadGraph M]
    (tree : DecisionTree)
    (scrutinees : Array PortId)
    (scrutineeTypes : Array Value)
    (registry : ConstructorTypeRegistry)
    (resultType : Value)
    (lowerArm : ArmCallback M)
    (usageCounts : Std.HashMap Unique Nat := {})
    : M PortId := do
  let (result, _) ← LowerT.run
    (lowerTree tree lowerArm usageCounts)
    scrutinees scrutineeTypes registry resultType
  pure result

/-- Full compilation and lowering from case arms. -/
def compileAndLower {M : Type → Type} [Monad M] [MonadGraph M]
    (ctx : SimplifyCtx)
    (registry : ConstructorTypeRegistry)
  (arms : Array Soma.Core.Arm)
    (scrutinees : Array PortId)
    (scrutineeTypes : Array Value)
    (resultType : Value)
    (lowerArm : ArmCallback M)
    (usageCounts : Std.HashMap Unique Nat := {})
    : M PortId := do
  let matrix := buildMatrixFromArms ctx arms
  let tree := compileMatrix matrix registry scrutineeTypes
  lower tree scrutinees scrutineeTypes registry resultType lowerArm usageCounts

end Somac.Circuit.PatternMatch
