import Soma.Circuit.PatternMatch.Pattern
import Soma.Circuit.PatternMatch.Matrix
import Soma.Circuit.PatternMatch.Decision
import Soma.Circuit.PatternMatch.Compile
import Soma.Circuit.Graph
import Soma.Circuit.Node
import Soma.Metal.Expr
import Std.Data.HashMap

namespace Soma.Circuit.PatternMatch

open Soma.Circuit.Graph (Graph GraphM)
open Soma.Circuit.Node (Node NodeId PortId PortIdx Label)
open Soma.Metal (BindingId Literal)

/-- State for lowering -/
structure LowerState where
  /-- Maps occurrences to their corresponding ports -/
  occurrenceCache : Std.HashMap Occurrence PortId := {}
  /-- The original scrutinee ports (one per column) -/
  scrutinees : Array PortId := #[]
  deriving Inhabited

/-! ## Lowering Monad

    We use the same monad structure as Circuit.Lower for compatibility.
-/

/-- Lowering monad - wraps GraphM with context -/
abbrev LowerM := StateT LowerState GraphM

namespace LowerM

/-- Run the lowering monad -/
def run (m : LowerM α) (scrutinees : Array PortId) : GraphM (α × LowerState) :=
  StateT.run m { scrutinees := scrutinees }

/-- Lift a GraphM action -/
def liftGraph (m : GraphM α) : LowerM α :=
  StateT.lift m

/-- Add a node to the graph -/
def addNode (n : Node) : LowerM NodeId :=
  liftGraph (GraphM.addNode n)

/-- Connect two ports -/
def connect (p1 p2 : PortId) : LowerM Unit :=
  liftGraph (GraphM.connect p1 p2)

/-- Get a fresh DUP label -/
def freshLabel : LowerM Label :=
  liftGraph GraphM.freshLabel

/-- Get n fresh labels -/
def freshLabels (n : Nat) : LowerM (Array Label) :=
  liftGraph (GraphM.freshLabels n)

/-- Get the state -/
def getState : LowerM LowerState := get

/-- Modify the state -/
def modifyState (f : LowerState → LowerState) : LowerM Unit := modify f

/-- Cache an occurrence → port mapping -/
def cacheOccurrence (occ : Occurrence) (port : PortId) : LowerM Unit :=
  modifyState fun s => { s with occurrenceCache := s.occurrenceCache.insert occ port }

/-- Look up a cached occurrence -/
def lookupOccurrence (occ : Occurrence) : LowerM (Option PortId) := do
  let s ← getState
  pure (s.occurrenceCache.get? occ)

end LowerM

/-! ## Occurrence Resolution

    Convert an Occurrence (path to a sub-value) into a Circuit port.
    This involves generating PROJ nodes for field access.
-/

/-- Resolve an occurrence to a port, generating PROJ nodes as needed.

    For a path like column=0, path=[1, 2], we:
    1. Start with scrutinee 0
    2. Generate PROJ 1 to get field 1
    3. Generate PROJ 2 to get field 2 of that
-/
partial def resolveOccurrence (occ : Occurrence) : LowerM PortId := do
  -- Check cache first
  match ← LowerM.lookupOccurrence occ with
  | some port => pure port
  | none =>
    let state ← LowerM.getState
    -- Get the root scrutinee
    let rootPort := state.scrutinees[occ.column]!
    -- Follow the path, generating PROJs
    let resultPort ← occ.path.foldlM (init := rootPort) fun currentPort fieldIdx => do
      let proj ← LowerM.addNode (.proj fieldIdx)
      LowerM.connect ⟨proj, ⟨1⟩⟩ currentPort  -- PROJ.aux0 = input
      pure (PortId.principal proj)
    -- Cache the result
    LowerM.cacheOccurrence occ resultPort
    pure resultPort

/-! ## DUP Chain Building

    Build a chain of DUP nodes for multi-use variables.
-/

/-- Build a DUP chain for n uses of a value.

    Returns an array of n ports, one for each use.
    If n=0, connects an ERA and returns empty.
    If n=1, returns the source port directly.
-/
def buildDupChain (sourcePort : PortId) (n : Nat) : LowerM (Array PortId) := do
  if n == 0 then
    let era ← LowerM.addNode .era
    LowerM.connect (PortId.principal era) sourcePort
    pure #[]
  else if n == 1 then
    pure #[sourcePort]
  else
    let labels ← LowerM.freshLabels (n - 1)
    let mut usePorts : Array PortId := #[]
    let mut chainPort := sourcePort

    for i in [:n - 1] do
      let dup ← LowerM.addNode (.dup labels[i]!)
      LowerM.connect (PortId.principal dup) chainPort
      usePorts := usePorts.push ⟨dup, ⟨1⟩⟩  -- aux0 = first copy
      chainPort := ⟨dup, ⟨2⟩⟩               -- aux1 = chain continues

    usePorts := usePorts.push chainPort  -- last use from final aux1
    pure usePorts

/-! ## Decision Tree Lowering -/

/-- Context passed to arm body lowering.
    Each binding maps to an array of ports - one port per use of the variable.
    For single-use variables, the array has one element.
    For multi-use variables, the array contains ports from a DUP chain. -/
structure ArmContext where
  /-- Variable bindings: (id, name, ports).
      The ports array has one port per use of the variable. -/
  bindings : Array (BindingId × String × Array PortId)

/-- Type of callback for lowering arm bodies -/
abbrev ArmCallback := Nat → ArmContext → GraphM PortId

/-! ## Mutually Recursive Lowering Functions -/

mutual

/-- Lower a decision tree to Circuit IR.

    Parameters:
    - tree: The decision tree to lower
    - lowerArm: Callback to lower an arm body given its index and bindings
    - usageCounts: Maps BindingId to usage count (for DUP chains)

    Returns the port carrying the match result.
-/
partial def lowerTree
    (tree : DecisionTree)
    (lowerArm : ArmCallback)
    (usageCounts : Std.HashMap Nat Nat)
    : LowerM PortId := do
  match tree with
  | .fail =>
    -- Match failure - should be unreachable in exhaustive matches
    let era ← LowerM.addNode .era
    pure (PortId.principal era)

  | .leaf bindings armIndex =>
    -- Resolve all bindings to ports
    let resolvedBindings ← bindings.mapM fun binding => do
      let port ← resolveOccurrence binding.occurrence
      pure (binding.id, binding.name, port)

    -- Build DUP chains for multi-use bindings
    let finalBindings ← resolvedBindings.foldlM (init := #[]) fun acc (id, name, port) =>
      let count := usageCounts.getD id.id 1
      if count == 0 then do
        -- Erased binding: connect to ERA
        let era ← LowerM.addNode .era
        LowerM.connect (PortId.principal era) port
        pure acc
      else do
        -- Build DUP chain with exactly `count` ports
        let dupPorts ← buildDupChain port count
        pure (acc.push (id, name, dupPorts))

    -- Call the arm body lowering callback
    LowerM.liftGraph (lowerArm armIndex ⟨finalBindings⟩)

  | .switch occurrence kind cases default =>
    -- Resolve the scrutinee occurrence
    let scrutPort ← resolveOccurrence occurrence

    match kind with
    | .constructor =>
      -- Build a chain of MAT nodes for constructor matching
      lowerConstructorSwitch scrutPort cases default lowerArm usageCounts

    | .literal lits =>
      -- Literal matching: use literal values directly as discriminants
      -- Circuit IR MAT nodes work on numeric tags, so we convert literals to their values
      lowerLiteralSwitch scrutPort lits cases default lowerArm usageCounts

/-- Lower a constructor switch (chain of MAT nodes) -/
partial def lowerConstructorSwitch
    (scrutPort : PortId)
    (cases : Array (Nat × DecisionTree))
    (default : Option DecisionTree)
    (lowerArm : ArmCallback)
    (usageCounts : Std.HashMap Nat Nat)
    : LowerM PortId := do
  if cases.isEmpty then
    -- No cases - just use default or fail
    match default with
    | some d => lowerTree d lowerArm usageCounts
    | none =>
      let era ← LowerM.addNode .era
      LowerM.connect (PortId.principal era) scrutPort
      pure (PortId.principal era)
  else
    -- Build chain: MAT for first case, miss goes to rest
    lowerMATChain scrutPort cases.toList default lowerArm usageCounts

/-- Lower a literal switch using MAT nodes.
    Literals are converted to their numeric representation for matching. -/
partial def lowerLiteralSwitch
    (scrutPort : PortId)
    (lits : Array Literal)
    (cases : Array (Nat × DecisionTree))
    (default : Option DecisionTree)
    (lowerArm : ArmCallback)
    (usageCounts : Std.HashMap Nat Nat)
    : LowerM PortId := do
  if cases.isEmpty then
    match default with
    | some d => lowerTree d lowerArm usageCounts
    | none =>
      let era ← LowerM.addNode .era
      LowerM.connect (PortId.principal era) scrutPort
      pure (PortId.principal era)
  else
    -- Convert case indices to literal values for MAT matching
    let litCases := cases.filterMap fun (idx, tree) =>
      match lits[idx]? with
      | some lit => some (literalToTag lit, tree)
      | none => none
    lowerMATChain scrutPort litCases.toList default lowerArm usageCounts
where
  /-- Convert a literal to a numeric tag for MAT node matching -/
  literalToTag : Literal → Nat
    | .bool true => 1
    | .bool false => 0
    | .int n => n.toNat
    | .string s => s.hash.toNat

/-- Build a chain of MAT nodes -/
partial def lowerMATChain
    (scrutPort : PortId)
    (cases : List (Nat × DecisionTree))
    (default : Option DecisionTree)
    (lowerArm : ArmCallback)
    (usageCounts : Std.HashMap Nat Nat)
    : LowerM PortId := do
  match cases with
  | [] =>
    -- No more cases - use default or fail
    match default with
    | some d => lowerTree d lowerArm usageCounts
    | none =>
      let era ← LowerM.addNode .era
      LowerM.connect (PortId.principal era) scrutPort
      pure (PortId.principal era)

  | [(tag, subtree)] =>
    -- Last case
    let mat ← LowerM.addNode (.mat tag)
    LowerM.connect ⟨mat, ⟨1⟩⟩ scrutPort  -- aux0 = scrutinee

    -- Hit: lower the subtree
    let hitPort ← lowerTree subtree lowerArm usageCounts
    LowerM.connect ⟨mat, ⟨2⟩⟩ hitPort    -- aux1 = hit continuation

    -- Miss: default or fail
    let missPort ← match default with
      | some d => lowerTree d lowerArm usageCounts
      | none =>
        let era ← LowerM.addNode .era
        pure (PortId.principal era)
    LowerM.connect ⟨mat, ⟨3⟩⟩ missPort   -- aux2 = miss continuation

    pure (PortId.principal mat)

  | (tag, subtree) :: rest =>
    -- More cases follow
    let mat ← LowerM.addNode (.mat tag)
    LowerM.connect ⟨mat, ⟨1⟩⟩ scrutPort

    -- Hit: lower this subtree
    let hitPort ← lowerTree subtree lowerArm usageCounts
    LowerM.connect ⟨mat, ⟨2⟩⟩ hitPort

    -- Miss: continue to next MAT in chain
    -- The miss port becomes the scrutinee for the next MAT
    let missPort ← lowerMATChain ⟨mat, ⟨3⟩⟩ rest default lowerArm usageCounts
    LowerM.connect ⟨mat, ⟨3⟩⟩ missPort

    pure (PortId.principal mat)

end

/-! ## Public API -/

/-- Lower a compiled decision tree to Circuit IR.

    Parameters:
    - tree: The compiled decision tree
    - scrutinees: Ports for the original scrutinee expressions
    - lowerArm: Callback to lower arm bodies
    - usageCounts: Variable usage counts for DUP chain construction

    Returns the port carrying the match result.
-/
def lower
    (tree : DecisionTree)
    (scrutinees : Array PortId)
    (lowerArm : ArmCallback)
    (usageCounts : Std.HashMap Nat Nat := {})
    : GraphM PortId := do
  let (result, _) ← LowerM.run (lowerTree tree lowerArm usageCounts) scrutinees
  pure result

/-- Full compilation and lowering from Metal arms.

    This is the main entry point for pattern matching compilation.
-/
def compileAndLower
    (ctx : SimplifyCtx)
    (arms : Soma.Metal.ArmList α scope)
    (scrutinees : Array PortId)
    (lowerArm : ArmCallback)
    (usageCounts : Std.HashMap Nat Nat := {})
    : GraphM PortId := do
  let matrix := buildMatrixFromArmList ctx arms
  let tree := compileMatrix matrix
  lower tree scrutinees lowerArm usageCounts

end Soma.Circuit.PatternMatch
