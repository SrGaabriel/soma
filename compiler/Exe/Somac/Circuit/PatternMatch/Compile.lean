import Somac.Circuit.PatternMatch.Pattern
import Somac.Circuit.PatternMatch.Matrix
import Somac.Circuit.PatternMatch.Decision
import Somac.Circuit.PatternMatch.Types
import Soma.Core.Value

namespace Somac.Circuit.PatternMatch

open Soma.Core (Value)

/-- Heuristic scores for column selection (higher = better) -/
structure ColumnScore where
  /-- Column index -/
  column : Nat
  /-- Does the first row have a constructor here? (necessity heuristic) -/
  necessary : Bool
  /-- Number of distinct constructors/literals -/
  diversity : Nat
  /-- Number of rows with constructors (more = earlier discrimination) -/
  constructorCount : Nat
  deriving Repr, Inhabited

namespace ColumnScore

/-- Compare two scores: true if `a` is strictly better than `b` -/
def isBetterThan (a b : ColumnScore) : Bool :=
  -- Priority 1: Necessity (first row must be matched)
  if a.necessary && !b.necessary then true
  else if !a.necessary && b.necessary then false
  -- Priority 2: More constructors = better discrimination
  else if a.constructorCount > b.constructorCount then true
  else if a.constructorCount < b.constructorCount then false
  -- Priority 3: Higher diversity = smaller branching factor per case
  else if a.diversity > b.diversity then true
  else if a.diversity < b.diversity then false
  -- Priority 4: Left-to-right (smaller column index)
  else a.column < b.column

end ColumnScore

/-- Score a single column -/
def scoreColumn (m : PatternMatrix) (col : Nat) : ColumnScore :=
  let firstRowNecessary := match m.firstRow with
    | some row => match row.patterns[col]? with
      | some p => p.isConstraining
      | none => false
    | none => false

  let ctorTags := m.getConstructorTags col
  let litValues := m.getLiteralValues col
  let diversity := ctorTags.size + litValues.size

  let constructorCount := m.rows.foldl (init := 0) fun count row =>
    match row.patterns[col]? with
    | some p => if p.isConstraining then count + 1 else count
    | none => count

  ⟨col, firstRowNecessary, diversity, constructorCount⟩

/-- Select the best column to split on -/
def selectColumn (m : PatternMatrix) : Nat :=
  if m.numColumns == 0 then 0
  else
    let scores := Array.range m.numColumns |>.map (scoreColumn m)
    let best := scores.foldl (init := scores[0]!) fun best score =>
      if score.isBetterThan best then score else best
    best.column

/-! ## Binding Resolution

    Convert row bindings (which use column indices) to tree bindings
    (which use occurrences).
-/

/-- Convert a row's bindings to decision tree bindings.
    This includes both accumulated bindings from specialization
    and bindings from variable patterns still in the row. -/
def resolveBindings (row : Row) (toccMap : TypedOccurrenceMap) : Array Binding :=
  -- First, collect accumulated bindings from specialization
  let accumulated := row.bindings.filterMap fun (id, name, col) =>
    toccMap.get col |>.map fun tocc => ⟨id, name, tocc.occurrence, tocc.ty⟩

  -- Then collect bindings from remaining variable patterns
  let fromPatterns := collectPatternBindings row.patterns toccMap 0 #[]

  accumulated ++ fromPatterns
where
  collectPatternBindings (patterns : Array SimplePattern) (toccMap : TypedOccurrenceMap)
      (col : Nat) (acc : Array Binding) : Array Binding :=
    if col >= patterns.size then acc
    else
      let pat := patterns[col]!
      let acc' := match toccMap.get col with
        | none => acc
        | some tocc =>
          let patBindings := pat.collectBindings
          patBindings.foldl (init := acc) fun a (id, name) =>
            a.push ⟨id, name, tocc.occurrence, tocc.ty⟩
      collectPatternBindings patterns toccMap (col + 1) acc'

/-! ## Core Compilation Algorithm -/

/-- Compilation state -/
structure CompileState where
  /-- Fuel to prevent infinite loops (defensive) -/
  fuel : Nat
  deriving Inhabited

/-- Compile a pattern matrix to a decision tree with type tracking.

    This is the main entry point for the Maranget algorithm.
-/
partial def compileTyped (matrix : PatternMatrix) (toccMap : TypedOccurrenceMap)
    : DecisionTree :=
  compileAux matrix toccMap { fuel := 10000 }
where
  compileAux (m : PatternMatrix) (toccMap : TypedOccurrenceMap) (state : CompileState)
      : DecisionTree :=
    -- Defensive fuel check
    if state.fuel == 0 then
      .fail
    else
      let state' := { state with fuel := state.fuel - 1 }

      -- Base case 1: Empty matrix = match failure
      if m.isEmpty then
        .fail

      -- Base case 2: First row is all wildcards/vars = match success
      else if m.firstRowAllWildcards then
        match m.firstRow with
        | some row =>
          let bindings := resolveBindings row toccMap
          .leaf bindings row.armIndex
        | none => .fail

      -- Base case 3: No columns left but we have rows
      -- This means all patterns matched; take first row
      else if m.numColumns == 0 then
        match m.firstRow with
        | some row => .leaf (resolveBindings row toccMap) row.armIndex
        | none => .fail

      -- Recursive case: split on best column
      else
        let col := selectColumn m
        let occ := toccMap.getOccurrence! col

        -- Check what kind of patterns are in this column
        let ctorTags := m.getConstructorTags col
        let litValues := m.getLiteralValues col

        if !ctorTags.isEmpty then
          -- Constructor patterns: build switch on constructor tag
          let cases := ctorTags.map fun (tag, arity) =>
            let specialized := m.specialize col tag arity
            let newToccMap := toccMap.specialize col tag arity
            let subtree := compileAux specialized newToccMap state'
            (tag, subtree)

          -- Default case: rows with wildcards at this column
          let defaultMatrix := m.default col
          let default := if defaultMatrix.isEmpty then none
            else
              let newToccMap := toccMap.removeColumn col
              some (compileAux defaultMatrix newToccMap state')

          .switch occ .constructor cases default

        else if !litValues.isEmpty then
          -- Literal patterns: build switch on literal value
          let cases := litValues.mapIdx fun idx lit =>
            let specialized := m.specializeLit col lit
            let newToccMap := toccMap.removeColumn col
            let subtree := compileAux specialized newToccMap state'
            (idx, subtree)

          -- Default for non-matched literals
          let defaultMatrix := m.default col
          let default := if defaultMatrix.isEmpty then none
            else
              let newToccMap := toccMap.removeColumn col
              some (compileAux defaultMatrix newToccMap state')

          .switch occ (.literal litValues) cases default

        else
          -- All wildcards in this column - just remove it and continue
          let defaultMatrix := m.default col
          let newToccMap := toccMap.removeColumn col
          compileAux defaultMatrix newToccMap state'

/-- Compile a pattern matrix to a decision tree with type tracking -/
def compileMatrix (matrix : PatternMatrix) (registry : ConstructorTypeRegistry)
    (scrutineeTypes : Array Value) : DecisionTree :=
  let toccMap := TypedOccurrenceMap.initial registry scrutineeTypes
  compileTyped matrix toccMap

/-- Compile match arms to a decision tree with type tracking -/
def compileArms (ctx : SimplifyCtx) (registry : ConstructorTypeRegistry)
    (scrutineeTypes : Array Value) (arms : Soma.Metal.ArmList α scope)
    : DecisionTree :=
  let matrix := buildMatrixFromArmList ctx arms
  compileMatrix matrix registry scrutineeTypes

end Somac.Circuit.PatternMatch
