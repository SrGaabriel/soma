import Somac.Circuit.PatternMatch.Pattern
import Soma.Core.Expr
import Soma.Core.Literal

namespace Somac.Circuit.PatternMatch

open Soma.Core (Arm)
open Soma (Unique)

/-- A row in the pattern matrix.

    Each row corresponds to one arm of the original match expression.
    As the matrix is specialized during compilation, bindings accumulate
    and patterns are replaced with their sub-patterns.
-/
structure Row where
  /-- Patterns for each column (one per scrutinee) -/
  patterns : Array SimplePattern
  /-- Variable bindings accumulated during specialization.
      Each entry is (binding id, variable name, column index where bound).
      The column index indicates which scrutinee the variable is bound to. -/
  bindings : Array (Unique × String × Nat)
  /-- Index of the original arm (for selecting the right body) -/
  armIndex : Nat
  deriving Repr, Inhabited

namespace Row

/-- Create a row from an array of patterns -/
def ofPatterns (patterns : Array SimplePattern) (armIndex : Nat) : Row :=
  ⟨patterns, #[], armIndex⟩

/-- Check if all patterns in this row are wildcards or variables -/
def allWildcards (row : Row) : Bool :=
  row.patterns.all SimplePattern.isWildcardOrVar

/-- Get the pattern at a specific column -/
def getPattern (row : Row) (col : Nat) : Option SimplePattern :=
  row.patterns[col]?

/-- Check if the pattern at column `col` is a constructor with tag `tag` -/
def matchesTag (row : Row) (col : Nat) (tag : Nat) : Bool :=
  match row.patterns[col]? with
  | some p => p.getCtorTag? == some tag
  | none => false

/-- Check if the pattern at column `col` is a wildcard/var (matches any tag) -/
def isWildcardAt (row : Row) (col : Nat) : Bool :=
  match row.patterns[col]? with
  | some p => p.isWildcardOrVar
  | none => false

/-- Add a binding to the row -/
def addBinding (row : Row) (binding : Unique) (name : String) (col : Nat) : Row :=
  { row with bindings := row.bindings.push (binding, name, col) }

/-- Add multiple bindings -/
def addBindings (row : Row) (newBindings : Array (Unique × String × Nat)) : Row :=
  { row with bindings := row.bindings ++ newBindings }

/-- Collect bindings from a pattern at a given column and add them to the row -/
def collectBindingsFromPattern (row : Row) (col : Nat) : Row :=
  match row.patterns[col]? with
  | some p =>
    let patBindings := p.collectBindings
    let withCol := patBindings.map fun (b, n) => (b, n, col)
    row.addBindings withCol
  | none => row

end Row

/-- The pattern matrix for Maranget's algorithm.

    Invariant: All rows have the same number of columns (= numColumns).
-/
structure PatternMatrix where
  /-- The rows of the matrix -/
  rows : Array Row
  /-- Number of columns (scrutinees) -/
  numColumns : Nat
  deriving Repr, Inhabited

namespace PatternMatrix

/-- Create an empty matrix with a given number of columns -/
def empty (numColumns : Nat) : PatternMatrix :=
  ⟨#[], numColumns⟩

/-- Check if the matrix has no rows -/
def isEmpty (m : PatternMatrix) : Bool :=
  m.rows.isEmpty

/-- Get the number of rows -/
def numRows (m : PatternMatrix) : Nat :=
  m.rows.size

/-- Get a specific row -/
def getRow (m : PatternMatrix) (idx : Nat) : Option Row :=
  m.rows[idx]?

/-- Get the first row (if any) -/
def firstRow (m : PatternMatrix) : Option Row :=
  m.rows[0]?

/-- Add a row to the matrix -/
def addRow (m : PatternMatrix) (row : Row) : PatternMatrix :=
  { m with rows := m.rows.push row }

/-- Check if the first row is all wildcards (match found) -/
def firstRowAllWildcards (m : PatternMatrix) : Bool :=
  match m.firstRow with
  | some row => row.allWildcards
  | none => false

/-- Get all distinct constructor tags appearing in a column -/
def getConstructorTags (m : PatternMatrix) (col : Nat) : Array (Nat × Nat) :=
  let tagsWithArity := m.rows.filterMap fun row =>
    match row.patterns[col]? with
    | some p =>
      match p.getCtorTag?, p.getCtorArity? with
      | some tag, some arity => some (tag, arity)
      | _, _ => none
    | none => none
  -- Deduplicate while preserving order
  tagsWithArity.foldl (init := #[]) fun acc (tag, arity) =>
    if acc.any (fun (t, _) => t == tag) then acc
    else acc.push (tag, arity)

/-- Get all distinct literal values appearing in a column -/
def getLiteralValues (m : PatternMatrix) (col : Nat) : Array Soma.Core.Literal :=
  let lits := m.rows.filterMap fun row =>
    match row.patterns[col]? with
    | some p => p.getLit?
    | none => none
  -- Deduplicate
  lits.foldl (init := #[]) fun acc lit =>
    if acc.any (· == lit) then acc
    else acc.push lit

/-- Check if a column has any constructor patterns -/
def hasConstructorAt (m : PatternMatrix) (col : Nat) : Bool :=
  m.rows.any fun row =>
    match row.patterns[col]? with
    | some p => p.stripAs.getCtorTag?.isSome
    | none => false

/-- Check if a column has any literal patterns -/
def hasLiteralAt (m : PatternMatrix) (col : Nat) : Bool :=
  m.rows.any fun row =>
    match row.patterns[col]? with
    | some p => p.stripAs.getLit?.isSome
    | none => false

/-- Check if a column has only wildcards/variables -/
def allWildcardsAt (m : PatternMatrix) (col : Nat) : Bool :=
  m.rows.all fun row => row.isWildcardAt col

end PatternMatrix

/-- Strip as-patterns and collect their bindings with their column index -/
def collectAsBindings (p : SimplePattern) (col : Nat)
    : SimplePattern × Array (Unique × String × Nat) :=
  match p with
  | .as binding name inner =>
    let (inner', bindings) := collectAsBindings inner col
    (inner', #[(binding, name, col)] ++ bindings)
  | other => (other, #[])

/-! ## Matrix Specialization

    Specialization is the key operation in Maranget's algorithm.
    Given a column and a constructor tag, we produce a new matrix
    containing only rows that could match that constructor.
-/

/-- Specialize a single row for a constructor match at column `col`.

    If the row has a matching constructor pattern:
    - Replace the pattern at `col` with the constructor's sub-patterns
    - Return the specialized row

    If the row has a wildcard/variable pattern:
    - Replace with `arity` wildcards
    - Collect any variable bindings
    - Return the specialized row

    If the row has a non-matching constructor:
    - Return none (row is filtered out)
-/
def specializeRow (row : Row) (col : Nat) (tag : Nat) (arity : Nat)
    : Option Row :=
  match row.patterns[col]? with
  | none => none
  | some pat =>
    let (innerPat, outerBindings) := collectAsBindings pat col
    match innerPat with
    | .ctor ptag _ args =>
      if ptag == tag then
        -- Matching constructor: splice in the sub-patterns
        let before := row.patterns.extract 0 col
        let after := row.patterns.extract (col + 1) row.patterns.size
        let newPatterns := before ++ args ++ after
        let newRow := { row with patterns := newPatterns }
        some (newRow.addBindings outerBindings)
      else
        -- Non-matching constructor: filter out this row
        none
    | .wildcard =>
      -- Wildcard: replace with `arity` wildcards
      let wildcards := Array.mk (List.replicate arity SimplePattern.wildcard)
      let before := row.patterns.extract 0 col
      let after := row.patterns.extract (col + 1) row.patterns.size
      let newPatterns := before ++ wildcards ++ after
      let newRow := { row with patterns := newPatterns }
      some (newRow.addBindings outerBindings)
    | .var binding name =>
      -- Variable: replace with `arity` wildcards, record binding
      let wildcards := Array.mk (List.replicate arity SimplePattern.wildcard)
      let before := row.patterns.extract 0 col
      let after := row.patterns.extract (col + 1) row.patterns.size
      let newPatterns := before ++ wildcards ++ after
      let newRow := { row with patterns := newPatterns }
      let withBinding := newRow.addBinding binding name col
      some (withBinding.addBindings outerBindings)
    | .lit _ =>
      -- Literal pattern in a constructor specialization: filter out
      none
    | .as _ _ _ =>
      -- Should have been handled by collectAsBindings
      none

/-- Specialize the entire matrix for constructor `tag` at column `col`.

    The resulting matrix has `arity` more columns (the constructor's
    sub-patterns are spliced in place of the constructor pattern).
-/
def PatternMatrix.specialize (m : PatternMatrix) (col : Nat) (tag : Nat) (arity : Nat)
    : PatternMatrix :=
  let newRows := m.rows.filterMap fun row => specializeRow row col tag arity
  -- New column count: original - 1 (removed col) + arity (added sub-patterns)
  let newNumCols := m.numColumns - 1 + arity
  ⟨newRows, newNumCols⟩

/-- Specialize a row for a literal match at column `col`. -/
def specializeRowLit (row : Row) (col : Nat) (lit : Soma.Core.Literal)
    : Option Row :=
  match row.patterns[col]? with
  | none => none
  | some pat =>
    let (innerPat, outerBindings) := collectAsBindings pat col
    match innerPat with
    | .lit plit =>
      if plit == lit then
        -- Matching literal: just remove the column
        let before := row.patterns.extract 0 col
        let after := row.patterns.extract (col + 1) row.patterns.size
        let newPatterns := before ++ after
        let newRow := { row with patterns := newPatterns }
        some (newRow.addBindings outerBindings)
      else
        none
    | .wildcard =>
      -- Wildcard: matches any literal
      let before := row.patterns.extract 0 col
      let after := row.patterns.extract (col + 1) row.patterns.size
      let newPatterns := before ++ after
      let newRow := { row with patterns := newPatterns }
      some (newRow.addBindings outerBindings)
    | .var binding name =>
      -- Variable: matches and binds
      let before := row.patterns.extract 0 col
      let after := row.patterns.extract (col + 1) row.patterns.size
      let newPatterns := before ++ after
      let newRow := { row with patterns := newPatterns }
      let withBinding := newRow.addBinding binding name col
      some (withBinding.addBindings outerBindings)
    | .ctor _ _ _ =>
      -- Constructor in literal column: filter out
      none
    | .as _ _ _ =>
      none

/-- Specialize matrix for a literal match -/
def PatternMatrix.specializeLit (m : PatternMatrix) (col : Nat) (lit : Soma.Core.Literal)
    : PatternMatrix :=
  let newRows := m.rows.filterMap fun row => specializeRowLit row col lit
  ⟨newRows, m.numColumns - 1⟩

/-! ## Default Matrix

    The default matrix contains rows that would match if the scrutinee
    has a constructor tag not explicitly matched by any pattern.
    This is used for wildcard/variable patterns and incomplete matches.
-/

/-- Compute the default row for column `col`.

    If the pattern is a wildcard/variable, the row is included with
    that column removed. Otherwise the row is excluded.
-/
def defaultRow (row : Row) (col : Nat) : Option Row :=
  match row.patterns[col]? with
  | none => none
  | some pat =>
    let (innerPat, outerBindings) := collectAsBindings pat col
    match innerPat with
    | .wildcard =>
      let before := row.patterns.extract 0 col
      let after := row.patterns.extract (col + 1) row.patterns.size
      let newPatterns := before ++ after
      let newRow := { row with patterns := newPatterns }
      some (newRow.addBindings outerBindings)
    | .var binding name =>
      let before := row.patterns.extract 0 col
      let after := row.patterns.extract (col + 1) row.patterns.size
      let newPatterns := before ++ after
      let newRow := { row with patterns := newPatterns }
      let withBinding := newRow.addBinding binding name col
      some (withBinding.addBindings outerBindings)
    | .ctor _ _ _ =>
      -- Constructor pattern: not in default matrix
      none
    | .lit _ =>
      -- Literal pattern: not in default matrix
      none
    | .as _ _ _ =>
      none

/-- Compute the default matrix for column `col`.

    Contains all rows that have wildcard/variable patterns at `col`.
-/
def PatternMatrix.default (m : PatternMatrix) (col : Nat) : PatternMatrix :=
  let newRows := m.rows.filterMap fun row => defaultRow row col
  ⟨newRows, m.numColumns - 1⟩

/-! ## Building the Matrix from Core IR -/

/-- Build a pattern matrix from Core case arms. -/
def buildMatrixFromArms (ctx : SimplifyCtx) (arms : Array Soma.Core.Arm)
    : PatternMatrix :=
  let rows := arms.mapIdx fun idx arm =>
    let simplified := arm.patterns.map (simplifyPattern ctx)
    Row.ofPatterns simplified idx
  let numCols := match rows[0]? with
    | some r => r.patterns.size
    | none => 0
  ⟨rows, numCols⟩

end Somac.Circuit.PatternMatch
