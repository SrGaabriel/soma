import Soma.Circuit.PatternMatch.Pattern
import Soma.Circuit.PatternMatch.Types
import Soma.Metal.Literal
import Soma.Core.Value

namespace Soma.Circuit.PatternMatch

open Soma.Metal (BindingId Literal)
open Soma.Core (Value)

/-- Path to a sub-value within a scrutinee.

    For example, if we match `(x, (y, z))` and want to access `z`:
    - column = 0 (first scrutinee)
    - path = [1, 1] (second element of outer tuple, second element of inner tuple)
-/
structure Occurrence where
  /-- Which original scrutinee (0-indexed) -/
  column : Nat
  /-- Path of field indices to reach the sub-value -/
  path : Array Nat
  deriving Repr, Inhabited, BEq, Hashable

namespace Occurrence

/-- The root occurrence for a given column -/
def root (col : Nat) : Occurrence :=
  ⟨col, #[]⟩

/-- Extend an occurrence by accessing a field -/
def field (occ : Occurrence) (idx : Nat) : Occurrence :=
  ⟨occ.column, occ.path.push idx⟩

/-- Check if this occurrence is a root (no field path) -/
def isRoot (occ : Occurrence) : Bool :=
  occ.path.isEmpty

/-- Pretty print an occurrence -/
def format (occ : Occurrence) : String :=
  if occ.path.isEmpty then
    s!"${occ.column}"
  else
    let pathStr := ".".intercalate (occ.path.toList.map toString)
    s!"${occ.column}.{pathStr}"

instance : ToString Occurrence := ⟨format⟩

end Occurrence

/-- An occurrence with its associated type -/
structure TypedOccurrence where
  /-- Where the value comes from -/
  occurrence : Occurrence
  /-- The type of the value at this occurrence -/
  ty : Value
  deriving Inhabited

namespace TypedOccurrence

def root (col : Nat) (ty : Value) : TypedOccurrence :=
  ⟨Occurrence.root col, ty⟩

def field (tocc : TypedOccurrence) (idx : Nat) (fieldTy : Value) : TypedOccurrence :=
  ⟨tocc.occurrence.field idx, fieldTy⟩

end TypedOccurrence

/-- A variable binding at a decision tree leaf -/
structure Binding where
  /-- The binding ID from the source pattern -/
  id : BindingId
  /-- The original variable name -/
  name : String
  /-- Where to get the value from -/
  occurrence : Occurrence
  /-- The type of the bound variable -/
  ty : Value
  deriving Inhabited

namespace Binding

def format (b : Binding) : String :=
  s!"{b.name} = {b.occurrence}"

instance : ToString Binding := ⟨format⟩

end Binding

/-! ## Decision Tree -/

/-- What to test at a switch node -/
inductive TestKind where
  /-- Test constructor tag -/
  | constructor
  /-- Test literal value -/
  | literal (values : Array Literal)
  deriving Repr, Inhabited, BEq

/-- A decision tree for pattern matching.

    The tree is built by the compilation algorithm and later
    lowered to Circuit IR.
-/
inductive DecisionTree where
  /-- Successful match: bind variables and execute arm body -/
  | leaf (bindings : Array Binding) (armIndex : Nat)
  /-- Match failure (should be unreachable for exhaustive patterns) -/
  | fail
  /-- Test a value and branch based on result -/
  | switch
      (occurrence : Occurrence)
      (kind : TestKind)
      (cases : Array (Nat × DecisionTree))  -- tag/lit-index → subtree
      (default : Option DecisionTree)       -- fallback for unmatched
  deriving Inhabited

namespace DecisionTree

/-- Check if this tree is a leaf -/
def isLeaf : DecisionTree → Bool
  | .leaf _ _ => true
  | _ => false

/-- Check if this tree is a failure -/
def isFail : DecisionTree → Bool
  | .fail => true
  | _ => false

/-- Get the arm index if this is a leaf -/
def getArmIndex? : DecisionTree → Option Nat
  | .leaf _ idx => some idx
  | _ => none

/-- Count the total number of nodes in the tree -/
partial def nodeCount : DecisionTree → Nat
  | .leaf _ _ => 1
  | .fail => 1
  | .switch _ _ cases default =>
    let caseCounts := cases.foldl (fun acc (_, t) => acc + t.nodeCount) 0
    let defaultCount := default.map nodeCount |>.getD 0
    1 + caseCounts + defaultCount

/-- Compute the maximum depth of the tree -/
partial def maxDepth : DecisionTree → Nat
  | .leaf _ _ => 1
  | .fail => 1
  | .switch _ _ cases default =>
    let caseDepths := cases.map (fun (_, t) => t.maxDepth)
    let maxCase := caseDepths.foldl max 0
    let defaultDepth := default.map maxDepth |>.getD 0
    1 + max maxCase defaultDepth

/-- Collect all arm indices reachable from this tree -/
partial def reachableArms : DecisionTree → Array Nat
  | .leaf _ idx => #[idx]
  | .fail => #[]
  | .switch _ _ cases default =>
    let fromCases := cases.foldl (fun acc (_, t) => acc ++ t.reachableArms) #[]
    let fromDefault := default.map reachableArms |>.getD #[]
    -- Deduplicate
    (fromCases ++ fromDefault).foldl (init := #[]) fun acc idx =>
      if acc.contains idx then acc else acc.push idx

/-! ## Pretty Printing -/

/-- Format a decision tree with indentation -/
partial def format (tree : DecisionTree) (indent : Nat := 0) : String :=
  let pad := String.ofList (List.replicate (indent * 2) ' ')
  match tree with
  | .leaf bindings armIndex =>
    let bindingsStr := if bindings.isEmpty then ""
      else s!" [{", ".intercalate (bindings.toList.map Binding.format)}]"
    s!"{pad}→ arm {armIndex}{bindingsStr}"
  | .fail =>
    s!"{pad}→ FAIL"
  | .switch occ kind cases default =>
    let kindStr := match kind with
      | .constructor => "tag"
      | .literal lits => s!"lit({lits.size})"
    let header := s!"{pad}switch {occ} ({kindStr})"
    let caseStrs := cases.toList.map fun (tag, subtree) =>
      s!"{pad}  case {tag}:\n{format subtree (indent + 2)}"
    let defaultStr := match default with
      | some d => s!"\n{pad}  default:\n{format d (indent + 2)}"
      | none => ""
    s!"{header}\n{"\n".intercalate caseStrs}{defaultStr}"

instance : ToString DecisionTree := ⟨fun t => format t 0⟩

end DecisionTree

/-- Maps matrix column indices to occurrences.

    This map tracks both where each column's value comes from AND its type.
-/
structure TypedOccurrenceMap where
  /-- Typed occurrence for each current column -/
  columns : Array TypedOccurrence
  /-- Constructor type registry for field type lookup -/
  registry : ConstructorTypeRegistry
  deriving Inhabited

namespace TypedOccurrenceMap

/-- Create initial map for n scrutinees with their types -/
def initial (registry : ConstructorTypeRegistry) (scrutineeTypes : Array Value)
    : TypedOccurrenceMap :=
  let columns := scrutineeTypes.mapIdx fun i ty =>
    TypedOccurrence.root i ty
  ⟨columns, registry⟩

/-- Get the typed occurrence for a column -/
def get (m : TypedOccurrenceMap) (col : Nat) : Option TypedOccurrence :=
  m.columns[col]?

/-- Get typed occurrence, panicking if out of bounds -/
def get! (m : TypedOccurrenceMap) (col : Nat) : TypedOccurrence :=
  m.columns[col]!

/-- Get just the occurrence (without type) for a column -/
def getOccurrence (m : TypedOccurrenceMap) (col : Nat) : Option Occurrence :=
  m.columns[col]?.map (·.occurrence)

/-- Get occurrence, panicking if out of bounds -/
def getOccurrence! (m : TypedOccurrenceMap) (col : Nat) : Occurrence :=
  m.columns[col]!.occurrence

/-- Get the type at a column -/
def getType (m : TypedOccurrenceMap) (col : Nat) : Value :=
  m.columns[col]?.map (·.ty) |>.getD (.vPrimTy .unit)

/-- Specialize the map for constructor match at `col` with `arity` fields.

    The column at `col` is replaced by `arity` new columns for the
    constructor's fields with types computed from the constructor info.
-/
def specialize (m : TypedOccurrenceMap) (col : Nat) (tag : Nat) (arity : Nat)
    : TypedOccurrenceMap :=
  match m.columns[col]? with
  | none => m
  | some tocc =>
    let before := m.columns.extract 0 col
    let after := m.columns.extract (col + 1) m.columns.size

    -- Compute field types using the registry and scrutinee type
    let fieldTypes := computeFieldTypes m.registry tocc.ty tag arity

    -- Create typed occurrences for each field
    let fieldToccs := Array.range arity |>.map fun i =>
      let fieldTy := fieldTypes[i]?.getD (.vPrimTy .unit)
      TypedOccurrence.field tocc i fieldTy

    ⟨before ++ fieldToccs ++ after, m.registry⟩

/-- Remove a column (for literal specialization where no sub-patterns exist) -/
def removeColumn (m : TypedOccurrenceMap) (col : Nat) : TypedOccurrenceMap :=
  let before := m.columns.extract 0 col
  let after := m.columns.extract (col + 1) m.columns.size
  ⟨before ++ after, m.registry⟩

/-- Get the number of columns -/
def size (m : TypedOccurrenceMap) : Nat := m.columns.size

end TypedOccurrenceMap

end Soma.Circuit.PatternMatch
