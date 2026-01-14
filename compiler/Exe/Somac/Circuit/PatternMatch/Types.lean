import Soma.Core.Value
import Soma.Core.TypeId
import Std.Data.HashMap

namespace Somac.Circuit.PatternMatch

open Soma.Core (Value Closure TypeId)

/-- Key for looking up constructor field types: (TypeId, constructor tag) -/
structure ConstructorKey where
  typeId : TypeId
  tag : Nat
  deriving BEq, Hashable, Repr, Inhabited

/-- Information about a constructor's field types -/
structure ConstructorTypeInfo where
  /-- Number of type parameters the parent data type takes -/
  numTypeParams : Nat
  /-- Number of fields this constructor has -/
  arity : Nat
  /-- Field types. For parametric types, these may reference the type parameters -/
  fieldTypes : Array Value
  /-- The result type (the data type applied to parameters) -/
  resultType : Value
  deriving Inhabited

/-- Registry mapping constructor keys to their type information -/
abbrev ConstructorTypeRegistry := Std.HashMap ConstructorKey ConstructorTypeInfo

namespace ConstructorTypeRegistry

def empty : ConstructorTypeRegistry := {}

/-- Register a constructor's type information -/
def register (reg : ConstructorTypeRegistry) (typeId : TypeId) (tag : Nat)
    (info : ConstructorTypeInfo) : ConstructorTypeRegistry :=
  reg.insert ⟨typeId, tag⟩ info

/-- Look up constructor type info -/
def lookup (reg : ConstructorTypeRegistry) (typeId : TypeId) (tag : Nat)
    : Option ConstructorTypeInfo :=
  reg.get? ⟨typeId, tag⟩

/-- Extract field types from an elaborated constructor type. -/
def extractFieldTypes (ctorType : Value) : Array Value × Value :=
  go ctorType #[]
where
  go (ty : Value) (acc : Array Value) : Array Value × Value :=
    match ty with
    | .vPi _qty binder _name dom cod =>
      if binder.isImplicit then
        -- Skip implicit parameters
        match cod with
        | .const _ nextTy => go nextTy acc
        | .term _ _ _ => (acc, ty)
      else
        -- Explicit parameter = constructor field
        match cod with
        | .const _ nextTy => go nextTy (acc.push dom)
        | .term _ _ _ => (acc.push dom, ty)
    | resultTy => (acc, resultTy)

/-- Build constructor type info from an elaborated constructor type -/
def fromElaboratedType (ctorType : Value) : ConstructorTypeInfo :=
  let (fieldTypes, resultType) := extractFieldTypes ctorType
  -- Count implicit Pi binders to get numTypeParams
  let numTypeParams := countImplicits ctorType
  { numTypeParams, arity := fieldTypes.size, fieldTypes, resultType }
where
  countImplicits : Value → Nat
    | .vPi _qty binder _name _dom cod =>
      if binder.isImplicit then
        match cod with
        | .const _ nextTy => 1 + countImplicits nextTy
        | .term _ _ _ => 1
      else 0
    | _ => 0

end ConstructorTypeRegistry

mutual

/-- Substitute type parameters in a Value -/
partial def substituteParams (v : Value) (params : Array Value)
    (parentTypeId : TypeId) : Value :=
  match v with
  | .vNeutral _ (.nVar bv) =>
    -- Variable at level i → params[i] if in range
    let idx := bv.level.lvl
    params[idx]?.getD v

  | .vDataType typeId innerParams =>
    -- Recursively substitute in data type parameters
    let newParams := innerParams.map (substituteParams · params parentTypeId)
    .vDataType typeId newParams

  | .vPi qty binder name dom cod =>
    let newDom := substituteParams dom params parentTypeId
    -- For codomain, we can only substitute in const closures
    let newCod := match cod with
      | .const n result =>
        .const n (substituteParams result params parentTypeId)
      | other => other
    .vPi qty binder name newDom newCod

  | .vSigma qty name fst snd =>
    let newFst := substituteParams fst params parentTypeId
    let newSnd := match snd with
      | .const n result =>
        .const n (substituteParams result params parentTypeId)
      | other => other
    .vSigma qty name newFst newSnd

  | .vRecord row =>
    .vRecord (substituteParamsInRow row params parentTypeId)

  | .vVariant row =>
    .vVariant (substituteParamsInRow row params parentTypeId)

  | .vRowExtend label fieldTy tail =>
    let newFieldTy := substituteParams fieldTy params parentTypeId
    let newTail := substituteParams tail params parentTypeId
    .vRowExtend label newFieldTy newTail

  | other => other

/-- Substitute type parameters in a row type -/
partial def substituteParamsInRow (row : Value) (params : Array Value)
    (parentTypeId : TypeId) : Value :=
  match row with
  | .vRowExtend label fieldTy tail =>
    let newFieldTy := substituteParams fieldTy params parentTypeId
    let newTail := substituteParamsInRow tail params parentTypeId
    .vRowExtend label newFieldTy newTail
  | other => substituteParams other params parentTypeId

end

/-- Extract field types from a record row type -/
def extractRowFieldTypes (row : Value) (arity : Nat) : Array Value :=
  go row arity #[]
where
  go (r : Value) (remaining : Nat) (acc : Array Value) : Array Value :=
    if remaining == 0 then acc
    else match r with
    | .vRowExtend _ fieldTy tail =>
      go tail (remaining - 1) (acc.push fieldTy)
    | _ =>
      -- Pad with unit if row is shorter than expected
      acc ++ Array.mk (List.replicate remaining (.vPrimTy .unit))

/-- Fallback heuristic for field types when constructor info is unavailable -/
def fallbackFieldTypes (scrutineeType : Value) (arity : Nat) : Array Value :=
  match scrutineeType with
  | .vDataType _ params =>
    -- Common pattern: first field is first param, rest are the same data type
    if arity == 0 then #[]
    else if arity == 1 then
      #[params.head?.getD (.vPrimTy .unit)]
    else
      -- For arity > 1, use first param then repeat scrutinee type
      let firstField := params.head?.getD (.vPrimTy .unit)
      #[firstField] ++ Array.mk (List.replicate (arity - 1) scrutineeType)
  | _ =>
    Array.mk (List.replicate arity (.vPrimTy .unit))

/-- Instantiate field types by substituting type parameters -/
def instantiateFieldTypes (fieldTypes : Array Value) (params : Array Value)
    (parentTypeId : TypeId) : Array Value :=
  fieldTypes.map (substituteParams · params parentTypeId)

/-- Compute field types for a constructor match -/
def computeFieldTypes (registry : ConstructorTypeRegistry) (scrutineeType : Value)
    (tag : Nat) (arity : Nat) : Array Value :=
  match scrutineeType with
  | .vDataType typeId params =>
    match registry.lookup typeId tag with
    | some info =>
      -- Instantiate field types by substituting type parameters
      instantiateFieldTypes info.fieldTypes params.toArray typeId
    | none =>
      -- Constructor not in registry, fall back to heuristic
      fallbackFieldTypes scrutineeType arity

  | .vSigma _qty _name fst snd =>
    -- Sigma types: field 0 is fst, field 1 is snd (evaluated)
    if arity == 2 then
      let sndTy := match snd with
        | .const _ v => v
        | .term _ _ _ => .vPrimTy .unit -- Can't evaluate without argument
      #[fst, sndTy]
    else if arity == 1 then
      #[fst]
    else
      Array.mk (List.replicate arity (.vPrimTy .unit))

  | .vRecord row =>
    -- Record types: extract field types from row
    extractRowFieldTypes row arity

  | _ =>
    -- Unknown type, use unit placeholder
    Array.mk (List.replicate arity (.vPrimTy .unit))

/-- Type context for pattern match compilation -/
structure TypeContext where
  /-- Registry for looking up constructor field types -/
  registry : ConstructorTypeRegistry
  /-- Types of each column in the current matrix -/
  columnTypes : Array Value
  deriving Inhabited

namespace TypeContext

def empty : TypeContext := { registry := {}, columnTypes := #[] }

/-- Create a type context with initial scrutinee types -/
def initial (registry : ConstructorTypeRegistry) (scrutineeTypes : Array Value)
    : TypeContext :=
  { registry, columnTypes := scrutineeTypes }

/-- Get the type at a specific column -/
def getColumnType (ctx : TypeContext) (col : Nat) : Value :=
  ctx.columnTypes[col]?.getD (.vPrimTy .unit)

/-- Specialize the type context when matching a constructor -/
def specialize (ctx : TypeContext) (col : Nat) (tag : Nat) (arity : Nat)
    : TypeContext :=
  let colType := ctx.getColumnType col
  let fieldTypes := computeFieldTypes ctx.registry colType tag arity
  let before := ctx.columnTypes.extract 0 col
  let after := ctx.columnTypes.extract (col + 1) ctx.columnTypes.size
  { ctx with columnTypes := before ++ fieldTypes ++ after }

/-- Remove a column (for literal specialization) -/
def removeColumn (ctx : TypeContext) (col : Nat) : TypeContext :=
  let before := ctx.columnTypes.extract 0 col
  let after := ctx.columnTypes.extract (col + 1) ctx.columnTypes.size
  { ctx with columnTypes := before ++ after }

end TypeContext

end Somac.Circuit.PatternMatch
