import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Primitive
import Soma.Core.MetaId
import Soma.Core.Expr
import Kenosis

namespace Soma.Core

open Kenosis

mutual

/-- Values: normalized expressions -/
inductive Value where
  /-- Universe type: Type_l -/
  | vType (level : Level)

  /-- Dependent function type: (q x : A) -> B -/
  | vPi (qty : Quantity) (binder : BinderInfo) (name : String) (domain : Value) (codomain : Closure)

  /-- Lambda abstraction -/
  | vLam (name : String) (body : Closure)

  /-- Dependent pair type: (x : A) * B -/
  | vSigma (qty : Quantity) (name : String) (fst : Value) (snd : Closure)

  /-- Pair value -/
  | vPair (fst snd : Value)

  /-- Neutral term (stuck computation) -/
  | vNeutral (ty : Value) (neu : Neutral)

  /-- Primitive type (Int, Bool, etc.) -/
  | vPrimTy (p : PrimType)

  /-- Row sorts -/
  | vRowSort
  /-- Label sort -/
  | vLabelSort

  /-- Integer literal -/
  | vIntLit (n : Int)

  /-- Floating-point literal -/
  | vFloatLit (f : Float)

  /-- String literal -/
  | vStringLit (s : String)

  /-- Empty row -/
  | vRowEmpty

  /-- Row extension: { label : ty | tail } -/
  | vRowExtend (label : Value) (fieldTy : Value) (tail : Value)

  /-- Record type -/
  | vRecord (row : Value)

  /-- Variant type -/
  | vVariant (row : Value)

  /-- Label literal -/
  | vLabelLit (name : String)

  /-- Record value -/
  | vRecordVal (fields : List (String × Value))

  /-- User-defined data type applied to parameters -/
  | vDataType (id : Unique) (params : List Value)

  /-- Constructor application -/
  | vConstructor (name : QualifiedName) (tag : Nat) (args : List Value) (resultTy : Value)

  /-- Equality type: a = b -/
  | vEq (tyLevel : Level) (ty : Value) (lhs rhs : Value)

  /-- Reflexivity proof -/
  | vRefl (ty : Value) (x : Value)

  /-- Transport along equality: transporting a value from P x to P y via equality proof x = y -/
  | vTransport (tyLevel : Level) (ty : Value) (motive : Value) (lhs rhs : Value)
               (eq : Value) (body : Value)


/-- Closure: represents a function waiting for an argument.
    We support two representations:
    1. term: An Expr with its environment, for closures created during evaluation
    2. const: A constant Value, for non-dependent closures (like arrow type codomains)

    The const variant is for non-dependent types where the result doesn't depend on the argument. -/
inductive Closure where
  /-- Expr-based closure: evaluates body under extended environment -/
  | term (name : String) (env : Env) (body : Soma.Core.Expr) : Closure
  /-- Constant closure: always returns the same value (for non-dependent types) -/
  | const (name : String) (value : Value) : Closure

/-- Environment: mapping from De Bruijn levels to values -/
inductive Env where
  | mk (values : List (String × Value)) (size : Nat) : Env

/-- Neutral terms: terms that are stuck on a variable or metavariable -/
inductive Neutral where
  /-- Stuck on a bound variable -/
  | nVar (v : BoundVar)
  /-- Stuck on a metavariable -/
  | nMeta (id : MetaId)
  /-- Application of a neutral term -/
  | nApp (fn : Neutral) (arg : Value)
  /-- First projection of a neutral pair -/
  | nFst (pair : Neutral)
  /-- Second projection of a neutral pair -/
  | nSnd (pair : Neutral)
  /-- Field access on a neutral record -/
  | nFieldAccess (record : Neutral) (field : String)
  /-- Case analysis on a neutral scrutinee -/
  | nCase (scrutinee : Neutral) (arms : List ArmClosure) (resultTy : Value)
  /-- Stuck on an unresolved global constant (extern or opaque) -/
  | nConst (name : Soma.Core.QualifiedName) (constTy : Value)

/-- Case arm closure -/
inductive ArmClosure where
  | mk (pattern : String) (closure : Closure)
      (patterns : Array Soma.Core.Pattern := #[.wildcard]) : ArmClosure

end

deriving instance Serialize, Deserialize for Value
deriving instance Serialize, Deserialize for Closure
deriving instance Serialize, Deserialize for Env
deriving instance Serialize, Deserialize for Neutral
deriving instance Serialize, Deserialize for ArmClosure

namespace Closure

def name : Closure → String
  | .term n _ _ => n
  | .const n _ => n

def env : Closure → Env
  | .term _ e _ => e
  | .const _ _ => .mk [] 0

def body : Closure → Option Soma.Core.Expr
  | .term _ _ b => some b
  | .const _ _ => none

/-- Check if this is a constant (non-dependent) closure -/
def isConst : Closure → Bool
  | .const _ _ => true
  | .term _ _ _ => false

/-- Get the constant value if this is a const closure -/
def constValue? : Closure → Option Value
  | .const _ v => some v
  | .term _ _ _ => none

end Closure

namespace Env

def values : Env → List (String × Value)
  | .mk vs _ => vs

def size : Env → Nat
  | .mk _ s => s

end Env

namespace ArmClosure

def pattern : ArmClosure → String
  | .mk p _ _ => p

def closure : ArmClosure → Closure
  | .mk _ c _ => c

def patterns : ArmClosure → Array Soma.Core.Pattern
  | .mk _ _ ps => ps

end ArmClosure

mutual
  def Value.defaultValue : Value := Value.vType Level.zero
  def Closure.defaultValue : Closure := Closure.const "_" Value.defaultValue
  def Env.defaultValue : Env := Env.mk [] 0
  def Neutral.defaultValue : Neutral := Neutral.nVar ⟨"_", ⟨0⟩⟩
  def ArmClosure.defaultValue : ArmClosure := ArmClosure.mk "_" Closure.defaultValue #[.wildcard]
end

instance : Inhabited Value := ⟨Value.defaultValue⟩
instance : Inhabited Closure := ⟨Closure.defaultValue⟩
instance : Inhabited Env := ⟨Env.defaultValue⟩
instance : Inhabited Neutral := ⟨Neutral.defaultValue⟩
instance : Inhabited ArmClosure := ⟨ArmClosure.defaultValue⟩

def Env.empty : Env := Env.mk [] 0

def Env.extend (env : Env) (name : String) (v : Value) : Env :=
  Env.mk ((name, v) :: env.values) (env.size + 1)

def Env.lookup (env : Env) (lvl : DeBruijnLvl) : Option Value :=
  -- Level 0 is at the end of the list, level (size-1) is at the front
  -- Check if level is valid (must be < size)
  if lvl.lvl >= env.size then
    none
  else
    let idx := env.size - lvl.lvl - 1
    env.values[idx]? |>.map (·.2)

def Env.lookupByName (env : Env) (name : String) : Option Value :=
  env.values.find? (·.1 == name) |>.map (·.2)

/-- Current level (next variable will get this level) -/
def Env.level (env : Env) : DeBruijnLvl := ⟨env.size⟩

/-- Create a closure with no body (placeholder) -/
def Closure.mkEmpty (name : String) (env : Env) : Closure :=
  let clos : Closure := .term name env (.bvar 0)
  clos

/-- Create a closure with an Expr body -/
def Closure.mkWithBody (name : String) (env : Env) (body : Soma.Core.Expr) : Closure :=
  let clos : Closure := .term name env body
  clos

/-- Create a non-dependent function type: A -> B -/
def Value.arrow (a b : Value) : Value :=
  Value.vPi Quantity.omega BinderInfo.explicit "_" a (Closure.const "_" b)

/-- Build the kind of a type constructor with `arity` type parameters -/
def Value.typeConstructorKind (arity : Nat) : Value :=
  match arity with
  | 0 => Value.vType .zero
  | n + 1 => Value.arrow (Value.vType .zero) (typeConstructorKind n)

/-- Create Type₀ -/
def Value.type0 : Value := Value.vType Level.zero

/-- Create Type₁ -/
def Value.type1 : Value := Value.vType Level.one

/-- Check if value is a type (universe) -/
def Value.isType (v : Value) : Bool :=
  match v with
  | Value.vType _ => true
  | _ => false

/-- Check if value is a neutral term -/
def Value.isNeutral (v : Value) : Bool :=
  match v with
  | Value.vNeutral _ _ => true
  | _ => false

/-- Check if value is a pi type -/
def Value.isPi (v : Value) : Bool :=
  match v with
  | Value.vPi _ _ _ _ _ => true
  | _ => false

/-- Check if value is a sigma type -/
def Value.isSigma (v : Value) : Bool :=
  match v with
  | Value.vSigma _ _ _ _ => true
  | _ => false

/-- Extract the domain from a Pi type -/
def Value.piDomain? (v : Value) : Option Value :=
  match v with
  | Value.vPi _ _ _ domain _ => some domain
  | _ => none

/-- Extract the first component type from a Sigma type -/
def Value.sigmaFst? (v : Value) : Option Value :=
  match v with
  | Value.vSigma _ _ fst _ => some fst
  | _ => none

/-- Create a non-dependent Sigma (product) -/
def Value.prod (a b : Value) : Value :=
  Value.vSigma Quantity.omega "_" a (Closure.const "_" b)

/-- Build a tuple/product type from an array of types -/
def Value.tuple (types : Array Value) : Value :=
  if types.isEmpty then Value.vPrimTy .unit
  else if h : types.size = 1 then types[0]
  else
    -- Build right-nested sigma
    let rec go (i : Nat) : Value :=
      if i + 1 >= types.size then
        types[types.size - 1]!
      else
        Value.prod types[i]! (go (i + 1))
    go 0

/-- Extract field type from a record row type at a given index -/
partial def Value.rowFieldType (row : Value) (idx : Nat) : Option Value :=
  match row, idx with
  | .vRowExtend _ fieldTy _, 0 => some fieldTy
  | .vRowExtend _ _ tail, n + 1 => Value.rowFieldType tail n
  | _, _ => none

/-- Extract field type from a record type at a given index -/
def Value.recordFieldType (v : Value) (idx : Nat) : Option Value :=
  match v with
  | .vRecord row => Value.rowFieldType row idx
  | _ => none

/-- Collect all field names and types from a record row type -/
partial def Value.rowFields (row : Value) : Array (String × Value) :=
  match row with
  | .vRowExtend (.vLabelLit name) fieldTy tail =>
    #[(name, fieldTy)] ++ Value.rowFields tail
  | _ => #[]

/-- Collect all field names and types from a record type -/
def Value.recordFields (v : Value) : Array (String × Value) :=
  match v with
  | .vRecord row => Value.rowFields row
  | _ => #[]

/-- Look up a field index by name in a record type -/
def Value.recordFieldIndex (v : Value) (name : String) : Option Nat :=
  let fields := v.recordFields
  fields.findIdx? (·.1 == name) |>.map (·)

/-- Extract the first type parameter from a data type -/
def Value.dataTypeFirstParam? (v : Value) : Option Value :=
  match v with
  | .vDataType _ (first :: _) => some first
  | _ => none

/-- Extract the return type from a function type (Pi chain) -/
partial def Value.returnType? (v : Value) : Option Value :=
  match v with
  | .vPi _ _ _ _ cod =>
    match cod with
    | .const _ nextTy => Value.returnType? nextTy
    | .term _ _ _ => none -- Dependent return type
  | other => some other

/-- Extract parameter types from a function type (Pi chain) -/
partial def Value.paramTypes (v : Value) (acc : Array (String × Value) := #[]) : Array (String × Value) :=
  match v with
  | .vPi _ _ name dom cod =>
    match cod with
    | .const _ nextTy => Value.paramTypes nextTy (acc.push (name, dom))
    | .term _ _ _ => acc.push (name, dom) -- Stop at dependent type
  | _ => acc

/-- Get the arity of a function type (number of Pi binders) -/
partial def Value.arity (v : Value) : Nat :=
  match v with
  | .vPi _ _ _ _ cod =>
    match cod with
    | .const _ nextTy => 1 + Value.arity nextTy
    | .term _ _ _ => 1
  | _ => 0

/-- Get the number of explicit Pi binders -/
partial def Value.explicitArity (v : Value) : Nat :=
  match v with
  | .vPi _ binder _ _ cod =>
    let rest := match cod with
      | .const _ nextTy => Value.explicitArity nextTy
      | .term _ _ _ => 0
    if binder.isImplicit then rest else 1 + rest
  | _ => 0

/-! ## Neutral Operations -/

/-- Create a variable neutral -/
def Neutral.var (name : String) (lvl : DeBruijnLvl) : Neutral :=
  Neutral.nVar ⟨name, lvl⟩

/-- Create a metavariable neutral -/
def Neutral.mkMeta (id : Nat) : Neutral :=
  Neutral.nMeta ⟨id⟩

/-- Information about a metavariable -/
structure MetaInfo where
  /-- The type of the metavariable -/
  type : Value
  /-- The solution, if found -/
  solution : Option Value := none
  /-- The context in which it was created -/
  context : List (String × Value × Quantity)
  /-- Metavariables that this meta depends on (occurs in its type or solution) -/
  dependsOn : Array MetaId := #[]
  /-- Metavariables that depend on this meta (reverse of dependsOn) -/
  dependents : Array MetaId := #[]
  deriving Inhabited

/-- A constraint index for tracking which constraints involve which metas -/
structure ConstraintId where
  id : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

instance : ToString ConstraintId where
  toString c := s!"C{c.id}"

/-- Dependency tracking for metavariables.
    Tracks which metas occur in which constraints, enabling efficient "wake-up"
    when a meta is solved. -/
structure MetaDependencies where
  /-- Map from MetaId to constraint IDs that contain it -/
  metaToConstraints : Std.HashMap Nat (Array ConstraintId) := {}
  /-- Map from constraint ID to the metas it contains -/
  constraintToMetas : Std.HashMap Nat (Array MetaId) := {}
  /-- Next constraint ID -/
  nextConstraintId : Nat := 0
  deriving Inhabited

namespace MetaDependencies

def empty : MetaDependencies := {}

/-- Register a new constraint and return its ID -/
def registerConstraint (deps : MetaDependencies) (metas : Array MetaId)
    : ConstraintId × MetaDependencies :=
  let cid : ConstraintId := ⟨deps.nextConstraintId⟩
  -- Add constraint -> metas mapping
  let constraintToMetas := deps.constraintToMetas.insert cid.id metas
  -- Add metas -> constraint mapping for each meta
  let metaToConstraints := metas.foldl (fun acc mid =>
    let existing := acc.getD mid.id #[]
    acc.insert mid.id (existing.push cid)
  ) deps.metaToConstraints
  (cid, { deps with
    constraintToMetas := constraintToMetas
    metaToConstraints := metaToConstraints
    nextConstraintId := deps.nextConstraintId + 1
  })

/-- Get all constraints that involve a given meta -/
def getConstraintsFor (deps : MetaDependencies) (mid : MetaId) : Array ConstraintId :=
  deps.metaToConstraints.getD mid.id #[]

/-- Get all metas involved in a constraint -/
def getMetasFor (deps : MetaDependencies) (cid : ConstraintId) : Array MetaId :=
  deps.constraintToMetas.getD cid.id #[]

/-- Remove a constraint from tracking (after it's been solved) -/
def removeConstraint (deps : MetaDependencies) (cid : ConstraintId) : MetaDependencies :=
  -- Get the metas this constraint references
  let metas := deps.constraintToMetas.getD cid.id #[]
  -- Remove constraint from each meta's constraint list
  let metaToConstraints := metas.foldl (fun acc mid =>
    let existing := acc.getD mid.id #[]
    let filtered := existing.filter (· != cid)
    acc.insert mid.id filtered
  ) deps.metaToConstraints
  -- Remove the constraint entry
  let constraintToMetas := deps.constraintToMetas.erase cid.id
  { deps with
    metaToConstraints := metaToConstraints
    constraintToMetas := constraintToMetas
  }

/-- Check if any constraints reference a given meta -/
def hasConstraints (deps : MetaDependencies) (mid : MetaId) : Bool :=
  match deps.metaToConstraints.get? mid.id with
  | some arr => !arr.isEmpty
  | none => false

/-- Count how many metas a constraint depends on -/
def constraintComplexity (deps : MetaDependencies) (cid : ConstraintId) : Nat :=
  deps.constraintToMetas.getD cid.id #[] |>.size

end MetaDependencies

/-- State of all metavariables -/
structure MetaState where
  /-- Map from MetaId to info -/
  metas : Std.HashMap Nat MetaInfo := {}
  /-- Next fresh metavariable ID -/
  nextId : Nat := 0
  /-- Dependency tracking -/
  dependencies : MetaDependencies := {}
  deriving Inhabited

def MetaState.empty : MetaState := ⟨{}, 0, {}⟩

def MetaState.fresh (state : MetaState) (ty : Value) (ctx : List (String × Value × Quantity)) : MetaId × MetaState :=
  let id := state.nextId
  let info : MetaInfo := { type := ty, context := ctx }
  let metas := state.metas.insert id info
  (⟨id⟩, { state with metas := metas, nextId := id + 1 })

def MetaState.solve (state : MetaState) (id : MetaId) (v : Value) : MetaState :=
  match state.metas.get? id.id with
  | some info =>
    let info' : MetaInfo := { info with solution := some v }
    { state with metas := state.metas.insert id.id info' }
  | none => state

/-- Clear a metavariable's solution (make it unsolved again) -/
def MetaState.unsolve (state : MetaState) (id : MetaId) : MetaState :=
  match state.metas.get? id.id with
  | some info =>
    let info' : MetaInfo := { info with solution := none }
    { state with metas := state.metas.insert id.id info' }
  | none => state

def MetaState.lookup (state : MetaState) (id : MetaId) : Option MetaInfo :=
  state.metas.get? id.id

def MetaState.isSolved (state : MetaState) (id : MetaId) : Bool :=
  match state.metas.get? id.id with
  | some info => info.solution.isSome
  | none => false

/-- Register a constraint and the metas it references -/
def MetaState.registerConstraint (state : MetaState) (metas : Array MetaId)
    : ConstraintId × MetaState :=
  let (cid, deps') := state.dependencies.registerConstraint metas
  (cid, { state with dependencies := deps' })

/-- Get constraints affected by solving a meta -/
def MetaState.getAffectedConstraints (state : MetaState) (mid : MetaId) : Array ConstraintId :=
  state.dependencies.getConstraintsFor mid

/-- Remove a constraint after it's been solved -/
def MetaState.removeConstraint (state : MetaState) (cid : ConstraintId) : MetaState :=
  { state with dependencies := state.dependencies.removeConstraint cid }

/-- Get constraint complexity (number of metas) -/
def MetaState.constraintComplexity (state : MetaState) (cid : ConstraintId) : Nat :=
  state.dependencies.constraintComplexity cid

/-- Add a dependency: meta1 depends on meta2 -/
def MetaState.addDependency (state : MetaState) (meta1 meta2 : MetaId) : MetaState :=
  -- Update meta1's dependsOn
  let state' := match state.metas.get? meta1.id with
    | some info =>
      if info.dependsOn.contains meta2 then state
      else
        let info' := { info with dependsOn := info.dependsOn.push meta2 }
        { state with metas := state.metas.insert meta1.id info' }
    | none => state
  -- Update meta2's dependents
  match state'.metas.get? meta2.id with
  | some info =>
    if info.dependents.contains meta1 then state'
    else
      let info' := { info with dependents := info.dependents.push meta1 }
      { state' with metas := state'.metas.insert meta2.id info' }
  | none => state'

/-- Get all metas that depend on a given meta -/
def MetaState.getDependents (state : MetaState) (mid : MetaId) : Array MetaId :=
  match state.metas.get? mid.id with
  | some info => info.dependents
  | none => #[]

/-- Get all metas that a given meta depends on -/
def MetaState.getDependencies (state : MetaState) (mid : MetaId) : Array MetaId :=
  match state.metas.get? mid.id with
  | some info => info.dependsOn
  | none => #[]

end Soma.Core
