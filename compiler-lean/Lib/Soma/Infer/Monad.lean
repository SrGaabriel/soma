/-
  Inference Monad

  A monad that combines:
  - State for fresh variable generation and current substitution
  - Error accumulation for collecting multiple type errors
  - Reader for the type environment and instance environment

  Key improvements over the old Haskell design:
  1. Cleaner separation of concerns (no entangled resolver logic)
  2. Proper error accumulation without stopping on first error
  3. Efficient fresh variable generation using Nat counter
-/

import Std.Data.HashMap
import Soma.Infer.Constraint
import Soma.Infer.Instance
import Soma.Infer.Entailment
import Soma.Metal

namespace Soma.Infer

open Std
open Soma.Typing hiding Constraint
open Soma.Syntax hiding Constraint
open Soma.Metal (BindingId Name)

-- Use Typing.Constraint for type-level constraints
abbrev Constraint := Soma.Typing.Constraint

/-- Information about a bound variable in scope -/
structure VarInfo where
  /-- The type of the variable -/
  ty : MonoTy
  /-- The binding ID for scope tracking -/
  bindingId : BindingId
  /-- Original name for error messages -/
  name : String

/-- Information about a global function -/
structure FunctionInfo where
  /-- The qualified type of the function -/
  qualType : QualifiedType
  /-- The Metal IR name -/
  metalName : Metal.Name

/-- Information about a type constructor -/
structure TypeInfo where
  /-- The type ID -/
  typeId : TypeId
  /-- Type parameters -/
  params : Array TyVarId
  /-- Constructors (name → field types) -/
  constructors : HashMap String (Array MonoTy)
  deriving Inhabited

/-- Information about a data constructor -/
structure ConstructorInfo where
  /-- The type this constructor belongs to -/
  typeName : String
  /-- The type ID -/
  typeId : TypeId
  /-- Type parameters of the parent type -/
  typeParams : Array TyVarId
  /-- Field types (may reference type params) -/
  fieldTypes : Array MonoTy
  /-- Constructor tag (for runtime) -/
  tag : Nat

/-- The type environment -/
structure TypeEnv where
  /-- Local variables in scope (by name) -/
  locals : HashMap String VarInfo
  /-- Global functions -/
  functions : HashMap String FunctionInfo
  /-- Type definitions -/
  types : HashMap String TypeInfo
  /-- Data constructors -/
  constructors : HashMap String ConstructorInfo
  deriving Inhabited

namespace TypeEnv

def empty : TypeEnv :=
  { locals := {}
  , functions := {}
  , types := {}
  , constructors := {}
  }

/-- Add a local variable -/
def addLocal (env : TypeEnv) (name : String) (info : VarInfo) : TypeEnv :=
  { env with locals := env.locals.insert name info }

/-- Remove a local variable -/
def removeLocal (env : TypeEnv) (name : String) : TypeEnv :=
  { env with locals := env.locals.erase name }

/-- Look up a local variable -/
def lookupLocal (env : TypeEnv) (name : String) : Option VarInfo :=
  env.locals.get? name

/-- Look up a function -/
def lookupFunction (env : TypeEnv) (name : String) : Option FunctionInfo :=
  env.functions.get? name

/-- Look up a type -/
def lookupType (env : TypeEnv) (name : String) : Option TypeInfo :=
  env.types.get? name

/-- Look up a constructor -/
def lookupConstructor (env : TypeEnv) (name : String) : Option ConstructorInfo :=
  env.constructors.get? name

/-- Add a function -/
def addFunction (env : TypeEnv) (name : String) (info : FunctionInfo) : TypeEnv :=
  { env with functions := env.functions.insert name info }

/-- Add a type -/
def addType (env : TypeEnv) (name : String) (info : TypeInfo) : TypeEnv :=
  { env with types := env.types.insert name info }

/-- Add a constructor -/
def addConstructor (env : TypeEnv) (name : String) (info : ConstructorInfo) : TypeEnv :=
  { env with constructors := env.constructors.insert name info }

end TypeEnv

/-- Mutable state for type inference -/
structure InferState where
  /-- Counter for fresh type variables -/
  freshCounter : Nat
  /-- Current substitution (accumulated during solving) -/
  subst : Subst
  /-- Constraint graph being built -/
  constraints : ConstraintGraph
  /-- Accumulated errors -/
  errors : Array InferError
  deriving Inhabited

namespace InferState

def initial : InferState :=
  { freshCounter := 0
  , subst := Subst.empty
  , constraints := ConstraintGraph.empty
  , errors := #[]
  }

end InferState

/-- Read-only context for type inference -/
structure InferContext where
  /-- Type environment -/
  typeEnv : TypeEnv
  /-- Instance environment -/
  instanceEnv : InstanceEnv
  /-- Current function name (for error messages) -/
  currentFunction : Option String
  deriving Inhabited

namespace InferContext

def empty : InferContext :=
  { typeEnv := TypeEnv.empty
  , instanceEnv := InstanceEnv.empty
  , currentFunction := none
  }

def withFunction (ctx : InferContext) (name : String) : InferContext :=
  { ctx with currentFunction := some name }

end InferContext

/-- The inference monad: ReaderT + StateT + error accumulation -/
abbrev InferM := ReaderT InferContext (StateM InferState)

namespace InferM

/-- Run the inference monad -/
def run (m : InferM α) (ctx : InferContext) (state : InferState := InferState.initial)
    : α × InferState :=
  StateT.run (ReaderT.run m ctx) state

/-- Run and extract just the result (discarding state) -/
def run' (m : InferM α) (ctx : InferContext) : α :=
  (m.run ctx).1

/-- Run and get the final state -/
def runState (m : InferM α) (ctx : InferContext) : InferState :=
  (m.run ctx).2

/-- Get the type environment -/
def getTypeEnv : InferM TypeEnv := do
  return (← read).typeEnv

/-- Get the instance environment -/
def getInstanceEnv : InferM InstanceEnv := do
  return (← read).instanceEnv

/-- Run with a modified type environment -/
def withTypeEnv (f : TypeEnv → TypeEnv) (m : InferM α) : InferM α := do
  ReaderT.adapt (fun c => { c with typeEnv := f c.typeEnv }) m

/-- Add a local variable to scope for the duration of a computation -/
def withLocal (name : String) (info : VarInfo) (m : InferM α) : InferM α :=
  withTypeEnv (·.addLocal name info) m

/-- Add multiple locals -/
def withLocals (bindings : Array (String × VarInfo)) (m : InferM α) : InferM α :=
  bindings.foldl (init := m) fun acc (name, info) => withLocal name info acc

/-- Generate a fresh type variable -/
def freshTyVar (name : String := "t") (kind : Kind := .star) : InferM TyVarId := do
  let s ← get
  let id := s.freshCounter
  set { s with freshCounter := id + 1 }
  return ⟨s!"{name}{id}", id, kind⟩

/-- Generate a fresh monomorphic type variable -/
def freshVar (name : String := "t") : InferM MonoTy := do
  let v ← freshTyVar name
  return .var v

/-- Get the current substitution -/
def getSubst : InferM Subst := do
  return (← get).subst

/-- Update the substitution -/
def modifySubst (f : Subst → Subst) : InferM Unit := do
  modify fun s => { s with subst := f s.subst }

/-- Extend the current substitution -/
def extendSubst (σ : Subst) : InferM Unit := do
  modifySubst (σ.compose ·)

/-- Apply current substitution to a type -/
def applySubst (ty : MonoTy) : InferM MonoTy := do
  let σ ← getSubst
  return σ.apply ty

/-- Add an equality constraint -/
def addEqualityConstraint (lhs rhs : MonoTy) (purpose : UnifyPurpose)
    (lhsSpan rhsSpan : Span) : InferM Unit := do
  modify fun s => { s with
    constraints := s.constraints.addEquality lhs rhs purpose lhsSpan rhsSpan
  }

/-- Add a class constraint -/
def addClassConstraint (className : TyCon) (args : Array MonoTy) (span : Span) : InferM Unit := do
  modify fun s => { s with
    constraints := s.constraints.addClass className args span
  }

/-- Add a Constraint -/
def addConstraint (c : Constraint) (span : Span) : InferM Unit := do
  addClassConstraint c.className c.args span

/-- Report an error -/
def reportError (err : InferError) : InferM Unit := do
  modify fun s => { s with errors := s.errors.push err }

/-- Report multiple errors -/
def reportErrors (errs : Array InferError) : InferM Unit := do
  modify fun s => { s with errors := s.errors ++ errs }

/-- Check if there are any errors -/
def hasErrors : InferM Bool := do
  return !(← get).errors.isEmpty

/-- Get all accumulated errors -/
def getErrors : InferM (Array InferError) := do
  return (← get).errors

/-- Get the constraint graph -/
def getConstraints : InferM ConstraintGraph := do
  return (← get).constraints

/-- Look up a local variable -/
def lookupLocal (name : String) : InferM (Option VarInfo) := do
  return (← getTypeEnv).lookupLocal name

/-- Look up a function -/
def lookupFunction (name : String) : InferM (Option FunctionInfo) := do
  return (← getTypeEnv).lookupFunction name

/-- Look up a type -/
def lookupType (name : String) : InferM (Option TypeInfo) := do
  return (← getTypeEnv).lookupType name

/-- Look up a constructor -/
def lookupConstructor (name : String) : InferM (Option ConstructorInfo) := do
  return (← getTypeEnv).lookupConstructor name

/-- Instantiate a qualified type with fresh type variables -/
def instantiate (qt : QualifiedType) : InferM (MonoTy × Array Constraint) := do
  if qt.vars.isEmpty then
    return (qt.body, qt.constraints)

  -- Generate fresh variables for each quantified variable
  let freshVars ← qt.vars.mapM fun v => do
    let fresh ← freshTyVar v.name v.kind
    return (v.id, Ty.var fresh)

  -- Build substitution
  let σ := Subst.fromArrays
    (qt.vars)
    (freshVars.map fun (_, ty) => ty)

  -- Apply to body and constraints
  let body := σ.apply qt.body
  let constraints := qt.constraints.map fun c =>
    { c with args := c.args.map (σ.apply ·) }

  return (body, constraints)

/-- Generalize a type by quantifying over free variables -/
def generalize (ty : MonoTy) (constraints : Array Constraint) : InferM QualifiedType := do
  let σ ← getSubst

  -- Apply substitution to both the type and constraints
  let ty := σ.apply ty
  let constraints := constraints.map fun c =>
    { c with args := c.args.map (σ.apply ·) }

  -- Get free variables in the substituted type
  let tyVars := ty.freeVarsUnique

  -- Get free variables in the environment (these should NOT be quantified)
  -- Also apply current substitution to environment types before extracting free vars
  let env ← getTypeEnv
  let envVars := env.locals.fold (init := ({} : Std.HashSet Nat)) fun acc _ info =>
    let substTy := σ.apply info.ty
    substTy.freeVars.foldl (init := acc) fun acc v => acc.insert v.id

  -- Quantify over variables that are free in ty but not in env
  let quantified := tyVars.filter fun v => !envVars.contains v.id

  -- Filter constraints to only those mentioning quantified variables
  let relevantConstraints := constraints.filter fun c =>
    c.args.any fun arg => arg.freeVars.any fun v => quantified.any (·.id == v.id)

  return {
    vars := quantified
    constraints := relevantConstraints
    body := ty
  }

end InferM

end Soma.Infer
