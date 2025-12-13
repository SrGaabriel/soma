import Std.Data.HashMap
import Soma.Infer.Substitution
import Soma.Infer.Unify

namespace Soma.Infer

open Std
open Soma.Typing
open Soma.Syntax

/-- An instance declaration: instance (constraints) => Class args -/
structure InstanceDecl where
  /-- The class this is an instance for -/
  className : TyCon
  /-- Type arguments to the class -/
  args : Array MonoTy
  /-- Type variables quantified over -/
  typeVars : Array TyVarId
  /-- Constraints required by this instance -/
  constraints : Array Constraint
  /-- Unique identifier -/
  id : Nat
  /-- Source span for error reporting -/
  span : Span

namespace InstanceDecl

/-- Create an instance from a QualifiedType representing the instance head -/
def fromQualifiedType (className : TyCon) (qt : QualifiedType) (id : Nat) (span : Span)
    : Option InstanceDecl :=
  -- TODO: not assume the body directly represents the instance args
  some {
    className
    args := #[qt.body] -- todo: review
    typeVars := qt.vars
    constraints := qt.constraints
    id
    span
  }

/-- Get the qualified type this instance provides -/
def toQualifiedType (inst : InstanceDecl) : QualifiedType :=
  { vars := inst.typeVars
  , constraints := inst.constraints
  , body := if h : inst.args.size > 0 then inst.args[0] else .starPrim .unit
  }

/-- Freshen the type variables in this instance with new IDs -/
def freshen (inst : InstanceDecl) (startId : Nat) : InstanceDecl × Nat :=
  let numVars := inst.typeVars.size
  -- Create fresh variables
  let freshVars := inst.typeVars.mapIdx fun i v =>
    { v with id := startId + i }
  -- Build substitution from old to new
  let σ := Subst.fromArrays inst.typeVars (freshVars.map fun v => .var v)
  let freshArgs := inst.args.map (σ.apply ·)
  let freshConstraints := inst.constraints.map fun c =>
    { c with args := c.args.map (σ.apply ·) }
  ({ inst with
     typeVars := freshVars
     args := freshArgs
     constraints := freshConstraints
   }, startId + numVars)

end InstanceDecl

/-- A type class declaration with its superclasses -/
structure TypeClassDecl where
  /-- The class name -/
  name : TyCon
  /-- Type parameters -/
  params : Array TyVarId
  /-- Superclass constraints (Eq for Ord for exemple) -/
  superclasses : Array Constraint
  /-- Source span -/
  span : Span

/-- The instance environment tracks all available instances -/
structure InstanceEnv where
  /-- All instance declarations, indexed by class name -/
  instances : HashMap String (Array InstanceDecl)
  /-- Type class declarations, indexed by name -/
  classes : HashMap String TypeClassDecl
  /-- Next instance ID -/
  nextId : Nat
  deriving Inhabited

namespace InstanceEnv

/-- Create an empty instance environment -/
def empty : InstanceEnv :=
  { instances := {}
  , classes := {}
  , nextId := 0
  }

/-- Add an instance declaration -/
def addInstance (env : InstanceEnv) (inst : InstanceDecl) : InstanceEnv :=
  let key := inst.className.name
  let existing := env.instances.getD key #[]
  { env with
    instances := env.instances.insert key (existing.push { inst with id := env.nextId })
    nextId := env.nextId + 1
  }

/-- Add a type class declaration -/
def addClass (env : InstanceEnv) (cls : TypeClassDecl) : InstanceEnv :=
  { env with classes := env.classes.insert cls.name.name cls }

/-- Look up all instances for a class -/
def getInstances (env : InstanceEnv) (className : TyCon) : Array InstanceDecl :=
  env.instances.getD className.name #[]

/-- Look up a type class declaration -/
def getClass (env : InstanceEnv) (className : TyCon) : Option TypeClassDecl :=
  env.classes.get? className.name

/-- Check if a class exists -/
def hasClass (env : InstanceEnv) (className : TyCon) : Bool :=
  env.classes.contains className.name

/-- Get superclasses for a class -/
def getSuperclasses (env : InstanceEnv) (className : TyCon) : Array Constraint :=
  match env.getClass className with
  | some cls => cls.superclasses
  | none => #[]

/-- Helper to unify instance args with constraint args -/
private def tryUnifyArgs (instArgs constArgs : Array MonoTy) : Option Subst :=
  if instArgs.size != constArgs.size then none
  else go 0 Subst.empty
where
  go (i : Nat) (σ : Subst) : Option Subst :=
    if i >= instArgs.size then
      some σ
    else
      match instArgs[i]?, constArgs[i]? with
      | some instArg, some constArg =>
        let ctx : UnifyContext := {
          purpose := .general
          expectedSpan := Span.uninhabited
          actualSpan := Span.uninhabited
        }
        match Unify.unifyMono (σ.apply instArg) (σ.apply constArg) ctx with
        | .ok σ' => go (i + 1) (σ'.compose σ)
        | .error _ => none
      | _, _ => none
  termination_by instArgs.size - i

/-- Try to find an instance matching a constraint. -/
def findInstance (env : InstanceEnv) (constraint : Constraint) (freshIdStart : Nat)
    : Option (InstanceDecl × Subst × Array Constraint × Nat) :=
  let instances := env.getInstances constraint.className
  go instances.toList freshIdStart
where
  go : List InstanceDecl → Nat → Option (InstanceDecl × Subst × Array Constraint × Nat)
    | [], _ => none
    | inst :: rest, freshId =>
      let (freshInst, nextId) := inst.freshen freshId
      match tryUnifyArgs freshInst.args constraint.args with
      | none => go rest nextId
      | some σ =>
        let subConstraints := freshInst.constraints.map fun c =>
          { c with args := c.args.map (σ.apply ·) }
        some (freshInst, σ, subConstraints, nextId)

/-- Check if a constraint is immediately satisfiable (no sub-constraints) -/
def hasDirectInstance (env : InstanceEnv) (constraint : Constraint) : Bool :=
  match env.findInstance constraint 1000000 with -- todo: review
  | some (_, _, subConstraints, _) => subConstraints.isEmpty
  | none => false

/-- Get all instances as a flat array -/
def allInstances (env : InstanceEnv) : Array InstanceDecl :=
  env.instances.fold (init := #[]) fun acc _ insts => acc ++ insts

/-- Number of instances -/
def size (env : InstanceEnv) : Nat :=
  env.instances.fold (init := 0) fun acc _ insts => acc + insts.size

/-- Pretty print for debugging -/
def toString (_env : InstanceEnv) : String := "InstanceEnv"

instance : ToString InstanceEnv := ⟨InstanceEnv.toString⟩

end InstanceEnv

namespace TypeClassName
  def eq : TyCon := TyCon.mkUser "" "Eq" 1
  def ord : TyCon := TyCon.mkUser "" "Ord" 2
  def show_ : TyCon := TyCon.mkUser "" "Show" 3
  def num : TyCon := TyCon.mkUser "" "Num" 4
  def functor : TyCon := TyCon.mkUser "" "Functor" 5 (.arrow .star .star)
  def monad : TyCon := TyCon.mkUser "" "Monad" 6 (.arrow .star .star)
end TypeClassName

/-- Build a default instance environment with common instances -/
def defaultInstanceEnv : InstanceEnv := Id.run do
  let mut env := InstanceEnv.empty

  -- Add common type classes
  env := env.addClass {
    name := TypeClassName.eq
    params := #[⟨"a", 0, .star⟩]
    superclasses := #[]
    span := Span.uninhabited
  }

  env := env.addClass {
    name := TypeClassName.ord
    params := #[⟨"a", 0, .star⟩]
    superclasses := #[{ className := TypeClassName.eq, args := #[.var ⟨"a", 0, .star⟩] }]
    span := Span.uninhabited
  }

  env := env.addClass {
    name := TypeClassName.show_
    params := #[⟨"a", 0, .star⟩]
    superclasses := #[]
    span := Span.uninhabited
  }

  env := env.addClass {
    name := TypeClassName.num
    params := #[⟨"a", 0, .star⟩]
    superclasses := #[]
    span := Span.uninhabited
  }

  -- Add instances for primitives
  for prim in [StarPrimitive.int, .long, .short, .byte, .float, .double, .bool, .string] do
    let ty : MonoTy := .starPrim prim
    env := env.addInstance {
      className := TypeClassName.eq
      args := #[ty]
      typeVars := #[]
      constraints := #[]
      id := 0
      span := Span.uninhabited
    }
    env := env.addInstance {
      className := TypeClassName.show_
      args := #[ty]
      typeVars := #[]
      constraints := #[]
      id := 0
      span := Span.uninhabited
    }

  for prim in [StarPrimitive.int, .long, .short, .byte, .float, .double] do
    let ty : MonoTy := .starPrim prim
    env := env.addInstance {
      className := TypeClassName.ord
      args := #[ty]
      typeVars := #[]
      constraints := #[]
      id := 0
      span := Span.uninhabited
    }
    env := env.addInstance {
      className := TypeClassName.num
      args := #[ty]
      typeVars := #[]
      constraints := #[]
      id := 0
      span := Span.uninhabited
    }

  return env

end Soma.Infer
