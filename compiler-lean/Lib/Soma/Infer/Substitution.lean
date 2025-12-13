/-
  Type Substitutions

  Key improvements over the old Haskell design:
  1. Kind-preserving substitution (substituting in a Ty k returns Ty k)
  2. Efficient composition using HashMap
  3. Explicit free variable tracking
  4. Support for both monomorphic and polymorphic substitution
-/

import Std.Data.HashMap
import Std.Data.HashSet
import Soma.Typing

namespace Soma.Infer

open Std
open Soma.Typing

/-- A substitution maps type variable IDs to monomorphic types.
    We use Nat (the variable ID) as the key for efficiency. -/
structure Subst where
  /-- The underlying mapping from variable IDs to types -/
  mapping : HashMap Nat MonoTy
  deriving Inhabited

namespace Subst

/-- The empty substitution -/
def empty : Subst := ⟨{}⟩

instance : EmptyCollection Subst := ⟨empty⟩

/-- Create a singleton substitution -/
def singleton (varId : Nat) (ty : MonoTy) : Subst :=
  ⟨({} : HashMap Nat MonoTy).insert varId ty⟩

/-- Create a substitution from a type variable -/
def fromVar (v : TyVarId) (ty : MonoTy) : Subst :=
  singleton v.id ty

/-- Look up a type variable in the substitution -/
def lookup (σ : Subst) (varId : Nat) : Option MonoTy :=
  σ.mapping.get? varId

/-- Look up a type variable, returning the variable itself if not found -/
def lookupOrVar (σ : Subst) (v : TyVarId) : MonoTy :=
  σ.mapping.getD v.id (.var v)

/-- Insert a mapping into the substitution -/
def insert (σ : Subst) (varId : Nat) (ty : MonoTy) : Subst :=
  ⟨σ.mapping.insert varId ty⟩

/-- Remove a variable from the substitution -/
def remove (σ : Subst) (varId : Nat) : Subst :=
  ⟨σ.mapping.erase varId⟩

/-- Check if the substitution is empty -/
def isEmpty (σ : Subst) : Bool :=
  σ.mapping.isEmpty

/-- Get the size of the substitution -/
def size (σ : Subst) : Nat :=
  σ.mapping.size

/-- Get all variable IDs in the domain -/
def domain (σ : Subst) : Array Nat :=
  σ.mapping.toArray.map (·.1)

/-- Get all types in the range -/
def range (σ : Subst) : Array MonoTy :=
  σ.mapping.toArray.map (·.2)

/-- Check if a variable is in the domain -/
def contains (σ : Subst) (varId : Nat) : Bool :=
  σ.mapping.contains varId

/-- Apply a substitution to a monomorphic type -/
def apply (σ : Subst) (ty : MonoTy) : MonoTy :=
  if σ.isEmpty then ty else ty.subst σ.mapping

/-- Apply a substitution to a type of any kind (kind-preserving) -/
def applyAny (σ : Subst) : {k : Kind} → Ty k → Ty k
  | .star, ty => σ.apply ty
  | .arrow _ _, ty => ty.substFun σ.mapping

/-- Apply a substitution to a SomeTy -/
def applySome (σ : Subst) (sty : SomeTy) : SomeTy :=
  ⟨sty.kind, σ.applyAny sty.ty⟩

/-- Compose two substitutions: (σ1 ∘ σ2) means apply σ2 first, then σ1.
    This is the standard composition: (σ1 ∘ σ2)(t) = σ1(σ2(t))

    Implementation: For each binding v → t in σ2, we apply σ1 to t.
    Then we union with σ1, preferring the transformed σ2 bindings. -/
def compose (σ1 σ2 : Subst) : Subst :=
  if σ1.isEmpty then σ2
  else if σ2.isEmpty then σ1
  else
    -- Apply σ1 to all types in σ2's range
    let σ2Applied := σ2.mapping.fold (init := ({} : HashMap Nat MonoTy)) fun acc k v =>
      acc.insert k (σ1.apply v)
    -- Union: σ2Applied takes precedence, but we also need σ1's bindings
    -- for variables not in σ2's domain
    let result := σ1.mapping.fold (init := σ2Applied) fun acc k v =>
      if σ2Applied.contains k then acc else acc.insert k v
    ⟨result⟩

instance : Append Subst where
  append := compose

/-- Get all free type variables in the range of the substitution -/
def rangeVars (σ : Subst) : HashSet Nat :=
  σ.mapping.fold (init := ({} : HashSet Nat)) fun acc _ ty =>
    ty.freeVars.foldl (init := acc) fun acc v => acc.insert v.id

/-- Restrict a substitution to only certain variables -/
def restrict (σ : Subst) (vars : HashSet Nat) : Subst :=
  ⟨σ.mapping.fold (init := ({} : HashMap Nat MonoTy)) fun acc k v =>
    if vars.contains k then acc.insert k v else acc⟩

/-- Exclude certain variables from the substitution -/
def exclude (σ : Subst) (vars : HashSet Nat) : Subst :=
  ⟨σ.mapping.fold (init := ({} : HashMap Nat MonoTy)) fun acc k v =>
    if vars.contains k then acc else acc.insert k v⟩

/-- Create a substitution from parallel arrays of variables and types -/
def fromArrays (vars : Array TyVarId) (types : Array MonoTy) : Subst :=
  if vars.size != types.size then empty
  else
    let pairs := vars.zip types
    ⟨pairs.foldl (init := ({} : HashMap Nat MonoTy)) fun acc (v, t) => acc.insert v.id t⟩

/-- Convert to a list of pairs for debugging -/
def toList (σ : Subst) : List (Nat × MonoTy) :=
  σ.mapping.toList

/-- Pretty print a substitution -/
def toString (σ : Subst) : String :=
  let pairs := σ.mapping.toArray.map fun (k, v) => s!"t{k} ↦ {v}"
  s!"[{", ".intercalate pairs.toList}]"

instance : ToString Subst := ⟨Subst.toString⟩

end Subst

/-- Type class for things that can have substitutions applied -/
class Substitutable (α : Type) where
  apply : Subst → α → α
  freeVars : α → HashSet Nat

namespace Substitutable

instance : Substitutable MonoTy where
  apply := Subst.apply
  freeVars ty := ty.freeVars.foldl (init := ({} : HashSet Nat)) fun acc v => acc.insert v.id

instance : Substitutable Constraint where
  apply σ c := { c with args := c.args.map (σ.apply ·) }
  freeVars c := c.args.foldl (init := ({} : HashSet Nat)) fun acc ty =>
    ty.freeVars.foldl (init := acc) fun acc v => acc.insert v.id

instance : Substitutable QualifiedType where
  apply σ qt :=
    -- Don't substitute bound variables
    let boundIds : HashSet Nat := qt.vars.foldl (init := {}) fun acc v => acc.insert v.id
    let σ' := σ.exclude boundIds
    { qt with
      constraints := qt.constraints.map (apply σ' ·)
      body := σ'.apply qt.body
    }
  freeVars qt :=
    let boundIds : HashSet Nat := qt.vars.foldl (init := {}) fun acc v => acc.insert v.id
    let bodyVars := freeVars qt.body
    let constraintVars := qt.constraints.foldl (init := ({} : HashSet Nat)) fun acc c =>
      freeVars c |>.fold (init := acc) fun acc v => acc.insert v
    (bodyVars.fold (init := constraintVars) fun acc v => acc.insert v).fold
      (init := ({} : HashSet Nat)) fun acc v =>
        if boundIds.contains v then acc else acc.insert v

instance [Substitutable α] : Substitutable (Array α) where
  apply σ arr := arr.map (apply σ ·)
  freeVars arr := arr.foldl (init := ({} : HashSet Nat)) fun acc a =>
    freeVars a |>.fold (init := acc) fun acc v => acc.insert v

instance [Substitutable α] : Substitutable (Option α) where
  apply σ opt := opt.map (apply σ ·)
  freeVars opt := opt.map freeVars |>.getD {}

end Substitutable

end Soma.Infer
