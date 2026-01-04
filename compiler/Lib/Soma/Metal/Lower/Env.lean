import Soma.Metal.Name
import Soma.Metal.Scope
import Soma.Core.TypeId
import Soma.Unique
import Soma.Syntax.Ast
import Soma.Syntax.Source
import Std.Data.HashMap

namespace Soma.Metal.Lower

open Soma
open Soma.Core (TypeId)
open Soma.Metal
open Soma.Syntax (TypeExpr Span Constraint)

/-- Information about a global binding (collected during first pass) -/
structure GlobalInfo where
  name : Name
  typeSyntax : Option TypeExpr
  definedAt : Span

namespace GlobalInfo

instance : ToString GlobalInfo := ⟨fun info => toString info.name⟩

end GlobalInfo

/-- Information about a resolved type -/
structure TypeInfo where
  typeId : TypeId
  paramNames : Array String
  unique : Unique
  fieldNames : Array String := #[]

namespace TypeInfo

/-- Get the Metal.Name for this type -/
def name (info : TypeInfo) : Name := .user info.unique

/-- Get the type name as a string -/
def nameStr (info : TypeInfo) : String := info.typeId.name

/-- Check if this type is parameterized -/
def isParametric (info : TypeInfo) : Bool := !info.paramNames.isEmpty

/-- Get the arity (number of type parameters) -/
def arity (info : TypeInfo) : Nat := info.paramNames.size

/-- Check if this type has fields (is a struct/record) -/
def hasFields (info : TypeInfo) : Bool := !info.fieldNames.isEmpty

/-- Get the index of a field by name -/
def fieldIndex (info : TypeInfo) (fieldName : String) : Option Nat :=
  info.fieldNames.findIdx? (· == fieldName)

end TypeInfo

/-- Information about a constructor -/
structure ConstructorInfo where
  name : Name
  parentType : String
  parentUnique : Unique
  tag : Nat
  /-- Field types as syntax (unresolved) - for simple constructors -/
  fieldTypeSyntax : Array TypeExpr
  /-- Full type signature for indexed data types (e.g., `a -> Vec n a -> Vec (n+1) a`).
      When present, `fieldTypeSyntax` should be empty. -/
  sigSyntax : Option TypeExpr := none
  span : Span

namespace ConstructorInfo

/-- Get the constructor name (without type prefix) -/
def ctorName (info : ConstructorInfo) : String :=
  match info.name with
  | .ctor _ n _ => n
  | _ => info.name.display

/-- Check if this is a nullary constructor -/
def isNullary (info : ConstructorInfo) : Bool :=
  info.fieldTypeSyntax.isEmpty && info.sigSyntax.isNone

/-- Get the arity (number of fields) - returns 0 for indexed constructors with signatures -/
def arity (info : ConstructorInfo) : Nat := info.fieldTypeSyntax.size

/-- Check if this is an indexed constructor (has full signature) -/
def isIndexed (info : ConstructorInfo) : Bool := info.sigSyntax.isSome

end ConstructorInfo

/-- Information about a type class -/
structure TypeClassInfo where
  name : Name
  typeId : TypeId
  /-- Type parameter names (e.g., ["a"] for `trait Eq a`) -/
  paramNames : Array String
  /-- Superclass constraints as syntax -/
  superclasses : Array Constraint
  /-- Method signatures as syntax (name, type syntax) -/
  methods : Array (Name × TypeExpr)
  unique : Unique

namespace TypeClassInfo

/-- Get the number of methods -/
def methodCount (info : TypeClassInfo) : Nat := info.methods.size

/-- Look up a method by name -/
def lookupMethod (info : TypeClassInfo) (name : String) : Option TypeExpr :=
  info.methods.find? (·.1.display == name) |>.map (·.2)

end TypeClassInfo

/-- The global environment (built during first pass over declarations) -/
structure GlobalEnv where
  moduleName : String
  globals : Std.HashMap String GlobalInfo
  types : Std.HashMap String TypeInfo
  constructors : Std.HashMap String ConstructorInfo
  typeClasses : Std.HashMap String TypeClassInfo
  /-- Instance types stored as syntax (unresolved) -/
  instances : Std.HashMap String (Array TypeExpr)

namespace GlobalEnv

def empty (moduleName : String) : GlobalEnv :=
  { moduleName
  , globals := {}
  , types := {}
  , constructors := {}
  , typeClasses := {}
  , instances := {}
  }

def addGlobal (env : GlobalEnv) (name : String) (info : GlobalInfo) : GlobalEnv :=
  { env with globals := env.globals.insert name info }

def addType (env : GlobalEnv) (name : String) (info : TypeInfo) : GlobalEnv :=
  { env with types := env.types.insert name info }

def addConstructor (env : GlobalEnv) (name : String) (info : ConstructorInfo) : GlobalEnv :=
  { env with constructors := env.constructors.insert name info }

def addTypeClass (env : GlobalEnv) (name : String) (info : TypeClassInfo) : GlobalEnv :=
  { env with typeClasses := env.typeClasses.insert name info }

def addInstance (env : GlobalEnv) (className : String) (instanceType : TypeExpr) : GlobalEnv :=
  let existing := env.instances.getD className #[]
  { env with instances := env.instances.insert className (existing.push instanceType) }

def lookupGlobal (env : GlobalEnv) (name : String) : Option GlobalInfo :=
  env.globals.get? name

def lookupType (env : GlobalEnv) (name : String) : Option TypeInfo :=
  env.types.get? name

def lookupConstructor (env : GlobalEnv) (name : String) : Option ConstructorInfo :=
  env.constructors.get? name

def lookupTypeClass (env : GlobalEnv) (name : String) : Option TypeClassInfo :=
  env.typeClasses.get? name

def lookupInstances (env : GlobalEnv) (className : String) : Array TypeExpr :=
  env.instances.getD className #[]

def containsGlobal (env : GlobalEnv) (name : String) : Bool :=
  env.globals.contains name

def containsType (env : GlobalEnv) (name : String) : Bool :=
  env.types.contains name

def containsConstructor (env : GlobalEnv) (name : String) : Bool :=
  env.constructors.contains name

def containsTypeClass (env : GlobalEnv) (name : String) : Bool :=
  env.typeClasses.contains name

/-- Get all global names -/
def globalNames (env : GlobalEnv) : Array String :=
  env.globals.fold (init := #[]) fun acc k _ => acc.push k

/-- Get all type names -/
def typeNames (env : GlobalEnv) : Array String :=
  env.types.fold (init := #[]) fun acc k _ => acc.push k

/-- Get all constructor names -/
def constructorNames (env : GlobalEnv) : Array String :=
  env.constructors.fold (init := #[]) fun acc k _ => acc.push k

end GlobalEnv

/-- Local environment for expression lowering (changes as we descend).

    Uses a HashMap for O(1) lookup, but tracks scope through the
    dependent type parameter for type safety.
-/
structure LocalEnv (scope : Scope) where
  /-- Mapping from source names to scoped variables -/
  bindings : Std.HashMap String (ScopedVar scope)

namespace LocalEnv

def empty : LocalEnv [] := ⟨{}⟩

def lookup (env : LocalEnv scope) (name : String) : Option (ScopedVar scope) :=
  env.bindings.get? name

def contains (env : LocalEnv scope) (name : String) : Bool :=
  env.bindings.contains name

/-- Get all names in scope -/
def names (env : LocalEnv scope) : Array String :=
  env.bindings.fold (init := #[]) fun acc k _ => acc.push k

/-- Extend with a new binding -/
def extend (env : LocalEnv scope) (b : BindingId) (name : String)
    : LocalEnv (b :: scope) :=
  let weakened : Std.HashMap String (ScopedVar (b :: scope)) :=
    env.bindings.fold (init := {}) fun acc k v =>
      acc.insert k (v.weaken b)
  let newVar := ScopedVar.here b name scope
  ⟨weakened.insert name newVar⟩

/-- Extend with a binding, using its original name -/
def extendWithBinding (env : LocalEnv scope) (b : BindingId)
    : LocalEnv (b :: scope) :=
  env.extend b b.original

/-- Extend with multiple bindings.
    Returns the new scope and environment as a dependent pair. -/
def extendMany (env : LocalEnv scope) (bindings : List (BindingId × String))
    : (newScope : Scope) × LocalEnv newScope :=
  match bindings with
  | [] => ⟨scope, env⟩
  | (b, name) :: rest =>
    let env' := env.extend b name
    let ⟨finalScope, finalEnv⟩ := extendMany env' rest
    ⟨finalScope, finalEnv⟩

/-- Extend with multiple bindings, using their original names -/
def extendManyWithBindings (env : LocalEnv scope) (bindings : List BindingId)
    : (newScope : Scope) × LocalEnv newScope :=
  extendMany env (bindings.map fun b => (b, b.original))

end LocalEnv

end Soma.Metal.Lower
