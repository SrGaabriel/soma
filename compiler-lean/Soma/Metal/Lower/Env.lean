import Soma.Metal.Name
import Soma.Metal.Scope
import Soma.Typing
import Soma.Syntax.Ast
import Soma.Syntax.Source
import Std.Data.HashMap

namespace Soma.Metal.Lower

open Soma.Typing
open Soma.Metal
open Soma.Syntax (TypeExpr Span)

/-- Information about a global binding (collected during first pass) -/
structure GlobalInfo where
  name : Name
  typeSyntax : Option TypeExpr
  definedAt : Span

/-- Information about a resolved type -/
structure TypeInfo where
  tyCon : TyCon
  params : Array TyVarId
  kind : Kind

/-- Information about a constructor -/
structure ConstructorInfo where
  name : Name
  parentType : String
  tag : Nat
  fields : Array MonoTy

/-- Information about a type class -/
structure TypeClassInfo where
  name : Name
  tyCon : TyCon
  methods : Array (String × QualifiedType)

/-- The global environment (built during first pass over declarations) -/
structure GlobalEnv where
  moduleName : String
  globals : Std.HashMap String GlobalInfo
  types : Std.HashMap String TypeInfo
  constructors : Std.HashMap String ConstructorInfo
  typeClasses : Std.HashMap String TypeClassInfo
  instances : Std.HashMap String (Array QualifiedType)

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

def lookupGlobal (env : GlobalEnv) (name : String) : Option GlobalInfo :=
  env.globals.get? name

def lookupType (env : GlobalEnv) (name : String) : Option TypeInfo :=
  env.types.get? name

def lookupConstructor (env : GlobalEnv) (name : String) : Option ConstructorInfo :=
  env.constructors.get? name

def lookupTypeClass (env : GlobalEnv) (name : String) : Option TypeClassInfo :=
  env.typeClasses.get? name

end GlobalEnv

/-- Local environment for expression lowering (changes as we descend) -/
structure LocalEnv (scope : Scope) where
  /-- Mapping from source names to scoped variables -/
  bindings : Std.HashMap String (ScopedVar scope)

namespace LocalEnv

def empty : LocalEnv [] := ⟨{}⟩

def lookup (env : LocalEnv scope) (name : String) : Option (ScopedVar scope) :=
  env.bindings.get? name

/-- Extend with a new binding -/
def extend (env : LocalEnv scope) (b : BindingId) (name : String)
    : LocalEnv (b :: scope) :=
  let weakened : Std.HashMap String (ScopedVar (b :: scope)) :=
    env.bindings.fold (init := {}) fun acc k v =>
      acc.insert k (v.weaken b)
  let newVar := ScopedVar.here b name scope
  ⟨weakened.insert name newVar⟩

/-- Extend with multiple bindings -/
def extendMany (env : LocalEnv scope) (bindings : List (BindingId × String))
    : (newScope : Scope) × LocalEnv newScope :=
  match bindings with
  | [] => ⟨scope, env⟩
  | (b, name) :: rest =>
    let env' := env.extend b name
    let ⟨finalScope, finalEnv⟩ := extendMany env' rest
    ⟨finalScope, finalEnv⟩

end LocalEnv

end Soma.Metal.Lower
