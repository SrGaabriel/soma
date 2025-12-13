import Soma.Metal.Function
import Soma.Syntax.Ast

namespace Soma.Metal

open Soma.Typing

/-- A data constructor (untyped - fields not yet resolved) -/
structure UntypedConstructor where
  name : Name
  tag : Nat
  fieldTypeSyntax : Array Syntax.TypeExpr

/-- A data constructor (typed) -/
structure Constructor where
  name : Name
  tag : Nat
  fields : Array MonoTy
  deriving BEq

/-- An untyped type definition -/
inductive UntypedTypeDef where
  | algebraic (name : Name) (typeVarNames : Array String) (ctors : Array UntypedConstructor)
  | struct (name : Name) (typeVarNames : Array String) (ctorName : Name) (fieldTypeSyntax : Array Syntax.TypeExpr)
  | record (name : Name) (typeVarNames : Array String) (fieldNamesAndTypes : Array (String × Syntax.TypeExpr))

namespace UntypedTypeDef

def name : UntypedTypeDef → Name
  | .algebraic n _ _ => n
  | .struct n _ _ _ => n
  | .record n _ _ => n

def typeVarCount : UntypedTypeDef → Nat
  | .algebraic _ vs _ => vs.size
  | .struct _ vs _ _ => vs.size
  | .record _ vs _ => vs.size

end UntypedTypeDef

/-- A typed type definition -/
inductive TypeDef where
  | algebraic (name : Name) (typeVars : Array TyVarId) (ctors : Array Constructor)
  | struct (name : Name) (typeVars : Array TyVarId) (ctorName : Name) (fields : Array MonoTy)
  | record (name : Name) (typeVars : Array TyVarId) (fields : Array (String × MonoTy))

namespace TypeDef

/-- Get the name of a type definition -/
def name : TypeDef → Name
  | .algebraic n _ _ => n
  | .struct n _ _ _ => n
  | .record n _ _ => n

/-- Get the type variables of a type definition -/
def typeVars : TypeDef → Array TyVarId
  | .algebraic _ vs _ => vs
  | .struct _ vs _ _ => vs
  | .record _ vs _ => vs

/-- Get all constructors (for algebraic types) -/
def constructors : TypeDef → Array Constructor
  | .algebraic _ _ cs => cs
  | .struct _ _ cn fields => #[{ name := cn, tag := 0, fields := fields }]
  | .record n _ fields => #[{ name := n, tag := 0, fields := fields.map (·.2) }]

end TypeDef

/-- An untyped instance (before type checking) -/
structure UntypedInstance where
  className : String
  typeArgsSyntax : Array Syntax.TypeExpr
  constraintsSyntax : Array Syntax.Constraint
  methods : Array UntypedFunction
  span : Syntax.Span

/-- A typed type class instance -/
structure Instance where
  className : String
  instanceType : MonoTy
  methods : Array Function

/-- Metadata about a type class -/
structure TypeClassMeta where
  name : Name
  methods : Array (Name × QualifiedType)

/-! ## Untyped Module (after lowering, before type inference) -/

/-- An untyped Metal module - produced by lowering -/
structure UntypedModule where
  name : String
  functions : Array UntypedFunction
  types : Array UntypedTypeDef
  instances : Array UntypedInstance
  typeClasses : Array TypeClassMeta

namespace UntypedModule

/-- Create an empty untyped module -/
def empty (name : String) : UntypedModule :=
  { name, functions := #[], types := #[], instances := #[], typeClasses := #[] }

/-- Look up a function by name -/
def findFunction (m : UntypedModule) (name : Name) : Option UntypedFunction :=
  m.functions.find? (·.name == name)

end UntypedModule

/-! ## Typed Module (after type inference) -/

/-- A typed Metal module -/
structure Module where
  name : String
  functions : Array Function
  types : Array TypeDef
  instances : Array Instance
  typeClasses : Array TypeClassMeta

namespace Module

/-- Create an empty module -/
def empty (name : String) : Module :=
  { name, functions := #[], types := #[], instances := #[], typeClasses := #[] }

/-- Look up a function by name -/
def findFunction (m : Module) (name : Name) : Option Function :=
  m.functions.find? (·.name == name)

/-- Look up a type definition by name -/
def findType (m : Module) (name : Name) : Option TypeDef :=
  m.types.find? (·.name == name)

/-- Get all constructor names and their metadata -/
def allConstructors (m : Module) : Array (Name × Constructor) :=
  m.types.foldl (fun acc td =>
    acc ++ td.constructors.map (fun c => (c.name, c))
  ) #[]

/-- Look up a constructor by name -/
def findConstructor (m : Module) (name : Name) : Option Constructor :=
  m.allConstructors.find? (·.1 == name) |>.map (·.2)

end Module

end Soma.Metal
