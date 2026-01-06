import Soma.Metal.Function
import Soma.Syntax.Ast

namespace Soma.Metal

/-- A data constructor (fields stored as syntax for elaboration) -/
structure Constructor where
  name : Name
  tag : Nat
  fieldTypeSyntax : Array Syntax.TypeExpr
  /-- Full type signature for indexed data types (e.g., `a -> Vec n a -> Vec (n+1) a`).
      When present, `fieldTypeSyntax` should be empty. -/
  sigSyntax : Option Syntax.TypeExpr := none

/-- A type definition -/
inductive TypeDef where
  | algebraic (name : Name) (typeVarNames : Array String) (ctors : Array Constructor)
  | struct (name : Name) (typeVarNames : Array String) (ctorName : Name) (fields : Array (Option String × Syntax.TypeExpr))
  | record (name : Name) (typeVarNames : Array String) (fieldNamesAndTypes : Array (String × Syntax.TypeExpr))

namespace TypeDef

def name : TypeDef → Name
  | .algebraic n _ _ => n
  | .struct n _ _ _ => n
  | .record n _ _ => n

def typeVarNames : TypeDef → Array String
  | .algebraic _ vs _ => vs
  | .struct _ vs _ _ => vs
  | .record _ vs _ => vs

def typeVarCount : TypeDef → Nat
  | .algebraic _ vs _ => vs.size
  | .struct _ vs _ _ => vs.size
  | .record _ vs _ => vs.size

/-- Get all constructors -/
def constructors : TypeDef → Array Constructor
  | .algebraic _ _ cs => cs
  | .struct _ _ cn fields => #[{ name := cn, tag := 0, fieldTypeSyntax := fields.map (·.2) }]
  | .record n _ fields => #[{ name := n, tag := 0, fieldTypeSyntax := fields.map (·.2) }]

end TypeDef

/-- An instance declaration (before type checking) -/
structure InstanceDecl where
  className : String
  typeArgsSyntax : Array Syntax.TypeExpr
  constraintsSyntax : Array Syntax.Constraint
  methods : Array UntypedFunction
  span : Syntax.Span

/-- Metadata about a type class -/
structure TypeClassMeta where
  name : Name
  /-- Type parameters with optional kind annotations -/
  params : Array Syntax.TypeVarBinder
  /-- Superclass constraints as syntax -/
  superclasses : Array Syntax.Constraint
  /-- Method names and their type signatures (as syntax) -/
  methodSignatures : Array (Name × Syntax.TypeExpr)

/-- A type abbreviation -/
structure TypeAbbrev where
  name : String
  params : Array String
  expansion : Syntax.TypeExpr

/-! ## Module (after lowering, before type inference) -/

/-- A Metal module - produced by lowering from syntax -/
structure Module where
  name : String
  functions : Array UntypedFunction
  types : Array TypeDef
  instances : Array InstanceDecl
  typeClasses : Array TypeClassMeta
  abbreviations : Array TypeAbbrev := #[]

namespace Module

/-- Create an empty module -/
def empty (name : String) : Module :=
  { name, functions := #[], types := #[], instances := #[], typeClasses := #[], abbreviations := #[] }

/-- Look up a function by name -/
def findFunction (m : Module) (name : Name) : Option UntypedFunction :=
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

/-- Alias for backwards compatibility during migration -/
abbrev UntypedModule := Module
abbrev UntypedTypeDef := TypeDef
abbrev UntypedConstructor := Constructor
abbrev UntypedInstance := InstanceDecl

end Soma.Metal
