import Soma.Core.Function
import Soma.Syntax.Ast

namespace Soma.Core

/-- A data constructor (fields stored as syntax for elaboration) -/
structure Constructor where
  name : QualifiedName
  tag : Nat
  fieldTypeSyntax : Array Syntax.TypeExpr
  /-- Full type signature for indexed data types. -/
  sigSyntax : Option Syntax.TypeExpr := none
  /-- Attributes from the source declaration -/
  attrs : Array Syntax.Attribute := #[]

namespace Constructor

def qualifiedName (c : Constructor) : QualifiedName :=
  c.name

end Constructor

/-- A type definition -/
inductive TypeDef where
  | algebraic (attrs : Array Syntax.Attribute) (name : QualifiedName)
      (typeVarNames : Array String) (ctors : Array Constructor)
  | record (attrs : Array Syntax.Attribute) (name : QualifiedName) (typeVarNames : Array String) (ctorName : QualifiedName)
      (fields : Array (Option String × Syntax.TypeExpr))

namespace TypeDef

def name : TypeDef → QualifiedName
  | .algebraic _ n _ _ => n
  | .record _ n _ _ _ => n

def qualifiedName (td : TypeDef) : QualifiedName :=
  td.name

def typeVarNames : TypeDef → Array String
  | .algebraic _ _ vs _ => vs
  | .record _ _ vs _ _ => vs

def typeVarCount : TypeDef → Nat
  | .algebraic _ _ vs _ => vs.size
  | .record _ _ vs _ _ => vs.size

def attrs : TypeDef → Array Syntax.Attribute
  | .algebraic attrs _ _ _ => attrs
  | .record attrs _ _ _ _ => attrs

def constructors : TypeDef → Array Constructor
  | .algebraic _ _ _ cs => cs
  | .record _ _ _ cn fields => #[{ name := cn, tag := 0, fieldTypeSyntax := fields.map (·.2) }]

end TypeDef

/-- An instance declaration (before type checking) -/
structure InstanceDecl where
  className : String
  typeArgsSyntax : Array Syntax.TypeExpr
  binders : Array Syntax.InstanceBinder
  methods : Array UntypedFunction
  span : Syntax.Span

/-- Metadata about a type class -/
structure TypeClassMeta where
  name : QualifiedName
  params : Array Syntax.TypeVarBinder
  superclasses : Array Syntax.Constraint
  methodSignatures : Array (QualifiedName × Syntax.TypeExpr)
  span : Syntax.Span

/-- A type abbreviation (before type checking) -/
structure TypeAbbrev where
  name : String
  params : Array String
  expansion : Syntax.TypeExpr
  span : Syntax.Span

/-- A module produced by syntax lowering -/
structure Module where
  name : String
  functions : Array UntypedFunction
  types : Array TypeDef
  instances : Array InstanceDecl
  typeClasses : Array TypeClassMeta
  abbreviations : Array TypeAbbrev := #[]

namespace Module

def empty (name : String) : Module :=
  { name, functions := #[], types := #[], instances := #[], typeClasses := #[], abbreviations := #[] }

def findFunction (m : Module) (name : QualifiedName) : Option UntypedFunction :=
  m.functions.find? (·.name == name)

def findFunctionByQualifiedName (m : Module) (name : QualifiedName) : Option UntypedFunction :=
  m.functions.find? (fun fn => fn.name == name)

def findType (m : Module) (name : QualifiedName) : Option TypeDef :=
  m.types.find? (·.name == name)

def findTypeByQualifiedName (m : Module) (name : QualifiedName) : Option TypeDef :=
  m.types.find? (fun td => td.qualifiedName == name)

def allConstructors (m : Module) : Array (QualifiedName × Constructor) :=
  m.types.foldl (fun acc td => acc ++ td.constructors.map (fun c => (c.name, c))) #[]

def allConstructorsByQualifiedName (m : Module) : Array (QualifiedName × Constructor) :=
  m.types.foldl (fun acc td =>
    acc ++ td.constructors.map (fun c => (c.qualifiedName, c))
  ) #[]

def findConstructor (m : Module) (name : QualifiedName) : Option Constructor :=
  m.allConstructors.find? (·.1 == name) |>.map (·.2)

def findConstructorByQualifiedName (m : Module) (name : QualifiedName) : Option Constructor :=
  m.allConstructorsByQualifiedName.find? (·.1 == name) |>.map (·.2)

end Module

abbrev UntypedModule := Module
abbrev UntypedTypeDef := TypeDef
abbrev UntypedConstructor := Constructor
abbrev UntypedInstance := InstanceDecl

end Soma.Core
