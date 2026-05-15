import Soma.Core.Function
import Soma.Syntax.Ast

namespace Soma.Core

/-- A data constructor (fields stored as syntax for elaboration) -/
structure Constructor where
  name : QualifiedName
  tag : Nat
  fieldTypeSyntax : Array Syntax.Expr
  fieldBinderInfos : Array BinderInfo := #[]
  fieldQuantities : Array Quantity := #[]
  fieldNames : Array String := #[]
  /-- Full type signature for indexed data types -/
  sigSyntax : Option Syntax.Expr := none
  /-- Attributes from the source declaration -/
  attrs : Array Syntax.Attribute := #[]

namespace Constructor

end Constructor

/-- A record field declaration captured during lowering -/
structure RecordFieldDef where
  name : Option String
  type : Syntax.Expr
  binderInfo : BinderInfo := .explicit
  quantity : Quantity := .omega

namespace RecordFieldDef

end RecordFieldDef

/-- A type definition -/
inductive TypeDef where
  | algebraic (attrs : Array Syntax.Attribute) (name : QualifiedName)
      (typeVarBinders : Array Syntax.TypeVarBinder) (paramCount : Nat)
      (ctors : Array Constructor)
      (headSort : Level) (span : Soma.Syntax.Span)
  | record (attrs : Array Syntax.Attribute) (name : QualifiedName)
      (typeVarBinders : Array Syntax.TypeVarBinder) (ctorName : QualifiedName)
      (fields : Array RecordFieldDef) (span : Soma.Syntax.Span)

namespace TypeDef

end TypeDef

/-- An instance declaration (before type checking) -/
structure InstanceDecl where
  className : Syntax.QualName
  typeArgsSyntax : Array Syntax.Expr
  binders : Array Syntax.InstanceBinder
  methods : Array UntypedFunction
  span : Syntax.Span

/-- Metadata about a type class -/
structure TypeClassMeta where
  name : QualifiedName
  binders : Array Syntax.TypeVarBinder
  methodSignatures : Array (QualifiedName × Syntax.Expr)
  span : Syntax.Span

namespace TypeClassMeta

/-- The class's type-variable binders, in source order -/
def params (m : TypeClassMeta) : Array Syntax.TypeVarBinder :=
  m.binders.filter (! ·.isConstraint)

/-- The class's super-class constraint binders -/
def superclasses (m : TypeClassMeta)
    : Array (Option Syntax.QualName × Syntax.Constraint) :=
  m.binders.filterMap fun b => match b with
    | .constraint n? c => some (n?, c)
    | _                => none

end TypeClassMeta

/-- A type abbreviation (before type checking) -/
structure TypeAbbrev where
  name : String
  params : Array String
  expansion : Syntax.Expr
  span : Syntax.Span

/-- A module produced by syntax lowering -/
structure Module where
  name : String
  functions : Array UntypedFunction
  theorems : Array UntypedFunction := #[]
  types : Array TypeDef
  instances : Array InstanceDecl
  typeClasses : Array TypeClassMeta
  abbreviations : Array TypeAbbrev := #[]

namespace Module

end Module

abbrev UntypedModule := Module
abbrev UntypedTypeDef := TypeDef
abbrev UntypedConstructor := Constructor
abbrev UntypedInstance := InstanceDecl

end Soma.Core
