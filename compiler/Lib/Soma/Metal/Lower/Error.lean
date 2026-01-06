import Soma.Syntax.Source
import Soma.Syntax.Diagnostic

namespace Soma.Metal.Lower

open Soma.Syntax (Span Diagnostic Label)

/-- Naming convention expected for a declaration kind -/
inductive NamingConvention where
  | snakeCase
  | pascalCase
  deriving Repr, BEq

instance : ToString NamingConvention where
  toString
    | .snakeCase => "snake_case"
    | .pascalCase => "PascalCase"

/-- Warnings that can occur during lowering -/
inductive LowerWarning where
  | namingConvention (declKind : String) (name : String) (span : Span) (expected : NamingConvention)
  deriving Repr

namespace LowerWarning

def span : LowerWarning → Span
  | .namingConvention _ _ s _ => s

def message : LowerWarning → String
  | .namingConvention kind name _ expected =>
    s!"{kind} `{name}` should use {expected} naming convention"

/-- Convert a LowerWarning to a Diagnostic -/
def toDiagnostic : LowerWarning → Diagnostic
  | .namingConvention kind name span expected =>
    Diagnostic.warning s!"{kind} `{name}` should use {expected}" span "non-conventional name"
      |>.withHelp s!"{kind} names should use {expected} (e.g., {exampleFor expected})"
where
  exampleFor : NamingConvention → String
    | .snakeCase => "foo_bar, my_function"
    | .pascalCase => "FooBar, MyType"

end LowerWarning

/-- Errors that can occur during lowering -/
inductive LowerError where
  | unboundVariable (name : String) (span : Span)
  | unknownType (name : String) (span : Span)
  | unknownTypeClass (name : String) (span : Span)
  | unknownConstructor (name : String) (span : Span)
  | unknownField (typeName : String) (fieldName : String) (span : Span)
  | duplicateDefinition (name : String) (span : Span) (previousSpan : Span)
  | invalidPattern (message : String) (span : Span)
  | kindMismatch (expected : String) (got : String) (span : Span)
  | unsupportedFeature (feature : String) (span : Span)
  | other (message : String) (span : Span)
  deriving Repr

namespace LowerError

def span : LowerError → Span
  | .unboundVariable _ s => s
  | .unknownType _ s => s
  | .unknownTypeClass _ s => s
  | .unknownConstructor _ s => s
  | .unknownField _ _ s => s
  | .duplicateDefinition _ s _ => s
  | .invalidPattern _ s => s
  | .kindMismatch _ _ s => s
  | .unsupportedFeature _ s => s
  | .other _ s => s

def message : LowerError → String
  | .unboundVariable name _ => s!"Unbound variable: {name}"
  | .unknownType name _ => s!"Unknown type: {name}"
  | .unknownTypeClass name _ => s!"Unknown type class: {name}"
  | .unknownConstructor name _ => s!"Unknown constructor: {name}"
  | .unknownField typeName fieldName _ => s!"Unknown field: {typeName}.{fieldName}"
  | .duplicateDefinition name _ _ => s!"Duplicate definition: {name}"
  | .invalidPattern msg _ => s!"Invalid pattern: {msg}"
  | .kindMismatch expected got _ => s!"Kind mismatch: expected {expected}, got {got}"
  | .unsupportedFeature feature _ => s!"Unsupported feature: {feature}"
  | .other msg _ => msg

/-- Convert a LowerError to a rich Diagnostic -/
def toDiagnostic : LowerError → Diagnostic
  | .unboundVariable name span =>
    Diagnostic.error s!"Unbound variable `{name}`" span "not found in scope"
      |>.withHelp s!"Did you mean to define `{name}` or import it?"

  | .unknownType name span =>
    Diagnostic.error s!"Unknown type `{name}`" span "type not defined"
      |>.withHelp "Check that the type is defined or imported"

  | .unknownTypeClass name span =>
    Diagnostic.error s!"Unknown type class `{name}`" span "type class not defined"

  | .unknownConstructor name span =>
    Diagnostic.error s!"Unknown constructor `{name}`" span "constructor not defined"
      |>.withHelp "Check that the data type is defined or imported"

  | .unknownField typeName fieldName span =>
    Diagnostic.error s!"Unknown field `{typeName}.{fieldName}`" span "field not defined"
      |>.withHelp s!"Check that `{typeName}` has a field named `{fieldName}`"

  | .duplicateDefinition name span previousSpan =>
    Diagnostic.error s!"Duplicate definition of `{name}`" span "redefined here"
      |>.withSecondary previousSpan "previously defined here"

  | .invalidPattern msg span =>
    Diagnostic.error s!"Invalid pattern: {msg}" span

  | .kindMismatch expected got span =>
    Diagnostic.error s!"Kind mismatch" span s!"expected {expected}, got {got}"
      |>.withNote s!"Types have kinds: * for value types, * -> * for type constructors like Array"

  | .unsupportedFeature feature span =>
    Diagnostic.error s!"Unsupported feature: {feature}" span "not available in simple type inference"
      |>.withHelp "Use `somac check-dep` for dependent type checking"

  | .other msg span =>
    Diagnostic.error msg span

instance : ToString LowerError := ⟨LowerError.message⟩

end LowerError

/-- Convert an array of LowerErrors to Diagnostics -/
def LowerError.toDiagnostics (errors : Array LowerError) : Array Diagnostic :=
  errors.map LowerError.toDiagnostic

/-- Convert an array of LowerWarnings to Diagnostics -/
def LowerWarning.toDiagnostics (warnings : Array LowerWarning) : Array Diagnostic :=
  warnings.map LowerWarning.toDiagnostic

end Soma.Metal.Lower
