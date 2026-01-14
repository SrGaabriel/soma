import Soma.Metal.Expr
import Soma.Syntax.Ast
import Soma.Core.Value

namespace Soma.Metal

open Soma.Syntax (TypeExpr)

/-- Function attributes -/
structure FunctionAttrs where
  inline : Bool := false
  noInline : Bool := false
  deprecated : Option String := none
  extern : Option String := none
  /-- Whether this function is marked as total (must terminate) -/
  total : Bool := false
  deriving BEq, Inhabited

namespace FunctionAttrs

def default : FunctionAttrs := {}

end FunctionAttrs

/-- Information about a closure (lifted lambda) -/
structure ClosureInfo where
  capturedVars : Array (BindingId × String)
  deriving BEq

/-- A Metal function produced by lowering -/
structure Function where
  name : Name
  params : Array (BindingId × String)
  body : UntypedExpr (params.toList.map (·.1))
  declaredTypeSyntax : Option TypeExpr
  closureInfo : Option ClosureInfo
  attrs : FunctionAttrs

namespace Function

/-- Get the function's arity -/
def arity (f : Function) : Nat := f.params.size

/-- Check if this is a closure (lifted lambda) -/
def isClosure (f : Function) : Bool := f.closureInfo.isSome

/-- Check if this function has a declared type signature -/
def hasSignature (f : Function) : Bool := f.declaredTypeSyntax.isSome

end Function

/-- Alias for backwards compatibility during migration -/
abbrev UntypedFunction := Function
abbrev UntypedClosureInfo := ClosureInfo

/-- A typed Metal function - produced by type checking -/
structure TypedFunction where
  name : Name
  params : Array (BindingId × String)
  body : Expr Soma.Core.Value (params.toList.map (·.1))
  fnType : Soma.Core.Value
  closureInfo : Option ClosureInfo
  attrs : FunctionAttrs

namespace TypedFunction

/-- Get the function's arity -/
def arity (f : TypedFunction) : Nat := f.params.size

/-- Check if this is a closure (lifted lambda) -/
def isClosure (f : TypedFunction) : Bool := f.closureInfo.isSome

end TypedFunction

end Soma.Metal
