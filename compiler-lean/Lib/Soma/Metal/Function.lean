import Soma.Metal.Expr
import Soma.Syntax.Ast

namespace Soma.Metal

open Soma.Typing
open Soma.Syntax (TypeExpr)

/-- Function attributes -/
structure FunctionAttrs where
  inline : Bool := false
  noInline : Bool := false
  deprecated : Option String := none
  extern : Option String := none
  deriving BEq, Inhabited

namespace FunctionAttrs

def default : FunctionAttrs := {}

end FunctionAttrs

/-- Information about a closure (lifted lambda) - typed version -/
structure ClosureInfo where
  capturedVars : Array (BindingId × String × MonoTy)
  deriving BEq

/-- Information about a closure (lifted lambda) - untyped version -/
structure UntypedClosureInfo where
  capturedVars : Array (BindingId × String)
  deriving BEq

/-! ## Untyped Functions (after lowering, before type inference) -/

/-- An untyped Metal function produced by lowering, consumed by type inference -/
structure UntypedFunction where
  name : Name
  params : Array (BindingId × String)
  body : UntypedExpr (params.toList.map (·.1))
  declaredTypeSyntax : Option TypeExpr
  closureInfo : Option UntypedClosureInfo
  attrs : FunctionAttrs

namespace UntypedFunction

/-- Get the function's arity -/
def arity (f : UntypedFunction) : Nat := f.params.size

/-- Check if this is a closure (lifted lambda) -/
def isClosure (f : UntypedFunction) : Bool := f.closureInfo.isSome

/-- Check if this function has a declared type signature -/
def hasSignature (f : UntypedFunction) : Bool := f.declaredTypeSyntax.isSome

end UntypedFunction

/-! ## Typed Functions (after type inference) -/

/-- A typed Metal function produced by type inference -/
structure Function where
  name : Name
  params : Array (BindingId × String × MonoTy)
  returnType : MonoTy
  body : TypedExpr (params.toList.map (·.1))
  typeVars : Array TyVarId
  constraints : Array Constraint
  closureInfo : Option ClosureInfo
  attrs : FunctionAttrs

namespace Function

/-- Get the function's arity -/
def arity (f : Function) : Nat := f.params.size

/-- Check if this is a closure (lifted lambda) -/
def isClosure (f : Function) : Bool := f.closureInfo.isSome

/-- Check if this function is polymorphic -/
def isPolymorphic (f : Function) : Bool := !f.typeVars.isEmpty

/-- Check if this function has constraints -/
def hasConstraints (f : Function) : Bool := !f.constraints.isEmpty

/-- Get the function type -/
def type (f : Function) : MonoTy :=
  f.params.foldr (fun (_, _, ty) acc => Ty.arrow ty acc) f.returnType

/-- Get the qualified type (with forall and constraints) -/
def qualifiedType (f : Function) : QualifiedType :=
  { vars := f.typeVars
  , constraints := f.constraints
  , body := f.type
  }

end Function

end Soma.Metal
