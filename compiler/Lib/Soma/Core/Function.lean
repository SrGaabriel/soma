import Soma.Syntax.Ast
import Soma.Core.Value
import Soma.Core.Expr

namespace Soma.Core

/-- Function attributes -/
structure FunctionAttrs where
  inline : Bool := false
  noInline : Bool := false
  deprecated : Option String := none
  /-- External function name (for @[extern] functions) -/
  extern : Option String := none
  /-- Intrinsic tag from @[intrinsic "tag"] -/
  intrinsic : Option String := none
  /-- Wired-in role from @[wired_in "role"] -/
  wiredIn : Option String := none
  /-- Whether this function is marked as total (must terminate) -/
  total : Bool := false
  /-- Whether this function is irreducible (opaque to the interaction net reducer) -/
  irreducible : Bool := false
  deriving BEq, Inhabited

namespace FunctionAttrs

def default : FunctionAttrs := {}

end FunctionAttrs

/-- Information about a closure (lifted lambda) -/
structure ClosureInfo where
  capturedVars : Array (Soma.Unique × String)
  deriving BEq

/-- A function produced by lowering (body is raw syntax, elaborated by type checker) -/
structure Function where
  name : QualifiedName
  params : Array String
  body : Soma.Syntax.Expr
  span : Soma.Syntax.Span
  declaredTypeSyntax : Option Soma.Syntax.Expr
  closureInfo : Option ClosureInfo
  attrs : FunctionAttrs
  isBodilessExFalso : Bool := false

namespace Function

def qualifiedName (f : Function) : QualifiedName :=
  f.name

def arity (f : Function) : Nat := f.params.size

def isClosure (f : Function) : Bool := f.closureInfo.isSome

def hasSignature (f : Function) : Bool := f.declaredTypeSyntax.isSome

end Function

abbrev UntypedFunction := Function
abbrev UntypedClosureInfo := ClosureInfo

/-- A typed function produced by type checking -/
structure TypedFunction where
  name : QualifiedName
  params : Array (Soma.Unique × String)
  body : Expr
  fnType : Value
  closureInfo : Option ClosureInfo
  attrs : FunctionAttrs

namespace TypedFunction

def qualifiedName (f : TypedFunction) : QualifiedName :=
  f.name

def arity (f : TypedFunction) : Nat := f.params.size

def isClosure (f : TypedFunction) : Bool := f.closureInfo.isSome

end TypedFunction

end Soma.Core
