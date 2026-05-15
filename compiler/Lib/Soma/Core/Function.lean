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
  /-- Whether this function is marked as total (todo: remove) -/
  total : Bool := false
  /-- Whether this function is explicitly opted out of termination checking -/
  partial_ : Bool := false
  /-- Whether this function is irreducible (opaque to the interaction net reducer) -/
  irreducible : Bool := false
  deriving BEq, Inhabited

namespace FunctionAttrs

end FunctionAttrs

/-- Information about a closure (lifted lambda) -/
structure ClosureInfo where
  capturedVars : Array (Soma.Unique × String)
  deriving BEq

/-- A single parameter slot on an untyped function -/
structure FunctionParam where
  name : String
  typeSyntax : Option Soma.Syntax.Expr := none
  deriving Repr, Inhabited

namespace FunctionParam

end FunctionParam

/-- A function produced by lowering (body is raw syntax, elaborated by type checker) -/
structure Function where
  name : QualifiedName
  params : Array FunctionParam
  body : Soma.Syntax.Expr
  span : Soma.Syntax.Span
  declaredTypeSyntax : Option Soma.Syntax.Expr
  closureInfo : Option ClosureInfo
  attrs : FunctionAttrs
  isBodilessExFalso : Bool := false
  isExternStub : Bool := false

namespace Function

def paramNames (f : Function) : Array String := f.params.map (·.name)

end Function

abbrev UntypedFunction := Function
abbrev UntypedClosureInfo := ClosureInfo

/-- A typed function produced by type checking -/
structure TypedFunction where
  name : QualifiedName
  params : Array (Soma.Unique × String)
  valueParams : Array (Soma.Unique × String × BinderInfo) := #[]
  body : Expr
  fnType : Value
  closureInfo : Option ClosureInfo
  attrs : FunctionAttrs
  errored : Bool := false
  isExternStub : Bool := false

namespace TypedFunction

/-- Build the structured "errored body" sentinel for a function whose elaboration failed -/
def erroredBody (name : QualifiedName) : Expr :=
  .panic s!"errored definition `{name.display}` reached runtime"

/-- Build the body sentinel for `@[extern]` / `@[intrinsic]` declarations -/
def externBody (name : QualifiedName) : Expr :=
  .panic s!"extern/intrinsic body for `{name.display}` reached evaluator"

end TypedFunction

end Soma.Core
