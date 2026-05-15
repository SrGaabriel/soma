import Soma.Syntax.Source
import Soma.Core.Pp

namespace Soma.Dependent

open Soma.Syntax (Span)
open Soma.Core (PpContext Value)

inductive ExprKind where
  | var (name : String)
  | lit
  | app
  | infixOp (op : String)
  | lambda (paramCount : Nat)
  | ifElse
  | caseExpr
  | tuple (size : Nat)
  | list
  | record
  | recordUpdate
  | fieldAccess (field : String)
  | projection (tyName : String) (fieldName : String)
  | parens
  | annotation
  | typeApp
  | composeBlock (stmtCount : Nat)
  | variant (label : String)
  | constructor (name : String)
  | arrow
  | piType
  | sigmaType
  | forallType (varCount : Nat)
  | recordType
  | variantType
  | listType
  deriving Repr, BEq, Inhabited

namespace ExprKind

def describe : ExprKind → String
  | .var name => s!"var({name})"
  | .lit => "lit"
  | .app => "app"
  | .infixOp op => s!"infix({op})"
  | .lambda n => s!"λ({n} params)"
  | .ifElse => "if"
  | .caseExpr => "case"
  | .tuple n => s!"tuple({n})"
  | .list => "list"
  | .record => "record"
  | .recordUpdate => "recordUpdate"
  | .fieldAccess f => s!".{f}"
  | .projection tn fn => s!"proj({tn}.{fn})"
  | .parens => "parens"
  | .annotation => "ann"
  | .typeApp => "typeApp"
  | .composeBlock n => s!"composeBlock({n} stmts)"
  | .variant label => s!"variant(.{label})"
  | .constructor name => s!"con({name})"
  | .arrow => "arrow"
  | .piType => "pi"
  | .sigmaType => "sigma"
  | .forallType n => s!"forall({n})"
  | .recordType => "recordTy"
  | .variantType => "variantTy"
  | .listType => "listTy"

instance : ToString ExprKind := ⟨describe⟩

end ExprKind

/-- The purpose of a type check -/
inductive CheckPurpose where
  /-- Checking function body against declared return type -/
  | functionBody (fnName : String)
  /-- Checking argument against parameter type -/
  | functionArg (fnName : String) (argIndex : Nat)
  /-- Checking if condition against Bool -/
  | ifCondition
  /-- Checking pattern against scrutinee type -/
  | patternMatch
  /-- Checking let binding value against declared type -/
  | letBinding (name : String)
  /-- Checking against explicit type annotation -/
  | typeAnnotation
  /-- Checking pair element -/
  | pairElement (isFirst : Bool)
  /-- General checking (fallback) -/
  | general
  deriving Repr, BEq, Inhabited

namespace CheckPurpose

def describe : CheckPurpose → String
  | .functionBody fn => s!"in return type of function '{fn}'"
  | .functionArg fn idx => s!"in argument {idx + 1} of call to '{fn}'"
  | .ifCondition => "in if condition"
  | .patternMatch => "in pattern match"
  | .letBinding name => s!"in let binding '{name}'"
  | .typeAnnotation => "in type annotation"
  | .pairElement true => "in first element of pair"
  | .pairElement false => "in second element of pair"
  | .general => ""

end CheckPurpose

/-- Where a constraint originated from -/
inductive ConstraintOrigin where
  /-- From checking an expression against an expected type -/
  | checking (exprKind : ExprKind) (expected : Value) (span : Span)
  /-- From inferring an expression's type -/
  | inferring (exprKind : ExprKind) (span : Span)
  /-- From a function application -/
  | application (fnName : String) (argIndex : Nat) (span : Span)
  /-- From implicit argument insertion -/
  | implicitArg (paramName : String) (fnName : String) (span : Span)
  /-- From a type annotation -/
  | annotation (span : Span)
  /-- From pattern matching -/
  | patternMatch (patternDesc : String) (span : Span)
  /-- From instance resolution -/
  | instanceSearch (className : String) (span : Span)
  /-- From a let binding -/
  | letBinding (name : String) (span : Span)
  /-- From return type checking -/
  | returnType (fnName : String) (span : Span)
  /-- No origin information recorded -/
  | unknown
  deriving Inhabited

namespace ConstraintOrigin

def describeWith (pp : PpContext) : ConstraintOrigin → String
  | .checking expr expected _ =>
      s!"checking `{expr.describe}` against `{Soma.Core.Value.pp pp expected}`"
  | .inferring expr _ => s!"inferring type of `{expr.describe}`"
  | .application fn idx _ => s!"argument {idx + 1} of `{fn}`"
  | .implicitArg param fn _ => s!"implicit `{param}` in call to `{fn}`"
  | .annotation _ => "type annotation"
  | .patternMatch pat _ => s!"pattern `{pat}`"
  | .instanceSearch cls _ => s!"finding instance for `{cls}`"
  | .letBinding name _ => s!"let binding `{name}`"
  | .returnType fn _ => s!"return type of `{fn}`"
  | .unknown => "unknown origin"

def describe (origin : ConstraintOrigin) : String :=
  origin.describeWith PpContext.empty

instance : ToString ConstraintOrigin := ⟨describe⟩

instance : Repr ConstraintOrigin where
  reprPrec o _ := repr o.describe

end ConstraintOrigin

end Soma.Dependent
