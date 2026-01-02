import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quantity
import Soma.Core.Quote
import Soma.Syntax.Diagnostic
import Soma.Unique
import Soma.Metal.Name

namespace Soma.Dependent

open Soma (Unique)
open Soma.Core
open Soma.Syntax (Span Diagnostic Label)

/-- The purpose of a type check - provides context for error messages -/
inductive CheckPurpose where
  /-- Checking function body against declared return type -/
  | functionBody (fnName : String)
  /-- Checking argument against parameter type -/
  | functionArg (fnName : String) (argIndex : Nat)
  /-- Checking if condition against Bool -/
  | ifCondition
  /-- Checking if branches have same type -/
  | ifBranches
  /-- Checking case arm bodies have same type -/
  | caseArms
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
  | .ifBranches => "in if/else branches"
  | .caseArms => "in case expression arms"
  | .patternMatch => "in pattern match"
  | .letBinding name => s!"in let binding '{name}'"
  | .typeAnnotation => "in type annotation"
  | .pairElement true => "in first element of pair"
  | .pairElement false => "in second element of pair"
  | .general => ""

end CheckPurpose

/-- Reasons why unification might fail -/
inductive UnifyFailure where
  /-- Head mismatch -/
  | headMismatch (v1 v2 : Value)
  /-- Occurs check failed: metavariable appears in its solution -/
  | occursCheck (metaId : MetaId) (value : Value)
  /-- Rigid-rigid mismatch: two different stuck terms -/
  | rigidMismatch (n1 n2 : Neutral)
  /-- Universe level mismatch -/
  | levelMismatch (l1 l2 : Level)
  /-- Row label not found during rewriting -/
  | rowLabelNotFound (label : String) (row : Value)
  /-- Spine length mismatch in pattern unification -/
  | spineLengthMismatch (expected actual : Nat)
  /-- Non-linear pattern: variable appears multiple times -/
  | nonLinearPattern (varName : String)
  /-- Solution would reference out-of-scope variable -/
  | escapingVariable (varName : String) (level : DeBruijnLvl)
  deriving Inhabited

namespace UnifyFailure

def message : UnifyFailure → String
  | .headMismatch v1 v2 => s!"type mismatch: cannot unify `{v1}` with `{v2}`"
  | .occursCheck m v => s!"occurs check: `{m}` appears in `{v}`"
  | .rigidMismatch n1 n2 => s!"cannot unify `{n1}` with `{n2}`"
  | .levelMismatch l1 l2 => s!"universe level mismatch: `{l1}` vs `{l2}`"
  | .rowLabelNotFound label row => s!"field `{label}` not found in `{row}`"
  | .spineLengthMismatch expected actual =>
      s!"expected {expected} arguments, found {actual}"
  | .nonLinearPattern name => s!"variable `{name}` appears multiple times in pattern"
  | .escapingVariable name lvl =>
      s!"variable `{name}` (level {lvl.lvl}) would escape its scope"

instance : ToString UnifyFailure := ⟨UnifyFailure.message⟩

end UnifyFailure

/-- Type checking errors -/
inductive TCError where
  /-- Unification failed -/
  | unificationFailed
      (failure : UnifyFailure)
      (purpose : CheckPurpose)
      (span : Span)

  /-- Type mismatch in checking mode -/
  | typeMismatch
      (expected : Value)
      (actual : Value)
      (purpose : CheckPurpose)
      (expectedSpan : Span)
      (actualSpan : Span)

  /-- Expected a function type (Pi) but got something else -/
  | expectedFunction
      (actual : Value)
      (span : Span)

  /-- Expected a pair type (Sigma) but got something else -/
  | expectedSigma
      (actual : Value)
      (span : Span)

  /-- Expected a type (universe) but got something else -/
  | expectedType
      (actual : Value)
      (span : Span)

  /-- Expected a record type -/
  | expectedRecord
      (actual : Value)
      (span : Span)

  /-- Expected a variant type -/
  | expectedVariant
      (actual : Value)
      (span : Span)

  /-- Variable not found in context -/
  | unboundVariable
      (name : String)
      (span : Span)

  /-- Global definition not found -/
  | unboundGlobal
      (name : String)
      (span : Span)

  /-- Field not found in record -/
  | fieldNotFound
      (field : String)
      (recordTy : Value)
      (span : Span)

  /-- Constructor not found in data type -/
  | constructorNotFound
      (ctor : String)
      (dataTy : Value)
      (span : Span)

  /-- Wrong number of arguments to constructor -/
  | wrongConstructorArity
      (ctor : String)
      (expected : Nat)
      (actual : Nat)
      (span : Span)

  /-- Quantity mismatch: variable used incorrectly -/
  | quantityMismatch
      (expected : Quantity)
      (actual : Quantity)
      (varName : String)
      (span : Span)

  /-- Linear variable not used -/
  | linearNotUsed
      (varName : String)
      (declSpan : Span)

  /-- Linear variable used more than once -/
  | linearUsedMultiple
      (varName : String)
      (firstUse : Span)
      (secondUse : Span)

  /-- Erased variable used at runtime -/
  | erasedUsedAtRuntime
      (varName : String)
      (span : Span)

  /-- Unsolved metavariable after elaboration -/
  | unsolvedMeta
      (id : MetaId)
      (ty : Value)
      (span : Span)

  /-- Unsolved hole -/
  | unsolvedHole
      (name : Option String)
      (ty : Value)
      (span : Span)

  /-- Cannot infer implicit argument -/
  | ambiguousImplicit
      (paramName : String)
      (span : Span)

  /-- Cannot infer type, need annotation -/
  | cannotInfer
      (reason : String)
      (span : Span)

  /-- Internal error (should not happen) -/
  | internalError
      (message : String)
      (span : Span)

  /-- No instance found for a type class constraint -/
  | noInstance
      (classId : Unique)
      (args : Array Value)
      (span : Span)

  /-- Cycle detected in instance resolution -/
  | instanceCycle
      (classId : Unique)
      (span : Span)

  /-- Instance resolution depth exceeded -/
  | instanceDepthExceeded
      (classId : Unique)
      (span : Span)

  /-- Overlapping instances found -/
  | overlappingInstances
      (classId : Unique)
      (instanceIds : Array Unique)
      (span : Span)

  /-- Unknown type class -/
  | unknownClass
      (classId : Unique)
      (span : Span)

  /-- Termination check failed for @[total] function -/
  | terminationCheckFailed
      (fnName : Soma.Metal.Name)
      (reason : String)
      (span : Span)

  /-- Partial function used in type index -/
  | partialInTypeIndex
      (fnName : Soma.Metal.Name)
      (span : Span)

  /-- Positivity check failed for data type -/
  | positivityViolation
      (typeName : String)
      (reason : String)
      (span : Span)

  /-- Recursive call not structurally decreasing -/
  | nonStructuralRecursion
      (fnName : Soma.Metal.Name)
      (callSpan : Span)

  deriving Inhabited

namespace TCError

/-- Get the primary span of an error -/
def span : TCError → Span
  | .unificationFailed _ _ s => s
  | .typeMismatch _ _ _ _ s => s
  | .expectedFunction _ s => s
  | .expectedSigma _ s => s
  | .expectedType _ s => s
  | .expectedRecord _ s => s
  | .expectedVariant _ s => s
  | .unboundVariable _ s => s
  | .unboundGlobal _ s => s
  | .fieldNotFound _ _ s => s
  | .constructorNotFound _ _ s => s
  | .wrongConstructorArity _ _ _ s => s
  | .quantityMismatch _ _ _ s => s
  | .linearNotUsed _ s => s
  | .linearUsedMultiple _ _ s => s
  | .erasedUsedAtRuntime _ s => s
  | .unsolvedMeta _ _ s => s
  | .unsolvedHole _ _ s => s
  | .ambiguousImplicit _ s => s
  | .cannotInfer _ s => s
  | .internalError _ s => s
  | .noInstance _ _ s => s
  | .instanceCycle _ s => s
  | .instanceDepthExceeded _ s => s
  | .overlappingInstances _ _ s => s
  | .unknownClass _ s => s
  | .terminationCheckFailed _ _ s => s
  | .partialInTypeIndex _ s => s
  | .positivityViolation _ _ s => s
  | .nonStructuralRecursion _ s => s

/-- Convert a TCError to a Diagnostic for rich rendering -/
def toDiagnostic : TCError → Diagnostic
  | .unificationFailed failure purpose span =>
    let purposeStr := purpose.describe
    let baseMsg := match failure with
      | .headMismatch _ _ => "type mismatch"
      | _ => "unification failed"
    let msg := if purposeStr.isEmpty
      then baseMsg
      else s!"{baseMsg} {purposeStr}"
    Diagnostic.error msg span failure.message
      |>.withCode "E1001"

  | .typeMismatch expected actual purpose expectedSpan actualSpan =>
    let purposeStr := purpose.describe
    let msg := if purposeStr.isEmpty
      then "type mismatch"
      else s!"type mismatch {purposeStr}"
    { severity := .error
    , code := some "E1002"
    , message := msg
    , primaryLabel := Label.primary actualSpan s!"expected `{expected}`, found `{actual}`"
    , secondaryLabels := #[Label.secondary expectedSpan "expected due to this"]
    , notes := #[]
    , help := none
    }

  | .expectedFunction actual span =>
    Diagnostic.error "expected function type" span s!"`{actual}` is not a function"
      |>.withCode "E1003"
      |>.withNote "function application requires a function type (Π-type)"

  | .expectedSigma actual span =>
    Diagnostic.error "expected pair type" span s!"`{actual}` is not a pair"
      |>.withCode "E1004"
      |>.withNote "pair projection requires a dependent pair type (Σ-type)"

  | .expectedType actual span =>
    Diagnostic.error "expected a type" span s!"`{actual}` is not a type"
      |>.withCode "E1005"
      |>.withNote "types have type `Type`"

  | .expectedRecord actual span =>
    Diagnostic.error "expected record type" span s!"`{actual}` is not a record"
      |>.withCode "E1006"

  | .expectedVariant actual span =>
    Diagnostic.error "expected variant type" span s!"`{actual}` is not a variant"
      |>.withCode "E1007"

  | .unboundVariable name span =>
    Diagnostic.error s!"unknown variable `{name}`" span "not found in scope"
      |>.withCode "E1008"
      |>.withHelp s!"did you mean to define `{name}`?"

  | .unboundGlobal name span =>
    Diagnostic.error s!"unknown definition `{name}`" span "not found"
      |>.withCode "E1009"
      |>.withHelp "check that the definition is imported"

  | .fieldNotFound field recordTy span =>
    Diagnostic.error s!"field `{field}` not found" span s!"not in `{recordTy}`"
      |>.withCode "E1010"

  | .constructorNotFound ctor dataTy span =>
    Diagnostic.error s!"constructor `{ctor}` not found" span s!"not in `{dataTy}`"
      |>.withCode "E1011"

  | .wrongConstructorArity ctor expected actual span =>
    let args := if expected == 1 then "argument" else "arguments"
    Diagnostic.error s!"wrong number of arguments to `{ctor}`" span
        s!"expected {expected} {args}, found {actual}"
      |>.withCode "E1012"

  | .quantityMismatch expected actual varName span =>
    Diagnostic.error s!"quantity mismatch for `{varName}`" span
        s!"declared as `{expected}`, used as `{actual}`"
      |>.withCode "E1013"
      |>.withNote s!"`0` = erased, `1` = linear, `ω` = unrestricted"

  | .linearNotUsed varName declSpan =>
    Diagnostic.error s!"linear variable `{varName}` not used" declSpan
        "must be used exactly once"
      |>.withCode "E1014"
      |>.withHelp "use the variable or change its quantity to `0` or `ω`"

  | .linearUsedMultiple varName firstUse secondUse =>
    { severity := .error
    , code := some "E1015"
    , message := s!"linear variable `{varName}` used multiple times"
    , primaryLabel := Label.primary secondUse "used again here"
    , secondaryLabels := #[Label.secondary firstUse "first used here"]
    , notes := #["linear variables (quantity `1`) must be used exactly once"]
    , help := some "change the quantity to `ω` for unrestricted use"
    }

  | .erasedUsedAtRuntime varName span =>
    Diagnostic.error s!"erased variable `{varName}` used at runtime" span
        "erased variables cannot be used in runtime code"
      |>.withCode "E1016"
      |>.withNote "variables with quantity `0` are erased and exist only for type checking"

  | .unsolvedMeta id ty span =>
    Diagnostic.error s!"unsolved metavariable `{id}`" span s!"has type `{ty}`"
      |>.withCode "E1017"
      |>.withHelp "add a type annotation to help inference"

  | .unsolvedHole name ty span =>
    let nameStr := name.getD "_"
    Diagnostic.error s!"unsolved hole `?{nameStr}`" span s!"has type `{ty}`"
      |>.withCode "E1018"

  | .ambiguousImplicit paramName span =>
    Diagnostic.error s!"cannot infer implicit `{paramName}`" span "ambiguous"
      |>.withCode "E1019"
      |>.withHelp s!"provide explicit argument with @{paramName}"

  | .cannotInfer reason span =>
    Diagnostic.error "cannot infer type" span reason
      |>.withCode "E1020"
      |>.withHelp "add a type annotation"

  | .internalError message span =>
    Diagnostic.error s!"internal error: {message}" span
      |>.withCode "E1099"
      |>.withNote "this is a bug in the compiler, please report it"

  | .noInstance classId _args span =>
    let className := classId.original
    Diagnostic.error s!"no instance for `{className}`" span
        "could not find a matching instance"
      |>.withCode "E1021"
      |>.withHelp s!"add an instance for `{className}` or provide one explicitly"

  | .instanceCycle classId span =>
    let className := classId.original
    Diagnostic.error s!"cycle in instance resolution for `{className}`" span
        "instance resolution would loop forever"
      |>.withCode "E1022"
      |>.withNote "instance constraints form a cycle"

  | .instanceDepthExceeded classId span =>
    let className := classId.original
    Diagnostic.error s!"instance resolution depth exceeded for `{className}`" span
        "search exceeded maximum depth"
      |>.withCode "E1023"
      |>.withHelp "simplify instance constraints or increase search depth"

  | .overlappingInstances classId instanceIds span =>
    let className := classId.original
    let names := instanceIds.toList.map (·.original) |> String.intercalate ", "
    Diagnostic.error s!"overlapping instances for `{className}`" span
        s!"found multiple matching instances: {names}"
      |>.withCode "E1024"
      |>.withNote "exactly one instance must match"

  | .unknownClass classId span =>
    let className := classId.original
    Diagnostic.error s!"unknown type class `{className}`" span "class not defined"
      |>.withCode "E1025"
      |>.withHelp s!"define class `{className}` or check the spelling"

  | .terminationCheckFailed fnName reason span =>
    Diagnostic.error s!"termination check failed for `{fnName.display}`" span reason
      |>.withCode "E1026"
      |>.withNote "functions marked @[total] must be proven to terminate"
      |>.withHelp "ensure recursive calls are on structurally smaller arguments"

  | .partialInTypeIndex fnName span =>
    Diagnostic.error s!"partial function `{fnName.display}` used in type index" span
        "only total functions can appear in type indices"
      |>.withCode "E1027"
      |>.withNote "type indices must be computable to keep type checking decidable"
      |>.withHelp s!"mark `{fnName.display}` as @[total] or use a different function"

  | .positivityViolation typeName reason span =>
    Diagnostic.error s!"positivity check failed for `{typeName}`" span reason
      |>.withCode "E1028"
      |>.withNote "data types must be strictly positive to prevent paradoxes"
      |>.withHelp "ensure the type only appears in positive positions in constructors"

  | .nonStructuralRecursion fnName callSpan =>
    Diagnostic.error s!"non-structural recursion in `{fnName.display}`" callSpan
        "recursive call is not on a structurally smaller argument"
      |>.withCode "E1029"
      |>.withNote "for @[total] functions, each recursive call must decrease some argument"
      |>.withHelp "use pattern matching to obtain structurally smaller subterms"

instance : ToString TCError where
  toString err := err.toDiagnostic.message

end TCError

/-- Collection of type checking errors -/
abbrev TCErrors := Array TCError

namespace TCErrors

/-- Convert all errors to diagnostics -/
def toDiagnostics (errs : TCErrors) : Array Diagnostic :=
  errs.map TCError.toDiagnostic

/-- Check if there are any errors -/
def hasErrors (errs : TCErrors) : Bool :=
  !errs.isEmpty

end TCErrors

/-- A warning (non-fatal issue) -/
inductive TCWarning where
  /-- Unused variable -/
  | unusedVariable (name : String) (span : Span)
  /-- Implicit argument could be made explicit -/
  | unnecessaryImplicit (name : String) (span : Span)
  /-- Redundant type annotation -/
  | redundantAnnotation (span : Span)
  /-- Unreachable code -/
  | unreachableCode (span : Span)
  /-- Totality status unknown for function -/
  | totalityUnknown (fnName : Soma.Metal.Name) (span : Span)
  deriving Inhabited

namespace TCWarning

def toDiagnostic : TCWarning → Diagnostic
  | .unusedVariable name span =>
    Diagnostic.warning s!"unused variable `{name}`" span
      |>.withCode "W1001"
  | .unnecessaryImplicit name span =>
    Diagnostic.warning s!"implicit `{name}` could be explicit" span
      |>.withCode "W1002"
  | .redundantAnnotation span =>
    Diagnostic.warning "redundant type annotation" span
      |>.withCode "W1003"
  | .unreachableCode span =>
    Diagnostic.warning "unreachable code" span
      |>.withCode "W1004"
  | .totalityUnknown fnName span =>
    Diagnostic.warning s!"totality of `{fnName.display}` could not be determined" span
      |>.withCode "W1005"

instance : ToString TCWarning where
  toString w := w.toDiagnostic.message

end TCWarning

end Soma.Dependent
