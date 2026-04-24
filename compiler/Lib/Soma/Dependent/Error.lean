import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quantity
import Soma.Core.Quote
import Soma.Syntax.Diagnostic
import Soma.Dependent.Suggest

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

/-- Where a constraint originated from -/
inductive ConstraintOrigin where
  /-- From checking an expression against an expected type -/
  | checking (exprDesc : String) (expectedDesc : String) (span : Span)
  /-- From inferring an expression's type -/
  | inferring (exprDesc : String) (span : Span)
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
  deriving Repr, Inhabited

namespace ConstraintOrigin

def span : ConstraintOrigin → Option Span
  | .checking _ _ s => some s
  | .inferring _ s => some s
  | .application _ _ s => some s
  | .implicitArg _ _ s => some s
  | .annotation s => some s
  | .patternMatch _ s => some s
  | .instanceSearch _ s => some s
  | .letBinding _ s => some s
  | .returnType _ s => some s
  | .unknown => none

def describe : ConstraintOrigin → String
  | .checking expr expected _ => s!"checking `{expr}` against `{expected}`"
  | .inferring expr _ => s!"inferring type of `{expr}`"
  | .application fn idx _ => s!"argument {idx + 1} of `{fn}`"
  | .implicitArg param fn _ => s!"implicit `{param}` in call to `{fn}`"
  | .annotation _ => "type annotation"
  | .patternMatch pat _ => s!"pattern `{pat}`"
  | .instanceSearch cls _ => s!"finding instance for `{cls}`"
  | .letBinding name _ => s!"let binding `{name}`"
  | .returnType fn _ => s!"return type of `{fn}`"
  | .unknown => "unknown origin"

end ConstraintOrigin

/-- Information about a constraint in the solving chain -/
structure ConstraintInfo where
  /-- Where this constraint came from -/
  origin : ConstraintOrigin
  /-- Human-readable description of what was being unified -/
  description : String
  /-- The span where this constraint was created -/
  span : Span
  deriving Repr, Inhabited

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
  | escapingVariable (varName : String) (level : DeBruijnLvl) (bindingSite : Option Span)
  deriving Inhabited

namespace UnifyFailure

def message : UnifyFailure → String
  | .headMismatch v1 v2 => s!"cannot unify `{v1}` with `{v2}`"
  | .occursCheck m v => s!"infinite type: `{m}` would contain itself via `{v}`"
  | .rigidMismatch n1 n2 => s!"cannot unify `{n1}` with `{n2}` (both are stuck)"
  | .levelMismatch l1 l2 => s!"universe level mismatch: `{l1}` vs `{l2}`"
  | .rowLabelNotFound label row => s!"field `{label}` not found in `{row}`"
  | .spineLengthMismatch expected actual =>
      s!"expected {expected} arguments, found {actual}"
  | .nonLinearPattern name => s!"variable `{name}` appears multiple times in pattern"
  | .escapingVariable name _ _ =>
      s!"variable `{name}` would escape its scope in the solution"

def detailedMessage : UnifyFailure → String
  | .headMismatch v1 v2 =>
      s!"The types `{v1}` and `{v2}` have incompatible structure and cannot be unified."
  | .occursCheck m v =>
      s!"Solving `{m}` would create an infinite type because `{m}` appears in its own solution `{v}`. " ++
      "This usually means a type annotation is needed to break the cycle."
  | .rigidMismatch n1 n2 =>
      s!"Both `{n1}` and `{n2}` are blocked on unsolved variables or computations, " ++
      "so they cannot be compared. Adding type annotations may help resolve them."
  | .levelMismatch l1 l2 =>
      s!"Universe levels `{l1}` and `{l2}` cannot be unified. " ++
      "This may indicate mixing values and types incorrectly."
  | .rowLabelNotFound label row =>
      s!"The row type `{row}` does not contain a field named `{label}`."
  | .spineLengthMismatch expected actual =>
      s!"Function was applied to {actual} arguments but expected {expected}."
  | .nonLinearPattern name =>
      s!"In pattern unification, each variable must appear exactly once, " ++
      s!"but `{name}` appears multiple times."
  | .escapingVariable name lvl bindingSite =>
      let siteInfo := match bindingSite with
        | some _ => " (see binding site)"
        | none => s!" (at De Bruijn level {lvl.lvl})"
      s!"Variable `{name}`{siteInfo} is not in scope where the solution would be used. " ++
      "This often happens when trying to solve an outer metavariable with an inner-scoped variable."

instance : ToString UnifyFailure := ⟨UnifyFailure.message⟩

end UnifyFailure

/-- Information about an instance search attempt -/
structure InstanceAttempt where
  /-- The instance that was tried -/
  instanceName : String
  /-- Why it failed (if it failed) -/
  failureReason : Option String
  /-- Span of the instance definition -/
  instanceSpan : Option Span
  deriving Repr, Inhabited

/-- Information about constraints related to a metavariable -/
structure MetaConstraintInfo where
  /-- Description of the constraint -/
  description : String
  /-- Where the constraint came from -/
  origin : ConstraintOrigin
  /-- Whether the constraint is currently blocked -/
  isBlocked : Bool
  deriving Repr, Inhabited

/-- Type checking errors with full provenance information -/
inductive TCError where
  /-- Unification failed with full constraint chain -/
  | unificationFailed
      (failure : UnifyFailure)
      (purpose : CheckPurpose)
      (span : Span)
      (constraintChain : Array ConstraintInfo)
      (relatedMetas : Array MetaId)

  /-- Type mismatch in checking mode with inference path -/
  | typeMismatch
      (expected : Value)
      (actual : Value)
      (purpose : CheckPurpose)
      (expectedSpan : Span)
      (actualSpan : Span)
      (inferenceSteps : Array ConstraintInfo)

  /-- Expected a function type (Pi) but got something else -/
  | expectedFunction
      (actual : Value)
      (span : Span)
      (inferredFrom : Option ConstraintOrigin)

  /-- Expected a pair type (Sigma) but got something else -/
  | expectedSigma
      (actual : Value)
      (span : Span)
      (inferredFrom : Option ConstraintOrigin)

  /-- Expected a type (universe) but got something else -/
  | expectedType
      (actual : Value)
      (span : Span)
      (context : Option String)

  /-- Expected a record type -/
  | expectedRecord
      (actual : Value)
      (span : Span)
      (availableFields : Array String)

  /-- Expected a variant type -/
  | expectedVariant
      (actual : Value)
      (span : Span)

  /-- Variable not found in context -/
  | unboundVariable
      (name : String)
      (span : Span)
      (suggestions : Array String)

  /-- Global definition not found -/
  | unboundGlobal
      (name : String)
      (span : Span)
      (suggestions : Array String)

  /-- Field not found in record -/
  | fieldNotFound
      (field : String)
      (recordTy : Value)
      (span : Span)
      (availableFields : Array String)
      (inferredRecordType : Option ConstraintOrigin)

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
      (declSpan : Option Span)

  /-- Unsolved metavariable after elaboration -/
  | unsolvedMeta
      (ty : Value)
      (span : Span)
      (relatedConstraints : Array MetaConstraintInfo)
      (suggestedFix : Option String)

  /-- Unsolved hole -/
  | unsolvedHole
      (name : Option String)
      (ty : Value)
      (span : Span)

  /-- Cannot infer implicit argument -/
  | ambiguousImplicit
      (paramName : String)
      (span : Span)
      (relatedConstraints : Array MetaConstraintInfo)
      (partialInfo : Option String)

  /-- Cannot infer type, need annotation -/
  | cannotInfer
      (reason : String)
      (span : Span)
      (context : Option ConstraintOrigin)

  /-- Internal error (should not happen) -/
  | internalError
      (message : String)
      (span : Span)

  /-- No instance found for a type class constraint -/
  | noInstance
      (classId : Unique)
      (args : Array Value)
      (span : Span)
      (attemptedInstances : Array InstanceAttempt)
      (availableInstances : Array String)

  /-- Cycle detected in instance resolution -/
  | instanceCycle
      (classId : Unique)
      (span : Span)
      (cycleTrace : Array String)

  /-- Instance resolution depth exceeded -/
  | instanceDepthExceeded
      (classId : Unique)
      (span : Span)
      (searchPath : Array String)

  /-- Termination check failed for @[total] function -/
  | terminationCheckFailed
      (fnName : Soma.Core.QualifiedName)
      (reason : String)
      (span : Span)
      (failingCalls : Array Span)
      (triedArguments : Array (Nat × String))

  /-- Partial function used in type index -/
  | partialInTypeIndex
      (fnName : Soma.Core.QualifiedName)
      (span : Span)

  /-- A @[partial] function's declared return type is provably uninhabited -/
  | partialInhabitsUninhabited
      (fnName : Soma.Core.QualifiedName)
      (span : Span)

  /-- Positivity check failed for data type -/
  | positivityViolation
      (typeName : String)
      (reason : String)
      (span : Span)
      (violatingPosition : Option Span)

  /-- Impossible constructor pattern: indices conflict with scrutinee type -/
  | impossiblePattern
      (ctor : String)
      (ctorResultTy : Value)
      (scrutTy : Value)
      (span : Span)

  /-- Pattern match does not cover every inhabitant of the scrutinee type -/
  | nonExhaustiveMatch
      (scrutType : Value)
      (missingPatterns : Array String)
      (span : Span)

  /-- Bodiless definition cannot be derived by ex-falso -/
  | bodilessNotDerivable
      (defName : String)
      (resolvedType : Value)
      (span : Span)

  /-- Pattern clauses declare more parameters than the signature allows -/
  | patternArityMismatch
      (defName : String)
      (sigArity : Nat)
      (clauseArity : Nat)
      (resolvedResultType : Value)
      (span : Span)

  /-- `@[partial]` is not allowed on a `theorem` -/
  | partialTheorem
      (theoremName : String)
      (span : Span)

  /-- A case expression tries to eliminate a Prop-valued scrutinee into a Type-valued motive -/
  | propElimToType
      (scrutineeTy : Value)
      (motiveTy : Value)
      (span : Span)

  /-- Type-class name is used but not in scope -/
  | classNotInScope
      (name : String)
      (span : Span)

  /-- Name used as a type class does not refer to any known class -/
  | unknownClass
      (name : String)
      (span : Span)

  deriving Inhabited

namespace TCError

/-- Get the primary span of an error -/
def span : TCError → Span
  | .unificationFailed _ _ s _ _ => s
  | .typeMismatch _ _ _ _ s _ => s
  | .expectedFunction _ s _ => s
  | .expectedSigma _ s _ => s
  | .expectedType _ s _ => s
  | .expectedRecord _ s _ => s
  | .expectedVariant _ s => s
  | .unboundVariable _ s _ => s
  | .unboundGlobal _ s _ => s
  | .fieldNotFound _ _ s _ _ => s
  | .wrongConstructorArity _ _ _ s => s
  | .quantityMismatch _ _ _ s => s
  | .linearNotUsed _ s => s
  | .linearUsedMultiple _ _ s => s
  | .erasedUsedAtRuntime _ s _ => s
  | .unsolvedMeta _ s _ _ => s
  | .unsolvedHole _ _ s => s
  | .ambiguousImplicit _ s _ _ => s
  | .cannotInfer _ s _ => s
  | .internalError _ s => s
  | .noInstance _ _ s _ _ => s
  | .instanceCycle _ s _ => s
  | .instanceDepthExceeded _ s _ => s
  | .terminationCheckFailed _ _ s _ _ => s
  | .partialInTypeIndex _ s => s
  | .partialInhabitsUninhabited _ s => s
  | .positivityViolation _ _ s _ => s
  | .impossiblePattern _ _ _ s => s
  | .nonExhaustiveMatch _ _ s => s
  | .bodilessNotDerivable _ _ s => s
  | .patternArityMismatch _ _ _ _ s => s
  | .partialTheorem _ s => s
  | .propElimToType _ _ s => s
  | .classNotInScope _ s => s
  | .unknownClass _ s => s

/-- Build secondary labels from constraint chain -/
private def chainToLabels (chain : Array ConstraintInfo) : Array Label :=
  chain.filterMap fun info =>
    if info.span != Span.uninhabited then
      some (Label.secondary info.span info.origin.describe)
    else
      none

/-- Build notes from constraint info -/
private def chainToNotes (chain : Array ConstraintInfo) : Array String :=
  if chain.isEmpty then #[]
  else
    let steps := chain.map fun info => s!"  • {info.origin.describe}"
    #[s!"Constraint chain:\n{String.intercalate "\n" steps.toList}"]

/-- Convert a TCError to a Diagnostic for rich rendering -/
def toDiagnostic : TCError → Diagnostic
  | .unificationFailed failure purpose span chain _metas =>
    let purposeStr := purpose.describe
    let baseMsg := match failure with
      | .headMismatch _ _ => "type mismatch"
      | .occursCheck _ _ => "infinite type"
      | .rigidMismatch _ _ => "unification stuck"
      | .escapingVariable _ _ _ => "scope error"
      | .levelMismatch _ _ => "universe level mismatch"
      | _ => "unification failed"
    let msg := if purposeStr.isEmpty
      then baseMsg
      else s!"{baseMsg} {purposeStr}"
    let secondaryLabels := chainToLabels chain
    let notes := if chain.isEmpty then #[failure.detailedMessage]
                 else chainToNotes chain ++ #[failure.detailedMessage]
    { severity := .error
    , code := some "E1001"
    , message := msg
    , primaryLabel := Label.primary span failure.message
    , secondaryLabels := secondaryLabels
    , notes := notes
    , help := some "add type annotations to help the compiler infer types"
    }

  | .typeMismatch expected actual purpose expectedSpan actualSpan steps =>
    let purposeStr := purpose.describe
    let msg := if purposeStr.isEmpty
      then "type mismatch"
      else s!"type mismatch {purposeStr}"
    let baseLabels := #[Label.secondary expectedSpan "expected type from here"]
    let stepLabels := chainToLabels steps
    let help : Option String := match purpose with
      | .functionBody fn =>
        some s!"change `{fn}`'s return type or the body to match"
      | .functionArg fn idx =>
        some s!"pass a value of type `{expected}` as argument #{idx + 1} to `{fn}`"
      | .ifCondition => some "`if` conditions must have type `Bool`"
      | .ifBranches => some "both branches of an `if` must have the same type"
      | .caseArms => some "every arm of a `case` must produce the same type"
      | .patternMatch => some "the pattern doesn't match the scrutinee's type"
      | .letBinding nm => some s!"the value bound to `{nm}` doesn't match its annotation"
      | .typeAnnotation => some "the expression doesn't match its type annotation"
      | _ => none
    { severity := .error
    , code := some "E1002"
    , message := msg
    , primaryLabel := Label.primary actualSpan s!"expected `{expected}`, found `{actual}`"
    , secondaryLabels := baseLabels ++ stepLabels
    , notes := chainToNotes steps
    , help
    }

  | .expectedFunction actual span origin =>
    let originNote := match origin with
      | some o => #[s!"type was inferred from: {o.describe}"]
      | none => #[]
    Diagnostic.error "expected function type" span s!"`{actual}` is not a function"
      |>.withCode "E1003"
      |>.withNote "function application requires a function type (Π-type)"
      |>.withHelp "did you mean field access (`.x`) or forget parentheses?"
      |> fun d => { d with notes := d.notes ++ originNote }

  | .expectedSigma actual span origin =>
    let originNote := match origin with
      | some o => #[s!"type was inferred from: {o.describe}"]
      | none => #[]
    Diagnostic.error "expected pair type" span s!"`{actual}` is not a pair"
      |>.withCode "E1004"
      |>.withNote "pair projection requires a dependent pair type (Σ-type)"
      |>.withHelp "construct the pair with `(x, y)` before projecting with `.1` or `.2`"
      |> fun d => { d with notes := d.notes ++ originNote }

  | .expectedType actual span context =>
    let contextNote := match context with
      | some ctx => s!" ({ctx})"
      | none => ""
    Diagnostic.error "expected a type" span s!"`{actual}` is not a type{contextNote}"
      |>.withCode "E1005"
      |>.withNote "types have type `Type`"
      |>.withHelp "only type-level expressions are allowed here"

  | .expectedRecord actual span availableFields =>
    let fieldsNote := if availableFields.isEmpty then #[]
      else #[s!"available fields: {String.intercalate ", " availableFields.toList}"]
    let help := "field access (`.x`) and record literals require a record type"
    Diagnostic.error "expected record type" span s!"`{actual}` is not a record"
      |>.withCode "E1006"
      |>.withHelp help
      |> fun d => { d with notes := d.notes ++ fieldsNote }

  | .expectedVariant actual span =>
    Diagnostic.error "expected variant type" span s!"`{actual}` is not a variant"
      |>.withCode "E1007"
      |>.withHelp "variant injection (`.Label`) requires a variant type"

  | .unboundVariable name span suggestions =>
    let help := match Soma.Dependent.Suggest.formatSuggestions suggestions with
      | some hint => hint
      | none => s!"bind `{name}` with `let` or add a parameter, or check imports"
    Diagnostic.error s!"unknown variable `{name}`" span "not found in scope"
      |>.withCode "E1008"
      |>.withHelp help

  | .unboundGlobal name span suggestions =>
    let help := match Soma.Dependent.Suggest.formatSuggestions suggestions with
      | some hint => hint
      | none => s!"define `{name}` or add a `use` import that brings it into scope"
    Diagnostic.error s!"unknown definition `{name}`" span "not found"
      |>.withCode "E1009"
      |>.withHelp help

  | .fieldNotFound field recordTy span availableFields origin =>
    let fieldsNote := if availableFields.isEmpty then ""
      else s!"\navailable fields: {String.intercalate ", " availableFields.toList}"
    let originNote := match origin with
      | some o => #[s!"record type inferred from: {o.describe}"]
      | none => #[]
    let diag := Diagnostic.error s!"field `{field}` not found" span
        s!"not in `{recordTy}`{fieldsNote}"
      |>.withCode "E1010"
    let withHelp := match Soma.Dependent.Suggest.formatSuggestions
        (Soma.Dependent.Suggest.suggestSimilar field availableFields) with
      | some hint => diag.withHelp hint
      | none => diag
    { withHelp with notes := withHelp.notes ++ originNote }

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

  | .erasedUsedAtRuntime varName span declSpan =>
    let secondaryLabels := match declSpan with
      | some ds => #[Label.secondary ds s!"`{varName}` declared as erased (quantity `0`) here"]
      | none => #[]
    { severity := .error
    , code := some "E1016"
    , message := s!"erased variable `{varName}` used at runtime"
    , primaryLabel := Label.primary span "erased variable used here"
    , secondaryLabels := secondaryLabels
    , notes := #["variables with quantity `0` are erased and exist only for type checking"]
    , help := some "change the quantity to `ω` or `1` if runtime access is needed"
    }

  | .unsolvedMeta ty span relatedConstraints suggestedFix =>
    let constraintNotes := if relatedConstraints.isEmpty then #[]
      else
        let items := relatedConstraints.map fun c =>
          let blockedStr := if c.isBlocked then " (blocked)" else ""
          s!"  • {c.description}{blockedStr}"
        #[s!"Related constraints:\n{String.intercalate "\n" items.toList}"]
    let help := suggestedFix.getD "add a type annotation to help inference"
    Diagnostic.error "could not infer a type here" span s!"expected a value of type `{ty}`"
      |>.withCode "E1017"
      |>.withHelp help
      |> fun d => { d with notes := d.notes ++ constraintNotes }

  | .unsolvedHole name ty span =>
    let nameStr := name.getD "_"
    Diagnostic.error s!"unsolved hole `?{nameStr}`" span s!"has type `{ty}`"
      |>.withCode "E1018"

  | .ambiguousImplicit paramName span relatedConstraints partialInfo =>
    let constraintNotes := if relatedConstraints.isEmpty then #[]
      else
        let items := relatedConstraints.map fun c => s!"  • {c.description}"
        #[s!"Constraints involving `{paramName}`:\n{String.intercalate "\n" items.toList}"]
    let partialNote := match partialInfo with
      | some info => #[s!"Partial information available: {info}"]
      | none => #[]
    Diagnostic.error s!"cannot infer implicit `{paramName}`" span "not enough information"
      |>.withCode "E1019"
      |>.withHelp s!"provide explicit argument: @{paramName} = <value>"
      |> fun d => { d with notes := d.notes ++ constraintNotes ++ partialNote }

  | .cannotInfer reason span context =>
    let contextNote := match context with
      | some o => #[s!"while {o.describe}"]
      | none => #[]
    Diagnostic.error "cannot infer type" span reason
      |>.withCode "E1020"
      |>.withHelp "add a type annotation"
      |> fun d => { d with notes := d.notes ++ contextNote }

  | .internalError message span =>
    Diagnostic.error s!"internal error: {message}" span
      |>.withCode "E1099"
      |>.withNote "this is a bug in the compiler, please report it"

  | .noInstance classId _args span attemptedInstances availableInstances =>
    let className := classId.original
    let attemptNotes := if attemptedInstances.isEmpty then #[]
      else
        let items := attemptedInstances.map fun attempt =>
          match attempt.failureReason with
          | some reason => s!"  • {attempt.instanceName}: {reason}"
          | none => s!"  • {attempt.instanceName}: matched"
        #[s!"Tried instances:\n{String.intercalate "\n" items.toList}"]
    let availableNote := if availableInstances.isEmpty then #[]
      else #[s!"Available instances for `{className}`: {String.intercalate ", " availableInstances.toList}"]
    Diagnostic.error s!"no instance for `{className}`" span
        "could not find a matching instance"
      |>.withCode "E1021"
      |>.withHelp s!"add an instance for `{className}` or provide one explicitly"
      |> fun d => { d with notes := d.notes ++ attemptNotes ++ availableNote }

  | .instanceCycle classId span cycleTrace =>
    let className := classId.original
    let cycleNote := if cycleTrace.isEmpty then #[]
      else #[s!"Resolution cycle:\n{String.intercalate " → " cycleTrace.toList}"]
    Diagnostic.error s!"cycle in instance resolution for `{className}`" span
        "instance resolution would loop forever"
      |>.withCode "E1022"
      |> fun d => { d with notes := #["instance constraints form a cycle"] ++ cycleNote }

  | .instanceDepthExceeded classId span searchPath =>
    let className := classId.original
    let pathNote := if searchPath.isEmpty then #[]
      else #[s!"Search path (truncated):\n{String.intercalate " → " searchPath.toList}"]
    Diagnostic.error s!"instance resolution depth exceeded for `{className}`" span
        "search exceeded maximum depth"
      |>.withCode "E1023"
      |>.withHelp "simplify instance constraints or increase search depth"
      |> fun d => { d with notes := d.notes ++ pathNote }

  | .terminationCheckFailed fnName reason span failingCalls triedArguments =>
    let callLabels := failingCalls.map fun s => Label.secondary s "recursive call here"
    let triedNote := if triedArguments.isEmpty then #[]
      else
        let items := triedArguments.map fun (idx, reason) =>
          s!"  • argument {idx + 1}: {reason}"
        #[s!"Termination analysis:\n{String.intercalate "\n" items.toList}"]
    let baseNote :=
      "every definition is checked for termination"
    { severity := .error
    , code := some "E1026"
    , message := s!"termination check failed for `{fnName.display}`"
    , primaryLabel := Label.primary span reason
    , secondaryLabels := callLabels
    , notes := #[baseNote] ++ triedNote
    , help := some
        "ensure recursive calls are on structurally smaller arguments, \
         or mark the definition `@[partial]` (note: partial functions are \
         opaque and may not inhabit uninhabited types)"
    }

  | .partialInTypeIndex fnName span =>
    Diagnostic.error s!"partial function `{fnName.display}` used in type index" span
        "only total functions can appear in type indices"
      |>.withCode "E1027"
      |>.withNote "type indices must be computable to keep type checking decidable"
      |>.withHelp s!"mark `{fnName.display}` as @[total] or use a different function"

  | .partialInhabitsUninhabited fnName span =>
    Diagnostic.error
        s!"`@[partial]` definition `{fnName.display}` cannot inhabit an uninhabited type" span
        "partial functions never produce a concrete value"
      |>.withCode "E1029"
      |>.withNote
        "`@[partial]` is only valid when the return type has at least one constructor"
      |>.withHelp
        "make the definition total (its recursion must be provably well-founded)"

  | .positivityViolation typeName reason span violatingPosition =>
    let secondaryLabels := match violatingPosition with
      | some vs => #[Label.secondary vs "negative occurrence here"]
      | none => #[]
    { severity := .error
    , code := some "E1028"
    , message := s!"positivity check failed for `{typeName}`"
    , primaryLabel := Label.primary span reason
    , secondaryLabels := secondaryLabels
    , notes := #["data types must be strictly positive to prevent paradoxes"]
    , help := some "ensure the type only appears in positive positions in constructors"
    }

  | .impossiblePattern ctor ctorResultTy scrutTy span =>
    Diagnostic.error s!"impossible pattern `{ctor}`" span
        s!"constructor produces `{ctorResultTy}`, but matching against `{scrutTy}`"
      |>.withCode "E1030"
      |>.withNote "the constructor's index does not match the scrutinee type"
      |>.withHelp "remove this pattern — it can never match"

  | .nonExhaustiveMatch scrutType missing span =>
    let primaryDetail :=
      if missing.isEmpty then
        "pattern match does not cover every case"
      else
        let quoted := missing.toList.map (s!"`{·}`")
        s!"missing: {String.intercalate ", " quoted}"
    let notes :=
      if missing.isEmpty then
        #[s!"scrutinee has type `{scrutType}`"]
      else
        #[ s!"scrutinee has type `{scrutType}`"
         , "each listed shape can occur at runtime but no arm matches it"
         ]
    { severity := .error
    , code := some "E1031"
    , message := "non-exhaustive pattern match"
    , primaryLabel := Label.primary span primaryDetail
    , secondaryLabels := #[]
    , notes := notes
    , help := some "add an arm for each listed case, or a catch-all variable / `_` pattern"
    }

  | .bodilessNotDerivable name resolvedType span =>
    { severity := .error
    , code := some "E1032"
    , message := s!"bodiless definition '{name}' is not derivable"
    , primaryLabel := Label.primary span "no explicit parameter with an uninhabited type"
    , secondaryLabels := #[]
    , notes := #[
        s!"after reduction, the declared type is `{resolvedType}`",
        "a bodiless def is a proof-by-absurdity: it requires at least one explicit parameter whose type has no constructors (e.g. `Never`), so the body is vacuously unreachable"
      ]
    , help := some "if you meant to prove that the declared type is unprovable, rewrite as `T -> Never`; otherwise provide a body (`:=` or `|` clauses) or mark as @[intrinsic]/@[extern]"
    }

  | .patternArityMismatch name sigArity clauseArity resultTy span =>
    let patWord := if clauseArity == 1 then "pattern" else "patterns"
    let paramWord := if sigArity == 1 then "parameter" else "parameters"
    Diagnostic.error s!"arity mismatch in `{name}`" span
        s!"each clause has {clauseArity} {patWord}, but the signature exposes only {sigArity} explicit {paramWord}"
      |>.withCode "E1035"
      |>.withNote s!"after the {sigArity} explicit {paramWord}, the result type is not a function: `{resultTy}`"
      |>.withHelp (
        if clauseArity > sigArity then
          s!"remove {clauseArity - sigArity} pattern column(s), or extend the signature with more `->`"
        else
          "add patterns for the missing parameter(s), or adjust the signature"
      )

  | .partialTheorem name span =>
    Diagnostic.error
        s!"theorem `{name}` cannot be marked `@[partial]`" span
        "a partial proof is not a proof"
      |>.withCode "E1037"
      |>.withNote
        "theorems are required to be total"
      |>.withHelp
        "drop `@[partial]`, make the recursion structurally decreasing, \
         or restate the declaration as a `def` if it's really runtime code"

  | .propElimToType scrutTy motiveTy span =>
    Diagnostic.error
        "cannot eliminate this Prop into a Type" span
        s!"scrutinee of type `{scrutTy}` is a proposition"
      |>.withCode "E1038"
      |>.withNote
        s!"the expected motive `{motiveTy}` lives in `Type`, but \
           propositions can only be observed from another proposition"
      |>.withHelp
        "either change the result type so the match produces a \
         proposition, or rework the Prop so it becomes small \
         (drop constructors / lift a field from `Type` to `Prop`)"

  | .classNotInScope name span =>
    { severity := .error
    , code := some "E1033"
    , message := s!"type class `{name}` is not in scope"
    , primaryLabel := Label.primary span s!"`{name}` not imported"
    , secondaryLabels := #[]
    , notes := #[s!"the class exists in a loaded module but isn't visible here"]
    , help := some ("add a `use` clause that imports `" ++ name ++
        "`, e.g. `use <module>::{" ++ name ++ "}`")
    }

  | .unknownClass name span =>
    { severity := .error
    , code := some "E1034"
    , message := s!"unknown type class `{name}`"
    , primaryLabel := Label.primary span s!"`{name}` is not a class"
    , secondaryLabels := #[]
    , notes := #[s!"no class named `{name}` is defined in this module or any of its dependencies"]
    , help := some "check for typos, or declare the class with `class ... where ...`"
    }

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
  | totalityUnknown (fnName : Soma.Core.QualifiedName) (span : Span)
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
