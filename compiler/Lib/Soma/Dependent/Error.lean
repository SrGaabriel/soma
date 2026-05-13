import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quantity
import Soma.Core.Quote
import Soma.Diagnostic
import Soma.Dependent.Suggest

namespace Soma.Dependent

open Soma (Unique DiagContext Phase severity)
open Soma.Core
open Soma.Syntax (Span)
open Psychopomp (Diagnostic Label LabelStyle)

private def elabSev : Psychopomp.Severity := severity .elaborate

/-- Build a primary label -/
private def mkPrimary (ctx : DiagContext) (span : Span) (msg : String) : Label :=
  ctx.primary span msg

/-- Build a support label  -/
private def mkSupport (ctx : DiagContext) (span : Span) (msg : String) : Label :=
  ctx.support span msg

/-- Build a primary label inside a named link group -/
private def mkLinkedPrimary (ctx : DiagContext) (span : Span) (msg : String)
    (linkGroup : String) : Label :=
  ctx.label span msg { LabelStyle.error with linkGroup := some linkGroup }

/-- Build a support label inside a named link group -/
private def mkLinkedSupport (ctx : DiagContext) (span : Span) (msg : String)
    (linkGroup : String) : Label :=
  ctx.label span msg { LabelStyle.support with linkGroup := some linkGroup }

/-- Assemble a typical elaborator diagnostic -/
private def mkDiag (ctx : DiagContext) (code : String) (message : String)
    (primarySpan : Span) (primaryMsg : String := message)
    (secondary : Array Label := #[]) (notes : List String := [])
    (help : Option String := none)
    (audience : List String := [])
    (certainty : Psychopomp.Certainty := .certain)
    (fixes : List Psychopomp.QuickFix := []) : Diagnostic :=
  { severity :=
      { elabSev with audiences := audience, certainty }
    code := some code
    message
    primary := mkPrimary ctx primarySpan primaryMsg
    secondary := secondary.toList
    notes
    helps := match help with | some h => [h] | none => []
    fixes }

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

  /-- Compiler bug -/
  | compilerBug
      (message : String)
      (span : Span)

  /-- Feature the compiler doesn't yet handle -/
  | unhandledFeature
      (feature : String)
      (span : Span)

  /-- The user wrote something well-formed-but-meaningless -/
  | userTriggered
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

  /-- An instance declaration provides a `def` whose name is not a method of the class -/
  | unknownInstanceMethod
      (className : String)
      (methodName : String)
      (knownMethods : Array String)
      (span : Span)

  /-- An instance declaration is missing one or more methods required by the class -/
  | missingInstanceMethods
      (className : String)
      (missing : Array String)
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
  | .compilerBug _ s => s
  | .unhandledFeature _ s => s
  | .userTriggered _ s => s
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
  | .unknownInstanceMethod _ _ _ s => s
  | .missingInstanceMethods _ _ s => s

/-- Build secondary labels from constraint chain -/
private def chainToLabels (ctx : DiagContext) (chain : Array ConstraintInfo) : Array Label :=
  chain.filterMap fun info =>
    if info.span != Span.uninhabited then
      some (ctx.support info.span info.origin.describe)
    else
      none

/-- Convert a TCError to a Diagnostic for rich rendering -/
def toDiagnostic (ctx : DiagContext) : TCError → Diagnostic
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
    let secondaryLabels := chainToLabels ctx chain
    let unifySteps : List Soma.Attach.UnifyStep :=
      chain.toList.map fun info =>
        { origin := info.origin.describe, description := info.description }
    let traceAttach := Soma.Attach.unifyTrace unifySteps
    let attachments : List Psychopomp.Attachment := match failure with
      | .headMismatch v1 v2 | .rigidMismatch v1 v2 =>
        [Soma.Attach.typeMismatch (toString v1) (toString v2), traceAttach]
      | .levelMismatch l1 l2 =>
        [Soma.Attach.universeMismatch (toString l1) (toString l2), traceAttach]
      | _ => [traceAttach]
    { (mkDiag ctx "E1001" msg span failure.message
        (secondary := secondaryLabels)
        (notes := [failure.detailedMessage])
        (help := some "add type annotations to help the compiler infer types")) with
      attachments }

  | .typeMismatch expected actual purpose expectedSpan actualSpan steps =>
    let purposeStr := purpose.describe
    let msg := if purposeStr.isEmpty
      then "type mismatch"
      else s!"type mismatch {purposeStr}"
    let baseLabels := #[mkSupport ctx expectedSpan "expected type from here"]
    let stepLabels := chainToLabels ctx steps
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
    let mismatchAttach := Soma.Attach.typeMismatch (toString expected) (toString actual)
    let traceSteps : List Soma.Attach.UnifyStep := steps.toList.map fun info =>
      { origin := info.origin.describe, description := info.description }
    let traceAttach := Soma.Attach.unifyTrace traceSteps
    let attachments :=
      if steps.isEmpty then [mismatchAttach] else [mismatchAttach, traceAttach]
    { (mkDiag ctx "E1002" msg actualSpan
        (primaryMsg := s!"expected `{expected}`, found `{actual}`")
        (secondary := baseLabels ++ stepLabels)
        (help := help)) with
      attachments }

  | .expectedFunction actual span origin =>
    let originNote := match origin with
      | some o => [s!"type was inferred from: {o.describe}"]
      | none => []
    mkDiag ctx "E1003" "expected function type" span
      (primaryMsg := s!"`{actual}` is not a function")
      (notes := "function application requires a function type (Π-type)" :: originNote)
      (help := some "did you mean field access (`.x`) or forget parentheses?")

  | .expectedType actual span context =>
    let contextNote := match context with
      | some ctx => s!" ({ctx})"
      | none => ""
    mkDiag ctx "E1005" "expected a type" span
      (primaryMsg := s!"`{actual}` is not a type{contextNote}")
      (notes := ["types have type `Type`"])
      (help := some "only type-level expressions are allowed here")

  | .expectedRecord actual span availableFields =>
    let fieldsNote := if availableFields.isEmpty then []
      else [s!"available fields: {String.intercalate ", " availableFields.toList}"]
    mkDiag ctx "E1006" "expected record type" span
      (primaryMsg := s!"`{actual}` is not a record")
      (notes := fieldsNote)
      (help := some "field access (`.x`) and record literals require a record type")

  | .expectedVariant actual span =>
    mkDiag ctx "E1007" "expected variant type" span
      (primaryMsg := s!"`{actual}` is not a variant")
      (help := some "variant injection (`.Label`) requires a variant type")

  | .unboundVariable name span suggestions =>
    let help := match Soma.Dependent.Suggest.formatSuggestions suggestions with
      | some hint => hint
      | none => s!"bind `{name}` with `let` or add a parameter, or check imports"
    mkDiag ctx "E1008" s!"unknown variable `{name}`" span
      (primaryMsg := "not found in scope")
      (help := some help)
      (fixes := Soma.Fix.renameSuggestions ctx span suggestions)

  | .unboundGlobal name span suggestions =>
    let help := match Soma.Dependent.Suggest.formatSuggestions suggestions with
      | some hint => hint
      | none => s!"define `{name}` or add a `use` import that brings it into scope"
    mkDiag ctx "E1009" s!"unknown definition `{name}`" span
      (primaryMsg := "not found")
      (help := some help)
      (fixes := Soma.Fix.renameSuggestions ctx span suggestions)

  | .fieldNotFound field recordTy span availableFields origin =>
    let fieldsNote := if availableFields.isEmpty then ""
      else s!"\navailable fields: {String.intercalate ", " availableFields.toList}"
    let originNote := match origin with
      | some o => [s!"record type inferred from: {o.describe}"]
      | none => []
    let suggestions := Soma.Dependent.Suggest.suggestSimilar field availableFields
    let help := Soma.Dependent.Suggest.formatSuggestions suggestions
    mkDiag ctx "E1010" s!"field `{field}` not found" span
      (primaryMsg := s!"not in `{recordTy}`{fieldsNote}")
      (notes := originNote)
      (help := help)
      (fixes := Soma.Fix.renameSuggestions ctx span suggestions)

  | .wrongConstructorArity ctor expected actual span =>
    let args := if expected == 1 then "argument" else "arguments"
    mkDiag ctx "E1012" s!"wrong number of arguments to `{ctor}`" span
      (primaryMsg := s!"expected {expected} {args}, found {actual}")

  | .quantityMismatch expected actual varName span =>
    mkDiag ctx "E1013" s!"quantity mismatch for `{varName}`" span
      (primaryMsg := s!"declared as `{expected}`, used as `{actual}`")
      (notes := [s!"`0` = erased, `1` = linear, `ω` = unrestricted"])

  | .linearNotUsed varName declSpan =>
    mkDiag ctx "E1014" s!"linear variable `{varName}` not used" declSpan
      (primaryMsg := "must be used exactly once")
      (help := some "use the variable or change its quantity to `0` or `ω`")

  | .linearUsedMultiple varName firstUse secondUse =>
    let primary := mkLinkedPrimary ctx secondUse "used again here" "linear-uses"
    let firstLabel := mkLinkedSupport ctx firstUse "first used here" "linear-uses"
    { (mkDiag ctx "E1015"
        s!"linear variable `{varName}` used multiple times"
        secondUse (primaryMsg := "used again here")
        (secondary := #[firstLabel])
        (notes := ["linear variables (quantity `1`) must be used exactly once"])
        (help := some "change the quantity to `ω` for unrestricted use"))
        with primary }

  | .erasedUsedAtRuntime varName span declSpan =>
    let secondaryLabels := match declSpan with
      | some ds => #[mkSupport ctx ds s!"`{varName}` declared as erased (quantity `0`) here"]
      | none => #[]
    mkDiag ctx "E1016"
      s!"erased variable `{varName}` used at runtime"
      span (primaryMsg := "erased variable used here")
      (secondary := secondaryLabels)
      (notes := ["variables with quantity `0` are erased and exist only for type checking"])
      (help := some "change the quantity to `ω` or `1` if runtime access is needed")

  | .unsolvedMeta ty span relatedConstraints suggestedFix =>
    let originList : List Soma.Attach.MetaConstraint :=
      relatedConstraints.toList.map fun c =>
        { description := c.description
          origin := c.origin.describe
          blocked := c.isBlocked }
    let metaAttach := Soma.Attach.metavarOrigins originList
    let help := suggestedFix.getD "add a type annotation to help inference"
    { (mkDiag ctx "E1017" "could not infer a type here" span
        (primaryMsg := s!"expected a value of type `{ty}`")
        (help := some help))
      with attachments := [metaAttach] }

  | .unsolvedHole name ty span =>
    let nameStr := name.getD "_"
    mkDiag ctx "E1018" s!"unsolved hole `?{nameStr}`" span
      (primaryMsg := s!"has type `{ty}`")

  | .ambiguousImplicit paramName span relatedConstraints partialInfo =>
    let originList : List Soma.Attach.MetaConstraint :=
      relatedConstraints.toList.map fun c =>
        { description := c.description
          origin := c.origin.describe
          blocked := c.isBlocked }
    let metaAttach := Soma.Attach.metavarOrigins originList
    let partialNote := match partialInfo with
      | some info => [s!"Partial information available: {info}"]
      | none => []
    { (mkDiag ctx "E1019" s!"cannot infer implicit `{paramName}`" span
        (primaryMsg := "not enough information")
        (notes := partialNote)
        (help := some s!"provide explicit argument: @{paramName} = <value>"))
      with attachments := [metaAttach] }

  | .cannotInfer reason span context =>
    let contextNote := match context with
      | some o => [s!"while {o.describe}"]
      | none => []
    mkDiag ctx "E1020" "cannot infer type" span
      (primaryMsg := reason)
      (notes := contextNote)
      (help := some "add a type annotation")

  | .compilerBug message span =>
    mkDiag ctx "E1099" s!"compiler bug: {message}" span
      (notes := ["an invariant the compiler relied on was violated"])
      (help := some "please report this at https://github.com/SrGaabriel/soma/issues with the failing input")
      (audience := ["compilerDev"])
      (certainty := .suspected)

  | .unhandledFeature feature span =>
    mkDiag ctx "E1098" s!"unsupported: {feature}" span
      (primaryMsg := s!"the compiler does not yet handle {feature} here")
      (notes := ["this is a known limitation, not a bug"])
      (help := some "track the relevant issue or open a feature request if none exists")

  | .userTriggered message span =>
    mkDiag ctx "E1097" message span
      (notes := ["the input is well-formed but the elaborator cannot proceed"])

  | .noInstance classId _args span attemptedInstances availableInstances =>
    let className := classId.original
    let attemptList : List Soma.Attach.InstanceAttempt :=
      attemptedInstances.toList.map fun a =>
        { name := a.instanceName
          matched := a.failureReason.isNone
          reason := a.failureReason }
    let searchAttach := Soma.Attach.instanceSearch className attemptList
    let availableNote := if availableInstances.isEmpty then []
      else [s!"Available instances for `{className}`: {String.intercalate ", " availableInstances.toList}"]
    { (mkDiag ctx "E1021" s!"no instance for `{className}`" span
        (primaryMsg := "could not find a matching instance")
        (notes := availableNote)
        (help := some s!"add an instance for `{className}` or provide one explicitly"))
      with attachments := [searchAttach] }

  | .instanceCycle classId span cycleTrace =>
    let className := classId.original
    let cycleNote := if cycleTrace.isEmpty then []
      else [s!"Resolution cycle:\n{String.intercalate " → " cycleTrace.toList}"]
    mkDiag ctx "E1022" s!"cycle in instance resolution for `{className}`" span
      (primaryMsg := "instance resolution would loop forever")
      (notes := "instance constraints form a cycle" :: cycleNote)

  | .instanceDepthExceeded classId span searchPath =>
    let className := classId.original
    let pathNote := if searchPath.isEmpty then []
      else [s!"Search path (truncated):\n{String.intercalate " → " searchPath.toList}"]
    mkDiag ctx "E1023" s!"instance resolution depth exceeded for `{className}`" span
      (primaryMsg := "search exceeded maximum depth")
      (notes := pathNote)
      (help := some "simplify instance constraints or increase search depth")

  | .terminationCheckFailed fnName reason span failingCalls triedArguments =>
    let primary := mkLinkedPrimary ctx span reason "recursion"
    let callLabels := failingCalls.map fun s =>
      mkLinkedSupport ctx s "recursive call here" "recursion"
    let triedNote := if triedArguments.isEmpty then #[]
      else
        let items := triedArguments.map fun (idx, reason) =>
          s!"  • argument {idx + 1}: {reason}"
        #[s!"Termination analysis:\n{String.intercalate "\n" items.toList}"]
    let baseNote :=
      "every definition is checked for termination"
    { (mkDiag ctx "E1026"
        s!"termination check failed for `{fnName.display}`"
        span (primaryMsg := reason)
        (secondary := callLabels)
        (notes := (#[baseNote] ++ triedNote).toList)
        (help := some
          "ensure recursive calls are on structurally smaller arguments, \
           or mark the definition `@[partial]` (note: partial functions are \
           opaque and may not inhabit uninhabited types)"))
        with primary }

  | .partialInTypeIndex fnName span =>
    mkDiag ctx "E1027" s!"partial function `{fnName.display}` used in type index" span
      (primaryMsg := "only total functions can appear in type indices")
      (notes := ["type indices must be computable to keep type checking decidable"])
      (help := some s!"mark `{fnName.display}` as @[total] or use a different function")

  | .partialInhabitsUninhabited fnName span =>
    mkDiag ctx "E1029"
      s!"`@[partial]` definition `{fnName.display}` cannot inhabit an uninhabited type" span
      (primaryMsg := "partial functions never produce a concrete value")
      (notes := ["`@[partial]` is only valid when the return type has at least one constructor"])
      (help := some "make the definition total (its recursion must be provably well-founded)")

  | .positivityViolation typeName reason span violatingPosition =>
    match violatingPosition with
    | some vs =>
      let primary := mkLinkedPrimary ctx span reason "positivity"
      let sec := mkLinkedSupport ctx vs "negative occurrence here" "positivity"
      { (mkDiag ctx "E1028"
          s!"positivity check failed for `{typeName}`"
          span (primaryMsg := reason)
          (secondary := #[sec])
          (notes := ["data types must be strictly positive to prevent paradoxes"])
          (help := some "ensure the type only appears in positive positions in constructors"))
          with primary }
    | none =>
      mkDiag ctx "E1028"
        s!"positivity check failed for `{typeName}`"
        span (primaryMsg := reason)
        (notes := ["data types must be strictly positive to prevent paradoxes"])
        (help := some "ensure the type only appears in positive positions in constructors")

  | .impossiblePattern ctor ctorResultTy scrutTy span =>
    mkDiag ctx "E1030" s!"impossible pattern `{ctor}`" span
      (primaryMsg := s!"constructor produces `{ctorResultTy}`, but matching against `{scrutTy}`")
      (notes := ["the constructor's index does not match the scrutinee type"])
      (help := some "remove this pattern")

  | .nonExhaustiveMatch scrutType missing span =>
    let scrutStr := toString scrutType
    let primaryDetail :=
      if missing.isEmpty then
        "pattern match does not cover every case"
      else
        let quoted := missing.toList.map (s!"`{·}`")
        s!"missing: {String.intercalate ", " quoted}"
    let notes :=
      if missing.isEmpty then []
      else ["each listed shape can occur at runtime but no arm matches it"]
    let coverageAttach := Soma.Attach.coverage scrutStr missing.toList
    { (mkDiag ctx "E1031" "non-exhaustive pattern match" span
        (primaryMsg := primaryDetail)
        (notes := notes)
        (help := some "add an arm for each listed case, or a catch-all variable / `_` pattern"))
      with attachments := [coverageAttach] }

  | .bodilessNotDerivable name resolvedType span =>
    mkDiag ctx "E1032"
      s!"bodiless definition '{name}' is not derivable"
      span (primaryMsg := "no explicit parameter with an uninhabited type")
      (notes := [
        s!"after reduction, the declared type is `{resolvedType}`",
        "a bodiless def is a proof-by-absurdity"
      ])
      (help := some "if you meant to prove that the declared type is unprovable, rewrite as `T -> Never`; otherwise provide a body (`:=` or `|` clauses) or mark as @[intrinsic]/@[extern]")

  | .patternArityMismatch name sigArity clauseArity resultTy span =>
    let patWord := if clauseArity == 1 then "pattern" else "patterns"
    let paramWord := if sigArity == 1 then "parameter" else "parameters"
    mkDiag ctx "E1035" s!"arity mismatch in `{name}`" span
      (primaryMsg := s!"each clause has {clauseArity} {patWord}, but the signature exposes only {sigArity} explicit {paramWord}")
      (notes := [s!"after the {sigArity} explicit {paramWord}, the result type is not a function: `{resultTy}`"])
      (help := some (
        if clauseArity > sigArity then
          s!"remove {clauseArity - sigArity} pattern column(s), or extend the signature with more `->`"
        else
          "add patterns for the missing parameter(s), or adjust the signature"
      ))

  | .partialTheorem name span =>
    mkDiag ctx "E1037"
      s!"theorem `{name}` cannot be marked `@[partial]`" span
      (primaryMsg := "a partial proof is not a proof")
      (notes := ["theorems are required to be total"])
      (help := some
        "drop `@[partial]`, make the recursion structurally decreasing, \
         or restate the declaration as a `def` if it's really runtime code")

  | .propElimToType scrutTy motiveTy span =>
    mkDiag ctx "E1038"
      "cannot eliminate this Prop into a Type" span
      (primaryMsg := s!"scrutinee of type `{scrutTy}` is a proposition")
      (notes := [s!"the expected motive `{motiveTy}` lives in `Type`, but \
                   propositions can only be observed from another proposition"])
      (help := some
        "either change the result type so the match produces a \
         proposition, or rework the Prop so it becomes small \
         (drop constructors / lift a field from `Type` to `Prop`)")

  | .classNotInScope name span =>
    mkDiag ctx "E1033"
      s!"type class `{name}` is not in scope"
      span (primaryMsg := s!"`{name}` not imported")
      (notes := [s!"the class exists in a loaded module but isn't visible here"])
      (help := some ("add a `use` clause that imports `" ++ name ++ "` or its module"))

  | .unknownClass name span =>
    mkDiag ctx "E1034"
      s!"unknown type class `{name}`"
      span (primaryMsg := s!"`{name}` is not a class")
      (notes := [s!"no class named `{name}` is defined in this module or any of its dependencies"])
      (help := some "check for typos, or declare the class with `class ... where ...`")

  | .unknownInstanceMethod className methodName knownMethods span =>
    let knownNote :=
      if knownMethods.isEmpty then []
      else [s!"class `{className}` has methods: {String.intercalate ", " knownMethods.toList}"]
    let suggestions := Soma.Dependent.Suggest.suggestSimilar methodName knownMethods
    let help := match Soma.Dependent.Suggest.formatSuggestions suggestions with
      | some hint => hint
      | none =>
        s!"remove this `def`, or move it to an `instance` of the class that owns `{methodName}`"
    mkDiag ctx "E1040"
      s!"`{methodName}` is not a method of class `{className}`" span
      (primaryMsg := s!"`{methodName}` is not declared in `{className}`")
      (notes := knownNote)
      (help := some help)
      (fixes := Soma.Fix.renameSuggestions ctx span suggestions)

  | .missingInstanceMethods className missing span =>
    let list := String.intercalate ", " missing.toList
    mkDiag ctx "E1041"
      s!"instance of `{className}` is missing required methods" span
      (primaryMsg := s!"missing: {list}")
      (help := some s!"add a `def` clause for each missing method ({list}) inside this instance")

/-- The context-free headline string for a `TCError` -/
def headline (e : TCError) : String :=
  let ctx : DiagContext := default
  (toDiagnostic ctx e).message

instance : ToString TCError := ⟨TCError.headline⟩

end TCError

/-- Collection of type checking errors -/
abbrev TCErrors := Array TCError

namespace TCErrors

/-- Convert all errors to diagnostics -/
def toDiagnostics (ctx : DiagContext) (errs : TCErrors) : Array Diagnostic :=
  errs.map (TCError.toDiagnostic ctx)

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

private def warnSev : Psychopomp.Severity := severity .elaborate .warning

/-- Assemble an elaborator warning diagnostic -/
private def mkWarn (ctx : DiagContext) (code : String) (message : String)
    (span : Span) (primaryMsg : String := message) : Diagnostic :=
  { severity := warnSev
    code := some code
    message
    primary := ctx.primary span primaryMsg }

def toDiagnostic (ctx : DiagContext) : TCWarning → Diagnostic
  | .unusedVariable name span =>
    mkWarn ctx "W1001" s!"unused variable `{name}`" span
  | .unnecessaryImplicit name span =>
    mkWarn ctx "W1002" s!"implicit `{name}` could be explicit" span
  | .redundantAnnotation span =>
    mkWarn ctx "W1003" "redundant type annotation" span
  | .unreachableCode span =>
    mkWarn ctx "W1004" "unreachable code" span
  | .totalityUnknown fnName span =>
    mkWarn ctx "W1005" s!"totality of `{fnName.display}` could not be determined" span

/-- Context-free headline string for a `TCWarning` -/
def headline (w : TCWarning) : String :=
  let ctx : DiagContext := default
  (toDiagnostic ctx w).message

instance : ToString TCWarning := ⟨TCWarning.headline⟩

end TCWarning

end Soma.Dependent
