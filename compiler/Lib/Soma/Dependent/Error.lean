import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quantity
import Soma.Core.Quote
import Soma.Syntax.Diagnostic

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
  /-- Unknown/legacy origin -/
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

  /-- Constructor not found in data type -/
  | constructorNotFound
      (ctor : String)
      (dataTy : Value)
      (span : Span)
      (availableCtors : Array String)

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
      (id : MetaId)
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
      (fnName : Soma.Core.QualifiedName)
      (reason : String)
      (span : Span)
      (failingCalls : Array Span)
      (triedArguments : Array (Nat × String))

  /-- Partial function used in type index -/
  | partialInTypeIndex
      (fnName : Soma.Core.QualifiedName)
      (span : Span)

  /-- Positivity check failed for data type -/
  | positivityViolation
      (typeName : String)
      (reason : String)
      (span : Span)
      (violatingPosition : Option Span)

  /-- Recursive call not structurally decreasing -/
  | nonStructuralRecursion
      (fnName : Soma.Core.QualifiedName)
      (callSpan : Span)
      (expectedArg : Option (Nat × String))
      (actualArg : Option String)

  /-- Impossible constructor pattern: indices conflict with scrutinee type -/
  | impossiblePattern
      (ctor : String)
      (ctorResultTy : Value)
      (scrutTy : Value)
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
  | .constructorNotFound _ _ s _ => s
  | .wrongConstructorArity _ _ _ s => s
  | .quantityMismatch _ _ _ s => s
  | .linearNotUsed _ s => s
  | .linearUsedMultiple _ _ s => s
  | .erasedUsedAtRuntime _ s _ => s
  | .unsolvedMeta _ _ s _ _ => s
  | .unsolvedHole _ _ s => s
  | .ambiguousImplicit _ s _ _ => s
  | .cannotInfer _ s _ => s
  | .internalError _ s => s
  | .noInstance _ _ s _ _ => s
  | .instanceCycle _ s _ => s
  | .instanceDepthExceeded _ s _ => s
  | .overlappingInstances _ _ s => s
  | .unknownClass _ s => s
  | .terminationCheckFailed _ _ s _ _ => s
  | .partialInTypeIndex _ s => s
  | .positivityViolation _ _ s _ => s
  | .nonStructuralRecursion _ s _ _ => s
  | .impossiblePattern _ _ _ s => s

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
    { severity := .error
    , code := some "E1002"
    , message := msg
    , primaryLabel := Label.primary actualSpan s!"expected `{expected}`, found `{actual}`"
    , secondaryLabels := baseLabels ++ stepLabels
    , notes := chainToNotes steps
    , help := none
    }

  | .expectedFunction actual span origin =>
    let originNote := match origin with
      | some o => #[s!"type was inferred from: {o.describe}"]
      | none => #[]
    Diagnostic.error "expected function type" span s!"`{actual}` is not a function"
      |>.withCode "E1003"
      |>.withNote "function application requires a function type (Π-type)"
      |> fun d => { d with notes := d.notes ++ originNote }

  | .expectedSigma actual span origin =>
    let originNote := match origin with
      | some o => #[s!"type was inferred from: {o.describe}"]
      | none => #[]
    Diagnostic.error "expected pair type" span s!"`{actual}` is not a pair"
      |>.withCode "E1004"
      |>.withNote "pair projection requires a dependent pair type (Σ-type)"
      |> fun d => { d with notes := d.notes ++ originNote }

  | .expectedType actual span context =>
    let contextNote := match context with
      | some ctx => s!" ({ctx})"
      | none => ""
    Diagnostic.error "expected a type" span s!"`{actual}` is not a type{contextNote}"
      |>.withCode "E1005"
      |>.withNote "types have type `Type`"

  | .expectedRecord actual span availableFields =>
    let fieldsNote := if availableFields.isEmpty then #[]
      else #[s!"available fields: {String.intercalate ", " availableFields.toList}"]
    Diagnostic.error "expected record type" span s!"`{actual}` is not a record"
      |>.withCode "E1006"
      |> fun d => { d with notes := d.notes ++ fieldsNote }

  | .expectedVariant actual span =>
    Diagnostic.error "expected variant type" span s!"`{actual}` is not a variant"
      |>.withCode "E1007"

  | .unboundVariable name span suggestions =>
    let help := if suggestions.isEmpty then s!"did you mean to define `{name}`?"
      else s!"did you mean: {String.intercalate ", " suggestions.toList}?"
    Diagnostic.error s!"unknown variable `{name}`" span "not found in scope"
      |>.withCode "E1008"
      |>.withHelp help

  | .unboundGlobal name span suggestions =>
    let help := if suggestions.isEmpty then "check that the definition is imported"
      else s!"did you mean: {String.intercalate ", " suggestions.toList}?"
    Diagnostic.error s!"unknown definition `{name}`" span "not found"
      |>.withCode "E1009"
      |>.withHelp help

  | .fieldNotFound field recordTy span availableFields origin =>
    let fieldsNote := if availableFields.isEmpty then ""
      else s!"\navailable fields: {String.intercalate ", " availableFields.toList}"
    let originNote := match origin with
      | some o => #[s!"record type inferred from: {o.describe}"]
      | none => #[]
    Diagnostic.error s!"field `{field}` not found" span s!"not in `{recordTy}`{fieldsNote}"
      |>.withCode "E1010"
      |> fun d => { d with notes := d.notes ++ originNote }

  | .constructorNotFound ctor dataTy span availableCtors =>
    let ctorsNote := if availableCtors.isEmpty then ""
      else s!"\navailable constructors: {String.intercalate ", " availableCtors.toList}"
    Diagnostic.error s!"constructor `{ctor}` not found" span s!"not in `{dataTy}`{ctorsNote}"
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

  | .unsolvedMeta id ty span relatedConstraints suggestedFix =>
    let constraintNotes := if relatedConstraints.isEmpty then #[]
      else
        let items := relatedConstraints.map fun c =>
          let blockedStr := if c.isBlocked then " (blocked)" else ""
          s!"  • {c.description}{blockedStr}"
        #[s!"Related constraints:\n{String.intercalate "\n" items.toList}"]
    let help := suggestedFix.getD "add a type annotation to help inference"
    Diagnostic.error s!"unsolved metavariable `{id}`" span s!"has type `{ty}`"
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

  | .terminationCheckFailed fnName reason span failingCalls triedArguments =>
    let callLabels := failingCalls.map fun s => Label.secondary s "recursive call here"
    let triedNote := if triedArguments.isEmpty then #[]
      else
        let items := triedArguments.map fun (idx, reason) =>
          s!"  • argument {idx + 1}: {reason}"
        #[s!"Termination analysis:\n{String.intercalate "\n" items.toList}"]
    { severity := .error
    , code := some "E1026"
    , message := s!"termination check failed for `{fnName.display}`"
    , primaryLabel := Label.primary span reason
    , secondaryLabels := callLabels
    , notes := #["functions marked @[total] must be proven to terminate"] ++ triedNote
    , help := some "ensure recursive calls are on structurally smaller arguments"
    }

  | .partialInTypeIndex fnName span =>
    Diagnostic.error s!"partial function `{fnName.display}` used in type index" span
        "only total functions can appear in type indices"
      |>.withCode "E1027"
      |>.withNote "type indices must be computable to keep type checking decidable"
      |>.withHelp s!"mark `{fnName.display}` as @[total] or use a different function"

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

  | .nonStructuralRecursion fnName callSpan expectedArg actualArg =>
    let expectedNote := match expectedArg with
      | some (idx, name) => s!"expected argument {idx + 1} (`{name}`) to decrease"
      | none => "could not identify a decreasing argument"
    let actualNote := match actualArg with
      | some arg => s!"actual argument: `{arg}`"
      | none => ""
    let notes := #[
      "for @[total] functions, each recursive call must decrease some argument",
      expectedNote
    ] ++ (if actualNote.isEmpty then #[] else #[actualNote])
    { severity := .error
    , code := some "E1029"
    , message := s!"non-structural recursion in `{fnName.display}`"
    , primaryLabel := Label.primary callSpan "recursive call is not on a structurally smaller argument"
    , secondaryLabels := #[]
    , notes := notes
    , help := some "use pattern matching to obtain structurally smaller subterms"
    }

  | .impossiblePattern ctor ctorResultTy scrutTy span =>
    Diagnostic.error s!"impossible pattern `{ctor}`" span
        s!"constructor produces `{ctorResultTy}`, but matching against `{scrutTy}`"
      |>.withCode "E1030"
      |>.withNote "the constructor's index does not match the scrutinee type"
      |>.withHelp "remove this pattern — it can never match"

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
