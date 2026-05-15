import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quantity
import Soma.Core.Quote
import Soma.Core.Pp
import Soma.Diagnostic
import Soma.Diagnostic.Pretty.Substrate
import Soma.Dependent.Origin
import Soma.Core.Path
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

private def mkDefinitionLabel (ctx : DiagContext) (span : Span) (msg : String) : Label :=
  ctx.label span msg Soma.LabelStyle.definition

private def mkReferenceLabel (ctx : DiagContext) (span : Span) (msg : String) : Label :=
  ctx.label span msg Soma.LabelStyle.reference

private def mkInsertedLabel (ctx : DiagContext) (span : Span) (msg : String) : Label :=
  ctx.label span msg Soma.LabelStyle.inserted

private def mkOverriddenLabel (ctx : DiagContext) (span : Span) (msg : String) : Label :=
  ctx.label span msg Soma.LabelStyle.overridden

private def mkEnclosedLabel (ctx : DiagContext) (span : Span) (msg : String) : Label :=
  ctx.label span msg Soma.LabelStyle.enclosed

private def mkSuggestionLabel (ctx : DiagContext) (span : Span) (msg : String) : Label :=
  ctx.label span msg Soma.LabelStyle.suggestion

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
  /-- Head mismatch at the given structural path within `v1`/`v2` -/
  | headMismatch
      (v1 v2 : Value)
      (path : Path)
      (reduced : Option (Value × Value))
      (trace : Array Soma.Attach.UnfoldStep)
      (implicits : Option (String × Array Soma.Attach.InsertedImplicit))
  /-- Occurs check failed -/
  | occursCheck
      (metaId : MetaId)
      (value : Value)
      (path : Path)
      (roots : Option (Value × Value))
  /-- Rigid-rigid mismatch at the given structural path -/
  | rigidMismatch
      (n1 n2 : Neutral)
      (path : Path)
      (roots : Option (Value × Value))
  /-- Universe level mismatch -/
  | levelMismatch
      (l1 l2 : Level)
      (path : Path)
      (roots : Option (Value × Value))
  /-- Row label not found during rewriting -/
  | rowLabelNotFound
      (label : String)
      (row : Value)
      (path : Path)
      (roots : Option (Value × Value))
  /-- Spine length mismatch in pattern unification -/
  | spineLengthMismatch
      (expected actual : Nat)
      (path : Path)
      (roots : Option (Value × Value))
  /-- Non-linear pattern: variable appears multiple times -/
  | nonLinearPattern
      (varName : String)
      (path : Path)
      (roots : Option (Value × Value))
  /-- Solution would reference out-of-scope variable -/
  | escapingVariable
      (varName : String)
      (level : DeBruijnLvl)
      (bindingSite : Option Span)
      (path : Path)
      (roots : Option (Value × Value))
  deriving Inhabited

namespace UnifyFailure

/-- Build the " at <path>" suffix shown in the headline message -/
private def pathSuffix (path : Path) (roots : Option (Value × Value)) : String :=
  if path.isEmpty then ""
  else if roots.isSome then s!" at {path.describe}"
  else s!" (at structural path {path.describe})"

/-- Same shape as `pathSuffix` but for the multi-sentence `detailedMessage` -/
private def pathDetail (path : Path) (roots : Option (Value × Value)) : String :=
  if path.isEmpty then ""
  else if roots.isSome then s!" The clash sits inside the {path.describe} of the surrounding types."
  else s!" Structural path: {path.describe}."

/-- One-line message describing the failure -/
def message (pp : Soma.Core.PpContext) : UnifyFailure → String
  | .headMismatch v1 v2 path _ _ _ =>
      s!"cannot unify `{Soma.Core.Value.pp pp v1}` with `{Soma.Core.Value.pp pp v2}`{pathSuffix path none}"
  | .occursCheck m v path roots =>
      s!"infinite type: `?m{m.id}` would contain itself via `{Soma.Core.Value.pp pp v}`{pathSuffix path roots}"
  | .rigidMismatch n1 n2 path roots =>
      s!"cannot unify `{Soma.Core.Neutral.pp pp n1}` with `{Soma.Core.Neutral.pp pp n2}` (both are stuck){pathSuffix path roots}"
  | .levelMismatch l1 l2 path roots =>
      s!"universe level mismatch: `{l1}` vs `{l2}`{pathSuffix path roots}"
  | .rowLabelNotFound label row path roots =>
      s!"field `{label}` not found in `{Soma.Core.Value.pp pp row}`{pathSuffix path roots}"
  | .spineLengthMismatch expected actual path roots =>
      s!"expected {expected} arguments, found {actual}{pathSuffix path roots}"
  | .nonLinearPattern name path roots =>
      s!"variable `{name}` appears multiple times in pattern{pathSuffix path roots}"
  | .escapingVariable name _ _ path roots =>
      s!"variable `{name}` would escape its scope in the solution{pathSuffix path roots}"

/-- Multi-sentence explanation of the failure -/
def detailedMessage (pp : Soma.Core.PpContext) : UnifyFailure → String
  | .headMismatch v1 v2 path _ _ _ =>
      let suf :=
        if path.isEmpty then ""
        else s!" The obstruction lies in the {path.describe}."
      s!"The types `{Soma.Core.Value.pp pp v1}` and `{Soma.Core.Value.pp pp v2}` have incompatible structure and cannot be unified.{suf}"
  | .occursCheck m v path roots =>
      s!"Solving `?m{m.id}` would create an infinite type because `?m{m.id}` appears in its own solution `{Soma.Core.Value.pp pp v}`. " ++
      "This usually means a type annotation is needed to break the cycle." ++ pathDetail path roots
  | .rigidMismatch n1 n2 path roots =>
      s!"Both `{Soma.Core.Neutral.pp pp n1}` and `{Soma.Core.Neutral.pp pp n2}` are blocked on unsolved variables or computations, " ++
      "so they cannot be compared. Adding type annotations may help resolve them." ++ pathDetail path roots
  | .levelMismatch l1 l2 path roots =>
      s!"Universe levels `{l1}` and `{l2}` cannot be unified. " ++
      "This may indicate mixing values and types incorrectly." ++ pathDetail path roots
  | .rowLabelNotFound label row path roots =>
      s!"The row type `{Soma.Core.Value.pp pp row}` does not contain a field named `{label}`." ++ pathDetail path roots
  | .spineLengthMismatch expected actual path roots =>
      s!"Function was applied to {actual} arguments but expected {expected}." ++ pathDetail path roots
  | .nonLinearPattern name path roots =>
      s!"In pattern unification, each variable must appear exactly once, " ++
      s!"but `{name}` appears multiple times." ++ pathDetail path roots
  | .escapingVariable name lvl bindingSite path roots =>
      let siteInfo := match bindingSite with
        | some _ => " (see binding site)"
        | none => s!" (at De Bruijn level {lvl.lvl})"
      s!"Variable `{name}`{siteInfo} is not in scope where the solution would be used. " ++
      "This often happens when trying to solve an outer metavariable with an inner-scoped variable." ++ pathDetail path roots

instance : ToString UnifyFailure := ⟨UnifyFailure.message .empty⟩

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

/-- Which kind of branch construct fired a `branchTypeMismatch` -/
inductive BranchKind where
  | ifElse
  | caseArms
  deriving Repr, BEq, Inhabited

namespace BranchKind

def describe : BranchKind → String
  | .ifElse => "branches of `if/else`"
  | .caseArms => "arms of `case`"

end BranchKind

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

  /-- Branches of an `if` / `case` disagree on their result type -/
  | branchTypeMismatch
      (kind : BranchKind)
      (branches : Array (Span × Value))
      (span : Span)

  /-- Expected a function type (Pi) but got something else -/
  | expectedFunction
      (actual : Value)
      (span : Span)
      (inferredFrom : ConstraintOrigin)

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
      (inferredRecordType : ConstraintOrigin)

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
      (localContext : List (String × Value) := [])

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
      (context : ConstraintOrigin)

  /-- Compiler bug -/
  | compilerBug
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

/-- Whether this error should be treated as the root of a cascade -/
def isCascadeRoot : TCError → Bool
  | .partialTheorem _ _ => true
  | .terminationCheckFailed _ _ _ _ _ => true
  | .positivityViolation _ _ _ _ => true
  | .partialInhabitsUninhabited _ _ => true
  | .partialInTypeIndex _ _ => true
  | .bodilessNotDerivable _ _ _ => true
  | .patternArityMismatch _ _ _ _ _ => true
  | .impossiblePattern _ _ _ _ => true
  | .propElimToType _ _ _ => true
  | _ => false

/-- Build secondary labels from constraint chain -/
private def chainToLabels (ctx : DiagContext) (pp : Soma.Core.PpContext)
    (chain : Array ConstraintInfo) : Array Label :=
  chain.filterMap fun info =>
    if info.span != Span.uninhabited then
      some (ctx.support info.span (info.origin.describeWith pp))
    else
      none

/-- Convert a TCError to a Diagnostic for rich rendering -/
def toDiagnostic (ctx : DiagContext) (pp : Soma.Core.PpContext)
    (e : TCError) : Diagnostic :=
  letI : ToString Soma.Core.Value := ⟨Soma.Core.Value.pp pp⟩
  letI : ToString Soma.Core.Neutral := ⟨Soma.Core.Neutral.pp pp⟩
  let maybeMarkRoot (d : Diagnostic) : Diagnostic :=
    if e.isCascadeRoot then Soma.markCascadeRoot d else d
  maybeMarkRoot <| match e with
  | .unificationFailed failure purpose span chain _metas =>
    let purposeStr := purpose.describe
    let baseMsg := match failure with
      | .headMismatch .. => "type mismatch"
      | .occursCheck .. => "infinite type"
      | .rigidMismatch .. => "unification stuck"
      | .escapingVariable .. => "scope error"
      | .levelMismatch .. => "universe level mismatch"
      | _ => "unification failed"
    let msg := if purposeStr.isEmpty
      then baseMsg
      else s!"{baseMsg} {purposeStr}"
    let secondaryLabels := chainToLabels ctx pp chain
    let unifySteps : List Soma.Attach.UnifyStep :=
      chain.toList.map fun info =>
        { origin := info.origin.describeWith pp, description := info.description }
    let traceAttach := Soma.Attach.unifyTrace unifySteps
    let vpp (v : Soma.Core.Value) : String := Soma.Core.Value.pp pp v
    let npp (n : Soma.Core.Neutral) : String := Soma.Core.Neutral.pp pp n
    let attachments : List Psychopomp.Attachment := match failure with
      | .headMismatch v1 v2 _ reduced trace implicits =>
        let mismatchAttach := Soma.Attach.typeMismatch (vpp v1) (vpp v2)
        let defEqAttach : List Psychopomp.Attachment := match reduced with
          | some (r1, r2) =>
            let s1 := vpp v1
            let s2 := vpp v2
            let rs1 := vpp r1
            let rs2 := vpp r2
            if rs1 == s1 && rs2 == s2 then [] else [Soma.Attach.defEqHint rs1 rs2]
          | none => []
        let unfoldAttach : List Psychopomp.Attachment :=
          if trace.isEmpty then [] else [Soma.Attach.unfoldTrace trace.toList]
        let implicitsAttach : List Psychopomp.Attachment :=
          match implicits with
          | some (surface, ii) =>
            if ii.isEmpty then [] else [Soma.Attach.implicits surface ii.toList]
          | none => []
        [mismatchAttach] ++ defEqAttach ++ unfoldAttach ++ implicitsAttach ++ [traceAttach]
      | .rigidMismatch n1 n2 _ _ =>
        [Soma.Attach.typeMismatch (npp n1) (npp n2), traceAttach]
      | .levelMismatch l1 l2 _ _ =>
        [Soma.Attach.universeMismatch (toString l1) (toString l2), traceAttach]
      | _ => [traceAttach]
    { (mkDiag ctx "E1001" msg span (failure.message pp)
        (secondary := secondaryLabels)
        (notes := [failure.detailedMessage pp])
        (help := some "add type annotations to help the compiler infer types")) with
      attachments }

  | .typeMismatch expected actual purpose expectedSpan actualSpan steps =>
    let purposeStr := purpose.describe
    let msg := if purposeStr.isEmpty
      then "type mismatch"
      else s!"type mismatch {purposeStr}"
    let baseLabels := #[mkSupport ctx expectedSpan "expected type from here"]
    let stepLabels := chainToLabels ctx pp steps
    let help : Option String := match purpose with
      | .functionBody fn =>
        some s!"change `{fn}`'s return type or the body to match"
      | .functionArg fn idx =>
        some s!"pass a value of type `{expected}` as argument #{idx + 1} to `{fn}`"
      | .ifCondition => some "`if` conditions must have type `Bool`"
      | .patternMatch => some "the pattern doesn't match the scrutinee's type"
      | .letBinding nm => some s!"the value bound to `{nm}` doesn't match its annotation"
      | .typeAnnotation => some "the expression doesn't match its type annotation"
      | _ => none
    let mismatchAttach := Soma.Attach.typeMismatch (toString expected) (toString actual)
    let traceSteps : List Soma.Attach.UnifyStep := steps.toList.map fun info =>
      { origin := info.origin.describeWith pp, description := info.description }
    let traceAttach := Soma.Attach.unifyTrace traceSteps
    let attachments :=
      if steps.isEmpty then [mismatchAttach] else [mismatchAttach, traceAttach]
    { (mkDiag ctx "E1002" msg actualSpan
        (primaryMsg := s!"expected `{expected}`, found `{actual}`")
        (secondary := baseLabels ++ stepLabels)
        (help := help)) with
      attachments }

  | .branchTypeMismatch kind branches span =>
    let group := "branches-must-agree"
    let labels : Array Label := branches.mapIdx fun i (bspan, btype) =>
      let msg := s!"branch {i + 1}: `{toString btype}`"
      if i == 0 then
        mkLinkedPrimary ctx bspan msg group
      else
        mkLinkedSupport ctx bspan msg group
    let primary := labels[0]?.getD (mkPrimary ctx span "branches must agree")
    let secondary := if labels.size <= 1 then #[] else labels.extract 1 labels.size
    let kindStr := kind.describe
    { (mkDiag ctx "E1042"
        s!"types of {kindStr} disagree" span
        (primaryMsg := "branches must produce the same type")
        (secondary := secondary)
        (notes := ["every branch contributes to the result type; they have to unify"])
        (help := some "make the branches agree, or annotate the construct's result type"))
      with primary }

  | .expectedFunction actual span origin =>
    let originNote := match origin with
      | .unknown => []
      | o => [s!"type was inferred from: {o.describeWith pp}"]
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
      | .unknown => []
      | o => [s!"record type inferred from: {o.describeWith pp}"]
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
    let group := "linear-uses"
    let primary : Label :=
      ctx.label secondUse "used again here"
        { Soma.LabelStyle.reference with weight := 100, color := .severity, linkGroup := some group }
    let firstLabel : Label :=
      ctx.label firstUse "first used here"
        { Soma.LabelStyle.reference with linkGroup := some group }
    { (mkDiag ctx "E1015"
        s!"linear variable `{varName}` used multiple times"
        secondUse (primaryMsg := "used again here")
        (secondary := #[firstLabel])
        (notes := ["linear variables (quantity `1`) must be used exactly once"])
        (help := some "change the quantity to `ω` for unrestricted use"))
        with primary }

  | .erasedUsedAtRuntime varName span declSpan =>
    let secondaryLabels := match declSpan with
      | some ds =>
        #[mkDefinitionLabel ctx ds
            s!"`{varName}` declared as erased (quantity `0`) here"]
      | none => #[]
    mkDiag ctx "E1016"
      s!"erased variable `{varName}` used at runtime"
      span (primaryMsg := "erased variable used here")
      (secondary := secondaryLabels)
      (notes := ["variables with quantity `0` are erased and exist only for type checking"])
      (help := some "change the quantity to `ω` or `1` if runtime access is needed")

  | .unsolvedMeta ty span relatedConstraints suggestedFix _ctxLocals =>
    let originList : List Soma.Attach.MetaConstraint :=
      relatedConstraints.toList.map fun c =>
        { description := c.description
          origin := c.origin.describeWith pp
          blocked := c.isBlocked }
    let metaAttach := Soma.Attach.metavarOrigins originList
    let help := suggestedFix.getD "add a type annotation to help inference"
    { (mkDiag ctx "E1017" "could not infer a type here" span
        (primaryMsg := s!"expected a value of type `{ty}`")
        (help := some help))
      with attachments := [metaAttach] }

  | .ambiguousImplicit paramName span relatedConstraints partialInfo =>
    let originList : List Soma.Attach.MetaConstraint :=
      relatedConstraints.toList.map fun c =>
        { description := c.description
          origin := c.origin.describeWith pp
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
      | .unknown => []
      | o => [s!"while {o.describeWith pp}"]
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
  (toDiagnostic ctx Soma.Core.PpContext.empty e).message

instance : ToString TCError := ⟨TCError.headline⟩

/-- Build a diagnostic for `e` and decorate it with value-substrate snippet blocks where applicable -/
def toDiagnosticDecorated (ctx : DiagContext) (pp : Soma.Core.PpContext)
    (e : TCError) : DiagContext × Diagnostic :=
  let baseDiag := toDiagnostic ctx pp e
  let attachUnary (ctx : DiagContext) (v : Soma.Core.Value)
      (name : String) (msg : String) (d : Diagnostic)
      : DiagContext × Diagnostic :=
    let (ctx', _, lbl) :=
      ctx.putValueSubstrate pp v name msg Psychopomp.LabelStyle.support
    (ctx', { d with secondary := d.secondary ++ [lbl] })
  let decorateWithRoots (ctx : DiagContext) (path : Path)
      (roots : Option (Soma.Core.Value × Soma.Core.Value))
      (fallback : Soma.Core.Value × Soma.Core.Value)
      (src : String) (d : Diagnostic) : DiagContext × Diagnostic :=
    let (v1, v2) := roots.getD fallback
    Soma.Diagnostic.Pretty.Substrate.decorateBinary ctx pp v1 v2 src d (path := path)
  match e with
  | .unificationFailed (.headMismatch v1 v2 path _ _ _) _ span _ _ =>
    let src := s!"{span.start.line}:{span.start.column}"
    Soma.Diagnostic.Pretty.Substrate.decorateBinary ctx pp v1 v2 src baseDiag (path := path)
  | .unificationFailed (.rigidMismatch n1 n2 path roots) _ span _ _ =>
    let src := s!"{span.start.line}:{span.start.column}"
    decorateWithRoots ctx path roots
      (.vNeutral .type0 n1, .vNeutral .type0 n2) src baseDiag
  | .unificationFailed (.occursCheck _ v path roots) _ span _ _ =>
    let src := s!"{span.start.line}:{span.start.column}"
    decorateWithRoots ctx path roots (v, v) src baseDiag
  | .unificationFailed (.escapingVariable _ _ _ path roots) _ span _ _ =>
    match roots with
    | some _ =>
      let src := s!"{span.start.line}:{span.start.column}"
      decorateWithRoots ctx path roots (.vRowSort, .vRowSort) src baseDiag
    | none => (ctx, baseDiag)
  | .unificationFailed (.levelMismatch _ _ path (some (v1, v2))) _ span _ _ =>
    let src := s!"{span.start.line}:{span.start.column}"
    Soma.Diagnostic.Pretty.Substrate.decorateBinary ctx pp v1 v2 src baseDiag (path := path)
  | .unificationFailed (.rowLabelNotFound _ _ path (some (v1, v2))) _ span _ _ =>
    let src := s!"{span.start.line}:{span.start.column}"
    Soma.Diagnostic.Pretty.Substrate.decorateBinary ctx pp v1 v2 src baseDiag (path := path)
  | .unificationFailed (.spineLengthMismatch _ _ path (some (v1, v2))) _ span _ _ =>
    let src := s!"{span.start.line}:{span.start.column}"
    Soma.Diagnostic.Pretty.Substrate.decorateBinary ctx pp v1 v2 src baseDiag (path := path)
  | .typeMismatch expected actual _ _ actualSpan _ =>
    let src := s!"{actualSpan.start.line}:{actualSpan.start.column}"
    Soma.Diagnostic.Pretty.Substrate.decorateBinary ctx pp expected actual src baseDiag
  | .expectedFunction actual span _ =>
    let src := s!"{span.start.line}:{span.start.column}"
    attachUnary ctx actual s!"<actual at {src}>" "not a function" baseDiag
  | .fieldNotFound _field recordTy span _ _ =>
    let src := s!"{span.start.line}:{span.start.column}"
    attachUnary ctx recordTy s!"<record at {src}>" "this record type" baseDiag
  | .unsolvedMeta ty span _ _ ctxLocals =>
    let src := s!"{span.start.line}:{span.start.column}"
    if ctxLocals.isEmpty then
      attachUnary ctx ty s!"<expected at {src}>" "expected type" baseDiag
    else
      let hyps : List Soma.Diagnostic.Pretty.Substrate.GoalHyp :=
        ctxLocals.map fun (n, t) =>
          { name := n, type := Soma.Core.Value.pp pp t }
      let (ctx', _, lbl) :=
        ctx.putGoalSubstrate pp hyps ty s!"<goal at {src}>"
          "this goal is unsolved" Psychopomp.LabelStyle.support
      (ctx', { baseDiag with secondary := baseDiag.secondary ++ [lbl] })
  | .impossiblePattern _ctor ctorTy scrutTy span =>
    let src := s!"{span.start.line}:{span.start.column}"
    Soma.Diagnostic.Pretty.Substrate.decorateBinary ctx pp scrutTy ctorTy src baseDiag
  | _ => (ctx, baseDiag)

end TCError

/-- Collection of type checking errors -/
abbrev TCErrors := Array TCError

namespace TCErrors

/-- Convert all errors to diagnostics with substrate decoration -/
def toDiagnosticsDecorated (ctx : DiagContext) (pp : Soma.Core.PpContext)
    (errs : TCErrors) : DiagContext × Array Diagnostic := Id.run do
  let mut c := ctx
  let mut diags : Array Diagnostic := #[]
  for e in errs do
    let (c', d) := TCError.toDiagnosticDecorated c pp e
    c := c'
    diags := diags.push d
  return (c, diags)

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
