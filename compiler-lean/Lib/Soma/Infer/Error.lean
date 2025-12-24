/-
  Type Inference Errors

  Key improvement over the old Haskell design: errors store spans directly,
  not expressions. This eliminates the "magic spans" workaround where dummy
  expressions were created just to carry span information.
-/

import Soma.Typing
import Soma.Syntax.Diagnostic

namespace Soma.Infer

open Soma.Syntax
open Soma.Typing

/-- The purpose of a unification - provides context for error messages -/
inductive UnifyPurpose where
  /-- Unifying function body with declared return type -/
  | functionBody (fnName : String)
  /-- Unifying argument type with parameter type -/
  | functionArg (fnName : String) (argIndex : Nat)
  /-- Unifying if condition with Bool -/
  | ifCondition
  /-- Unifying if branches to have same type -/
  | ifBranches
  /-- Unifying case arm bodies to have same type -/
  | caseArms
  /-- Unifying pattern with scrutinee type -/
  | patternMatch
  /-- Unifying let binding value with declared type -/
  | letBinding (name : String)
  /-- Unifying binary operator operands -/
  | binaryOp (op : String)
  /-- Unifying array elements to have same type -/
  | arrayElements
  /-- Unifying tuple element -/
  | tupleElement (index : Nat)
  /-- Unifying field access -/
  | fieldAccess (fieldName : String)
  /-- Unifying with explicit type annotation -/
  | typeAnnotation
  /-- General unification (fallback) -/
  | general
  deriving Repr, BEq, Inhabited

namespace UnifyPurpose

def describe : UnifyPurpose → String
  | .functionBody fn => s!"in return type of function '{fn}'"
  | .functionArg fn idx => s!"in argument {idx + 1} of call to '{fn}'"
  | .ifCondition => "in if condition"
  | .ifBranches => "in if/else branches"
  | .caseArms => "in case expression arms"
  | .patternMatch => "in pattern match"
  | .letBinding name => s!"in let binding '{name}'"
  | .binaryOp op => s!"in binary operator '{op}'"
  | .arrayElements => "in array literal elements"
  | .tupleElement idx => s!"in tuple element {idx + 1}"
  | .fieldAccess field => s!"in field access '.{field}'"
  | .typeAnnotation => "in type annotation"
  | .general => ""

end UnifyPurpose

/-- Type inference errors with direct span information -/
inductive InferError where
  /-- Type mismatch during unification -/
  | typeMismatch
      (expected : MonoTy)
      (actual : MonoTy)
      (purpose : UnifyPurpose)
      (expectedSpan : Span)
      (actualSpan : Span)

  /-- Kind mismatch during unification -/
  | kindMismatch
      (expected : Kind)
      (actual : Kind)
      (span : Span)

  /-- Occurs check failed (infinite type) -/
  | occursCheck
      (varId : TyVarId)
      (ty : MonoTy)
      (span : Span)

  /-- Unknown variable reference -/
  | unknownVariable
      (name : String)
      (span : Span)

  /-- Unknown type constructor -/
  | unknownType
      (name : String)
      (span : Span)

  /-- Unknown type class -/
  | unknownTypeClass
      (name : String)
      (span : Span)

  /-- No instance found for constraint -/
  | noInstance
      (constraint : Constraint)
      (span : Span)

  /-- Ambiguous type variable (not resolved after inference) -/
  | ambiguousType
      (varId : TyVarId)
      (span : Span)

  /-- Wrong number of type arguments -/
  | wrongTypeArity
      (typeName : String)
      (expected : Nat)
      (actual : Nat)
      (span : Span)

  /-- Tuple has too many elements -/
  | tupleTooLarge
      (size : Nat)
      (span : Span)

  /-- Wrong number of function arguments -/
  | wrongArgCount
      (fnName : String)
      (expected : Nat)
      (actual : Nat)
      (span : Span)

  /-- Applying a non-function type -/
  | notAFunction
      (ty : MonoTy)
      (span : Span)

  /-- Pattern doesn't match scrutinee type -/
  | patternTypeMismatch
      (expected : MonoTy)
      (patternSpan : Span)

  /-- Constructor not found -/
  | unknownConstructor
      (name : String)
      (span : Span)

  /-- Field not found on type -/
  | unknownField
      (typeName : String)
      (fieldName : String)
      (span : Span)

  /-- Cannot infer type (need annotation) -/
  | cannotInfer
      (context : String)
      (span : Span)

  /-- Duplicate definition -/
  | duplicateDefinition
      (name : String)
      (firstSpan : Span)
      (secondSpan : Span)

  /-- Constraint not satisfied by instance -/
  | constraintNotSatisfied
      (constraint : Constraint)
      (reason : String)
      (span : Span)

  /-- Recursive type without indirection -/
  | recursiveType
      (typeName : String)
      (span : Span)

  /-- Skolem escape (rigid type variable escaping its scope) -/
  | skolemEscape
      (varName : String)
      (span : Span)

namespace InferError

/-- Get the primary span of an error -/
def span : InferError → Span
  | .typeMismatch _ _ _ _ s => s
  | .kindMismatch _ _ s => s
  | .occursCheck _ _ s => s
  | .unknownVariable _ s => s
  | .unknownType _ s => s
  | .unknownTypeClass _ s => s
  | .noInstance _ s => s
  | .ambiguousType _ s => s
  | .wrongTypeArity _ _ _ s => s
  | .tupleTooLarge _ s => s
  | .wrongArgCount _ _ _ s => s
  | .notAFunction _ s => s
  | .patternTypeMismatch _ s => s
  | .unknownConstructor _ s => s
  | .unknownField _ _ s => s
  | .cannotInfer _ s => s
  | .duplicateDefinition _ _ s => s
  | .constraintNotSatisfied _ _ s => s
  | .recursiveType _ s => s
  | .skolemEscape _ s => s

/-- Convert an InferError to a Diagnostic for rendering -/
def toDiagnostic : InferError → Diagnostic
  | .typeMismatch expected actual purpose expectedSpan actualSpan =>
    let purposeStr := purpose.describe
    let msg := if purposeStr.isEmpty then "type mismatch" else s!"type mismatch {purposeStr}"
    { severity := .error
    , code := some "E0308"
    , message := msg
    , primaryLabel := Label.primary actualSpan s!"expected `{expected}`, found `{actual}`"
    , secondaryLabels := #[Label.secondary expectedSpan s!"expected due to this"]
    , notes := #[]
    , help := none
    }

  | .kindMismatch expected actual span =>
    { severity := .error
    , code := some "E0309"
    , message := "kind mismatch"
    , primaryLabel := Label.primary span s!"expected kind `{expected}`, found kind `{actual}`", secondaryLabels := #[]
    , notes := #[]
    , help := none
    }

  | .occursCheck var ty span =>
    { severity := .error
    , code := some "E0310"
    , message := "infinite type"
    , primaryLabel := Label.primary span s!"type variable `{var.name}` occurs in `{ty}`", secondaryLabels := #[]
    , notes := #["this would create an infinite type like `a = List a`"]
    , help := some "consider using an explicit recursive type wrapper"
    }

  | .unknownVariable name span =>
    { severity := .error
    , code := some "E0425"
    , message := s!"unknown variable `{name}`"
    , primaryLabel := Label.primary span "not found in this scope", secondaryLabels := #[]
    , notes := #[]
    , help := none
    }

  | .unknownType name span =>
    { severity := .error
    , code := some "E0412"
    , message := s!"unknown type `{name}`"
    , primaryLabel := Label.primary span "not found", secondaryLabels := #[]
    , notes := #[]
    , help := none
    }

  | .unknownTypeClass name span =>
    { severity := .error
    , code := some "E0405"
    , message := s!"unknown type class `{name}`"
    , primaryLabel := Label.primary span "not found", secondaryLabels := #[]
    , notes := #[]
    , help := none
    }

  | .noInstance constraint span =>
    { severity := .error
    , code := some "E0277"
    , message := s!"no instance for `{constraint}`"
    , primaryLabel := Label.primary span "required by this", secondaryLabels := #[]
    , notes := #[]
    , help := some s!"consider adding an instance declaration for `{constraint}`"
    }

  | .ambiguousType var span =>
    { severity := .error
    , code := some "E0282"
    , message := s!"type variable `{var.name}` is ambiguous"
    , primaryLabel := Label.primary span "cannot infer type", secondaryLabels := #[]
    , notes := #["the type of this expression could not be fully determined"]
    , help := some "consider adding a type annotation"
    }

  | .wrongTypeArity name expected actual span =>
    let args := if expected == 1 then "argument" else "arguments"
    { severity := .error
    , code := some "E0107"
    , message := s!"wrong number of type arguments for `{name}`"
    , primaryLabel := Label.primary span s!"expected {expected} type {args}, found {actual}", secondaryLabels := #[]
    , notes := #[]
    , help := none
    }

  | .tupleTooLarge size span =>
    { severity := .error
    , code := some "E0108"
    , message := s!"tuple has too many elements ({size})"
    , primaryLabel := Label.primary span "maximum tuple size is 8", secondaryLabels := #[]
    , notes := #[]
    , help := some "consider using a struct or array instead"
    }

  | .wrongArgCount name expected actual span =>
    let args := if expected == 1 then "argument" else "arguments"
    { severity := .error
    , code := some "E0061"
    , message := s!"wrong number of arguments for `{name}`"
    , primaryLabel := Label.primary span s!"expected {expected} {args}, found {actual}", secondaryLabels := #[]
    , notes := #[]
    , help := none
    }

  | .notAFunction ty span =>
    { severity := .error
    , code := some "E0618"
    , message := "expected function"
    , primaryLabel := Label.primary span s!"`{ty}` is not a function", secondaryLabels := #[]
    , notes := #[]
    , help := none
    }

  | .patternTypeMismatch expected span =>
    { severity := .error
    , code := some "E0308"
    , message := "pattern type mismatch"
    , primaryLabel := Label.primary span s!"expected pattern for type `{expected}`", secondaryLabels := #[]
    , notes := #[]
    , help := none
    }

  | .unknownConstructor name span =>
    { severity := .error
    , code := some "E0531"
    , message := s!"unknown constructor `{name}`"
    , primaryLabel := Label.primary span "not found", secondaryLabels := #[]
    , notes := #[]
    , help := none
    }

  | .unknownField typeName fieldName span =>
    { severity := .error
    , code := some "E0609"
    , message := s!"type `{typeName}` has no field `{fieldName}`"
    , primaryLabel := Label.primary span "unknown field", secondaryLabels := #[]
    , notes := #[]
    , help := none
    }

  | .cannotInfer context span =>
    { severity := .error
    , code := some "E0282"
    , message := s!"cannot infer type {context}"
    , primaryLabel := Label.primary span "type annotation needed", secondaryLabels := #[]
    , notes := #[]
    , help := some "add an explicit type annotation"
    }

  | .duplicateDefinition name firstSpan secondSpan =>
    { severity := .error
    , code := some "E0428"
    , message := s!"duplicate definition `{name}`"
    , primaryLabel := Label.primary secondSpan "redefined here"
    , secondaryLabels := #[Label.secondary firstSpan "first defined here"]
    , notes := #[]
    , help := none
    }

  | .constraintNotSatisfied constraint reason span =>
    { severity := .error
    , code := some "E0277"
    , message := s!"constraint `{constraint}` not satisfied"
    , primaryLabel := Label.primary span reason, secondaryLabels := #[]
    , notes := #[]
    , help := none
    }

  | .recursiveType name span =>
    { severity := .error
    , code := some "E0072"
    , message := s!"recursive type `{name}` has infinite size"
    , primaryLabel := Label.primary span "recursive without indirection", secondaryLabels := #[]
    , notes := #[]
    , help := some "insert an indirection (e.g., Box, Ref) to break the cycle"
    }

  | .skolemEscape name span =>
    { severity := .error
    , code := some "E0521"
    , message := s!"type variable `{name}` escapes its scope"
    , primaryLabel := Label.primary span "cannot escape", secondaryLabels := #[]
    , notes := #["rigid type variables introduced by `forall` cannot escape their scope"]
    , help := none
    }

end InferError

/-- Collection of inference errors -/
abbrev InferErrors := Array InferError

namespace InferErrors

/-- Convert all errors to diagnostics -/
def toDiagnostics (errs : InferErrors) : Diagnostics :=
  errs.map InferError.toDiagnostic

/-- Check if there are any errors -/
def hasErrors (errs : InferErrors) : Bool :=
  !errs.isEmpty

end InferErrors

end Soma.Infer
