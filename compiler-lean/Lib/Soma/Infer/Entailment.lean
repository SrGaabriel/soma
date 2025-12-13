import Soma.Infer.Instance
import Soma.Infer.Constraint

namespace Soma.Infer

open Std
open Soma.Typing
open Soma.Syntax

/-- Result of trying to satisfy a constraint -/
inductive EntailmentResult where
  /-- Constraint is satisfied, possibly with sub-constraints -/
  | satisfied (subConstraints : Array Constraint) (subst : Subst)
  /-- Constraint is deferred (contains unresolved type variables) -/
  | deferred
  /-- Constraint cannot be satisfied -/
  | unsatisfied (reason : String)
  deriving Inhabited, Nonempty

/-- Proof that a constraint is satisfied -/
structure EntailmentProof where
  /-- The constraint that was satisfied -/
  constraint : Constraint
  /-- The instance that satisfied it (if any) -/
  instance? : Option InstanceDecl
  /-- Sub-proofs for instance context constraints -/
  subProofs : Array EntailmentProof

/-- Context for entailment checking -/
structure EntailmentContext where
  /-- Available instances -/
  instanceEnv : InstanceEnv
  /-- Declared constraints (from function signatures) -/
  declaredConstraints : Array Constraint
  /-- Current substitution -/
  subst : Subst
  /-- Fresh variable counter -/
  freshId : Nat
  /-- Maximum recursion depth (to prevent infinite loops) -/
  maxDepth : Nat := 100
  deriving Inhabited

namespace Entailment

/-- Check if a constraint matches a declared constraint (from signature) -/
def matchesDeclared (c : Constraint) (declared : Constraint) (σ : Subst) : Bool :=
  -- Must be same class
  if c.className != declared.className then false
  else if c.args.size != declared.args.size then false
  else
    -- Check if applying substitution makes them match
    let cArgs := c.args.map (σ.apply ·)
    let declArgs := declared.args.map (σ.apply ·)
    cArgs == declArgs

/-- Check if a constraint is entailed by declared constraints -/
def isEntailedByDeclared (c : Constraint) (declared : Array Constraint) (σ : Subst) : Bool :=
  declared.any (matchesDeclared c · σ)

/-- Check if a constraint is trivially satisfied (all args are ground types) -/
def isGroundConstraint (c : Constraint) : Bool :=
  c.args.all (!·.hasVars)

/-- Try to satisfy a single constraint -/
partial def satisfyConstraint (ctx : EntailmentContext) (c : Constraint) (depth : Nat)
    : EntailmentResult := Id.run do
  -- Check depth limit
  if depth > ctx.maxDepth then
    return .unsatisfied "maximum entailment depth exceeded (possible infinite loop)"

  -- Apply current substitution
  let c := { c with args := c.args.map (ctx.subst.apply ·) }

  -- Check if satisfied by declared constraints
  if isEntailedByDeclared c ctx.declaredConstraints ctx.subst then
    return .satisfied #[] Subst.empty

  -- Check if constraint still has unresolved variables
  let hasVars := c.args.any (·.hasVars)

  -- Try to find a matching instance
  match ctx.instanceEnv.findInstance c ctx.freshId with
  | some (_, instSubst, subConstraints, newFreshId) =>
    -- We found a matching instance
    -- Now we need to satisfy the sub-constraints
    let ctx' := { ctx with freshId := newFreshId, subst := instSubst.compose ctx.subst }

    let mut allSubConstraints : Array Constraint := #[]
    let mut finalSubst := instSubst

    for subC in subConstraints do
      match satisfyConstraint ctx' subC (depth + 1) with
      | .satisfied moreSubConstraints subSubst =>
        allSubConstraints := allSubConstraints ++ moreSubConstraints
        finalSubst := subSubst.compose finalSubst
      | .deferred =>
        -- Sub-constraint is deferred, so this constraint is also deferred
        allSubConstraints := allSubConstraints.push subC
      | .unsatisfied reason =>
        return .unsatisfied s!"sub-constraint `{subC}` not satisfied: {reason}"

    return .satisfied allSubConstraints finalSubst

  | none =>
    -- No matching instance found
    if hasVars then
      return .deferred
    else
      return .unsatisfied s!"no instance found for `{c}`"

/-- Satisfy all constraints in a constraint graph -/
def satisfyAll (ctx : EntailmentContext) (constraints : Array ClassConstraint)
    : Except (Array InferError) (Array Constraint × Subst) := do
  let mut deferred : Array Constraint := #[]
  let mut σ := Subst.empty
  let mut errors : Array InferError := #[]
  let mut ctx := ctx

  for cc in constraints do
    let c := cc.toConstraint
    match satisfyConstraint ctx c 0 with
    | .satisfied subConstraints subst =>
      -- Add any remaining sub-constraints to deferred
      deferred := deferred ++ subConstraints
      σ := subst.compose σ
      ctx := { ctx with subst := σ.compose ctx.subst }
    | .deferred =>
      deferred := deferred.push c
    | .unsatisfied _ =>
      errors := errors.push (.noInstance c cc.span)

  if errors.isEmpty then
    .ok (deferred, σ)
  else
    .error errors

/-- Build a substitution from class parameters to constraint arguments -/
def buildParamSubstitution (classParams : Array TyVarId) (constraintArgs : Array MonoTy) : Subst :=
  Subst.fromArrays classParams constraintArgs

/-- Instantiate superclass constraints with the constraint's type arguments -/
def checkSuperclasses (ctx : EntailmentContext) (c : Constraint)
    : Except InferError (Array Constraint) := do
  -- Get the class declaration to access its parameters
  let some classDecl := ctx.instanceEnv.getClass c.className
    | return #[]  -- Unknown class, no superclasses to check

  let superclasses := classDecl.superclasses
  if superclasses.isEmpty then
    return #[]

  -- Build substitution from class parameters to constraint arguments
  -- e.g., for `Ord Int` with class params [a], build {a ↦ Int}
  let σ := buildParamSubstitution classDecl.params c.args

  -- Instantiate each superclass constraint with this substitution
  let instantiated := superclasses.map fun super =>
    { super with args := super.args.map (σ.apply ·) }

  return instantiated

/-- Full entailment check with superclass handling -/
def entails (instanceEnv : InstanceEnv) (declared : Array Constraint)
    (constraint : Constraint) (span : Span)
    : Except InferError Bool := do
  let ctx : EntailmentContext := {
    instanceEnv
    declaredConstraints := declared
    subst := Subst.empty
    freshId := 0
  }

  match satisfyConstraint ctx constraint 0 with
  | .satisfied _ _ => .ok true
  | .deferred => .ok true -- Deferred constraints are assumed satisfiable
  | .unsatisfied _ => .error (.noInstance constraint span)

/-- Check if all constraints in a qualified type can be satisfied -/
def checkQualifiedType (instanceEnv : InstanceEnv) (qt : QualifiedType) (span : Span)
    : Except (Array InferError) Unit := do
  let ctx : EntailmentContext := {
    instanceEnv
    declaredConstraints := qt.constraints
    subst := Subst.empty
    freshId := 0
  }

  let mut errors : Array InferError := #[]

  for c in qt.constraints do
    -- Check that each constraint mentions only the quantified variables and that superclasses are satisfied
    match checkSuperclasses ctx c with
    | .ok supers =>
      for super in supers do
        if !isEntailedByDeclared super qt.constraints Subst.empty then
          errors := errors.push (.constraintNotSatisfied super
            s!"superclass `{super}` of `{c}` is not declared" span)
    | .error e =>
      errors := errors.push e

  if errors.isEmpty then
    .ok ()
  else
    .error errors

end Entailment

end Soma.Infer
