import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quantity
import Soma.Core.Primitive
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Unify
import Soma.Metal.Expr
import Soma.Syntax.Source
import Soma.Unique

namespace Soma.Dependent

open Soma (Unique)
open Soma.Core
open Soma.Metal (Name Expr BinderInfo)
open Soma.Syntax (Span)

/-- Module name for built-in classes -/
def builtinModule : String := "Soma.Prelude"

/-- Create a built-in class unique -/
def mkBuiltinClassId (name : String) (uid : Nat) : Unique :=
  { id := uid, module := builtinModule, original := name }

namespace BuiltinClass
  def eq : Unique := mkBuiltinClassId "Eq" 0
  def ord : Unique := mkBuiltinClassId "Ord" 1
  def show_ : Unique := mkBuiltinClassId "Show" 2
  def num : Unique := mkBuiltinClassId "Num" 3
  def functor : Unique := mkBuiltinClassId "Functor" 4
  def monad : Unique := mkBuiltinClassId "Monad" 5
  def applicative : Unique := mkBuiltinClassId "Applicative" 6
end BuiltinClass

/-- Default maximum depth for instance resolution -/
def defaultInstanceMaxDepth : Nat := 100

/-- Configuration for instance resolution -/
structure InstanceResolutionConfig where
  /-- Maximum search depth before giving up -/
  maxDepth : Nat := defaultInstanceMaxDepth
  deriving Inhabited

/-- State for instance resolution (tracks search to prevent loops) -/
structure ResolutionState where
  /-- Goals we're currently trying to solve (for cycle detection) -/
  activeGoals : Array (Unique × Array Value) := #[]
  /-- Maximum search depth (from configuration) -/
  maxDepth : Nat := defaultInstanceMaxDepth
  /-- Current depth -/
  depth : Nat := 0
  /-- Metavariables created during this resolution (for rollback) -/
  createdMetas : Array MetaId := #[]
  deriving Inhabited

namespace ResolutionState

def empty : ResolutionState := {}

/-- Check if we've exceeded max depth -/
def tooDeep (s : ResolutionState) : Bool :=
  s.depth >= s.maxDepth

/-- Increment depth -/
def deeper (s : ResolutionState) : ResolutionState :=
  { s with depth := s.depth + 1 }

/-- Add an active goal (for cycle detection) -/
def pushGoal (s : ResolutionState) (classId : Unique) (args : Array Value)
    : ResolutionState :=
  { s with activeGoals := s.activeGoals.push (classId, args) }

/-- Remove an active goal -/
def popGoal (s : ResolutionState) : ResolutionState :=
  { s with activeGoals := s.activeGoals.pop }

/-- Record a created metavariable -/
def recordMeta (s : ResolutionState) (m : MetaId) : ResolutionState :=
  { s with createdMetas := s.createdMetas.push m }

/-- Check if a goal is already active (cycle detection).
    Uses structural equality on heads to avoid expensive conversion. -/
def isActive (s : ResolutionState) (classId : Unique) (args : Array Value) : Bool :=
  s.activeGoals.any fun (cid, as) =>
    cid == classId && as.size == args.size && Id.run do
      -- Quick structural check on value heads
      for i in [:as.size] do
        if let (some a1, some a2) := (as[i]?, args[i]?) then
          -- Compare value heads structurally (fast check)
          if !valueHeadsMatch a1 a2 then
            return false
        else
          return false
      return true
where
  /-- Quick structural comparison of value heads -/
  valueHeadsMatch (v1 v2 : Value) : Bool :=
    match v1, v2 with
    | .vPrimTy p1, .vPrimTy p2 => p1 == p2
    | .vType l1, .vType l2 => l1 == l2
    | .vLabelLit s1, .vLabelLit s2 => s1 == s2
    | .vRowSort, .vRowSort => true
    | .vLabelSort, .vLabelSort => true
    | .vDataType id1 _, .vDataType id2 _ => id1 == id2
    | .vNeutral _ (.nMeta m1), .vNeutral _ (.nMeta m2) => m1 == m2
    | .vNeutral _ (.nVar v1), .vNeutral _ (.nVar v2) => v1.level == v2.level
    | _, _ => false  -- Different heads or complex values

end ResolutionState

/-- Result of instance resolution -/
inductive ResolutionResult where
  /-- Successfully found an instance -/
  | found (value : Value) (usedInstances : Array Unique)
  /-- No matching instance found -/
  | notFound (classId : Unique) (args : Array Value) (reason : String)
  /-- Resolution would cause an infinite loop -/
  | cycle (classId : Unique) (args : Array Value)
  /-- Search depth exceeded -/
  | depthExceeded (classId : Unique)
  deriving Inhabited

namespace ResolutionResult

def isFound : ResolutionResult → Bool
  | .found _ _ => true
  | _ => false

def getValue? : ResolutionResult → Option Value
  | .found v _ => some v
  | _ => none

def getClassId? : ResolutionResult → Option Unique
  | .notFound cid _ _ => some cid
  | .cycle cid _ => some cid
  | .depthExceeded cid => some cid
  | .found _ _ => none

def toString : ResolutionResult → String
  | .found _ ids => s!"found (used {ids.size} instances)"
  | .notFound cid _ reason => s!"not found for '{cid.original}': {reason}"
  | .cycle cid _ => s!"cycle detected: {cid.original}"
  | .depthExceeded cid => s!"search depth exceeded: {cid.original}"

instance : ToString ResolutionResult := ⟨ResolutionResult.toString⟩

end ResolutionResult

/-- Result of trying to match an instance -/
inductive MatchResult where
  /-- Instance matches with the given substitutions -/
  | matched (instValue : Value) (substitutions : Array (MetaId × Value))
  /-- Instance doesn't match -/
  | noMatch
  /-- Matching failed with an error -/
  | error (msg : String)
  deriving Inhabited

/-- Try to match instance arguments against goal arguments using unification.
    Creates fresh metavariables for polymorphic type parameters in the instance.
    Returns the instantiated instance value if matching succeeds. -/
def tryMatchInstanceUnify (inst : InstanceInfo) (goalArgs : Array Value)
    : TCM MatchResult := do
  if inst.args.size != goalArgs.size then
    return .noMatch

  -- Save state for potential rollback
  let stateBefore ← TCM.getState

  -- Create fresh metavariables for any polymorphic parameters in the instance
  let mut substitutions : Array (MetaId × Value) := #[]

  -- Try to unify each argument
  for i in [:inst.args.size] do
    if let (some instArg, some goalArg) := (inst.args[i]?, goalArgs[i]?) then
      let instArg' ← force instArg
      let goalArg' ← force goalArg

      -- Try unification - this will solve metavariables
      let unifyResult := (unify instArg' goalArg').run'
      match unifyResult with
      | .ok () => pure ()
      | .error e =>
        -- Unification failed - restore state and return error with details
        TCM.modifyState fun _ => stateBefore
        return .error s!"unification failed: {e}"

  -- Check that all created metas during unification are solved and collect the substitutions
  let stateAfter ← TCM.getState
  for id in [stateBefore.metas.nextId:stateAfter.metas.nextId] do
    let metaId : MetaId := ⟨id⟩
    if let some info := stateAfter.metas.lookup metaId then
      if let some sol := info.solution then
        substitutions := substitutions.push (metaId, sol)

  return .matched inst.value substitutions

/-- Check if an instance matches a goal using unification -/
def matchInstance (inst : InstanceInfo) (classId : Unique) (args : Array Value)
    : TCM (Option Value) := do
  -- Check class id matches
  if inst.classId != classId then
    return none

  -- Try to match arguments using unification
  match ← tryMatchInstanceUnify inst args with
  | .matched value _ => return some value
  | .noMatch => return none
  | .error msg =>
    -- Log the error for debugging but return none to try other instances
    TCM.debug s!"Instance matching error: {msg}"
    return none

mutual

/-- Resolve superclass constraints for a class
    Returns the superclass instance values if all can be resolved -/
partial def resolveSuperclasses (classInfo : ClassInfo) (args : Array Value)
    (state : ResolutionState) : TCM (Option (Array Value)) := do
  if classInfo.superclasses.isEmpty then
    return some #[]

  let mut superInstances : Array Value := #[]

  for (superclassId, paramIndices) in classInfo.superclasses do
    -- Build superclass arguments from the class arguments using the indices
    let mut superArgs : Array Value := #[]
    for idx in paramIndices do
      if let some arg := args[idx]? then
        superArgs := superArgs.push arg
      else
        return none -- Invalid index

    -- Recursively resolve the superclass
    let result ← resolveInstance superclassId superArgs state
    match result with
    | .found value _ =>
      superInstances := superInstances.push value
    | _ =>
      return none -- Superclass resolution failed

  return some superInstances

/-- Resolve an instance for a type class constraint -/
partial def resolveInstance (classId : Unique) (args : Array Value)
    (state : ResolutionState := ResolutionState.empty) : TCM ResolutionResult := do
  -- Check depth limit
  if state.tooDeep then
    return .depthExceeded classId

  -- Check for cycles (using fast structural check)
  if state.isActive classId args then
    return .cycle classId args

  -- Add this goal to active set
  let state' := state.pushGoal classId args |>.deeper

  -- Look up class info for superclass resolution
  let classInfo ← TCM.lookupClass classId

  -- Look up instances for this class
  let instances ← TCM.getClassInstances classId
  if instances.isEmpty then
    return .notFound classId args s!"no instances registered for class '{classId.original}'"

  -- Try each instance
  for inst in instances do
    -- Save state for rollback if this instance doesn't work
    let stateBefore ← TCM.getState

    -- Check if instance matches using unification
    match ← matchInstance inst classId args with
    | some value =>
      -- Instance matches! Now check constraints

      -- 1. Check instance's own constraints
      let constraintsSatisfied ← do
        if inst.isGround then
          pure true
        else
          let mut allSatisfied := true
          for (constraintClassId, constraintArgs) in inst.constraints do
            let result ← resolveInstance constraintClassId constraintArgs state'
            match result with
            | .found _ _ => pure ()
            | _ =>
              allSatisfied := false
              break
          pure allSatisfied

      if !constraintsSatisfied then
        -- Rollback and try next instance
        TCM.modifyState fun _ => stateBefore
        continue

      -- 2. Check superclass constraints (if we have class info)
      let superclassesSatisfied ← do
        match classInfo with
        | some info =>
          match ← resolveSuperclasses info args state' with
          | some _ => pure true
          | none => pure false
        | none => pure true -- No class info, skip superclass check

      if !superclassesSatisfied then
        -- Rollback and try next instance
        TCM.modifyState fun _ => stateBefore
        continue

      -- All constraints satisfied!
      return .found value #[inst.instanceId]

    | none =>
      -- Instance doesn't match, try next
      continue

  return .notFound classId args s!"no matching instance for '{classId.original}' with given arguments"

end

/-- Resolve an instance, returning just the value or none -/
def resolveInstanceValue (classId : Unique) (args : Array Value) : TCM (Option Value) := do
  let result ← resolveInstance classId args
  return result.getValue?

/-- Detailed failure information for instance resolution -/
structure InstanceFailure where
  metaId : MetaId
  classId : Unique
  args : Array Value
  reason : String
  span : Span

instance : Inhabited InstanceFailure where
  default := {
    metaId := ⟨0⟩
    classId := { id := 0, module := "", original := "" }
    args := #[]
    reason := ""
    span := Span.uninhabited
  }

/-- Solve all pending instance constraints -/
def solvePendingInstances : TCM (Array InstanceFailure) := do
  let pending ← TCM.getPendingInstances
  let mut failures : Array InstanceFailure := #[]

  for p in pending do
    let result ← resolveInstance p.classId p.args
    match result with
    | .found value _ =>
      TCM.solveMeta p.metaId value
    | .notFound classId args reason =>
      failures := failures.push {
        metaId := p.metaId
        classId := classId
        args := args
        reason := reason
        span := p.span
      }
    | .cycle classId args =>
      failures := failures.push {
        metaId := p.metaId
        classId := classId
        args := args
        reason := "cycle in instance resolution"
        span := p.span
      }
    | .depthExceeded classId =>
      failures := failures.push {
        metaId := p.metaId
        classId := classId
        args := #[]
        reason := "instance search depth exceeded"
        span := p.span
      }

  -- Clear pending instances after processing
  TCM.clearPendingInstances
  return failures

/-- Solve pending instances and accumulate errors for all failures -/
def solvePendingInstancesOrFail : TCM Unit := do
  let failures ← solvePendingInstances
  for failure in failures do
    match failure.reason with
    | "cycle in instance resolution" =>
      TCM.addError (.instanceCycle failure.classId failure.span #[])
    | "instance search depth exceeded" =>
      TCM.addError (.instanceDepthExceeded failure.classId failure.span #[])
    | _ =>
      TCM.addError (.noInstance failure.classId failure.args failure.span #[] #[])

/-- Create an empty closure for non-dependent types -/
private def mkSimpleClosure (name : String) : Closure :=
  Closure.mkEmpty name Env.empty

/-- Create a placeholder function value for instance methods -/
private def mkMethodPlaceholder (name : String) : Value :=
  -- Create a lambda that returns a placeholder
  -- todo: use the actual method implementation
  Value.vLam name (mkSimpleClosure name)

/-- Build the default instance environment with common classes -/
def defaultInstanceEnv : InstanceEnv := Id.run do
  let mut env := InstanceEnv.forModule builtinModule

  let eqRecordType := Value.vPi .omega .explicit "a" (.vType .zero) (mkSimpleClosure "Eq")
  env := env.addClass {
    classId := BuiltinClass.eq
    numParams := 1
    paramQuantities := #[.omega] -- Type parameter is unrestricted
    recordType := eqRecordType
    superclasses := #[]
    span := Span.uninhabited
  }

  let ordRecordType := Value.vPi .omega .explicit "a" (.vType .zero) (mkSimpleClosure "Ord")
  env := env.addClass {
    classId := BuiltinClass.ord
    numParams := 1
    paramQuantities := #[.omega]
    recordType := ordRecordType
    superclasses := #[(BuiltinClass.eq, #[0])] -- Ord a requires Eq a
    span := Span.uninhabited
  }

  let showRecordType := Value.vPi .omega .explicit "a" (.vType .zero) (mkSimpleClosure "Show")
  env := env.addClass {
    classId := BuiltinClass.show_
    numParams := 1
    paramQuantities := #[.omega]
    recordType := showRecordType
    superclasses := #[]
    span := Span.uninhabited
  }

  let numRecordType := Value.vPi .omega .explicit "a" (.vType .zero) (mkSimpleClosure "Num")
  env := env.addClass {
    classId := BuiltinClass.num
    numParams := 1
    paramQuantities := #[.omega]
    recordType := numRecordType
    superclasses := #[]
    span := Span.uninhabited
  }

  let starToStar := Value.vPi .omega .explicit "_" (.vType .zero) (mkSimpleClosure "_")
  let functorRecordType := Value.vPi .omega .explicit "f" starToStar (mkSimpleClosure "Functor")
  env := env.addClass {
    classId := BuiltinClass.functor
    numParams := 1
    paramQuantities := #[.omega]
    recordType := functorRecordType
    superclasses := #[]
    span := Span.uninhabited
  }

  let applicativeRecordType := Value.vPi .omega .explicit "f" starToStar (mkSimpleClosure "Applicative")
  env := env.addClass {
    classId := BuiltinClass.applicative
    numParams := 1
    paramQuantities := #[.omega]
    recordType := applicativeRecordType
    superclasses := #[(BuiltinClass.functor, #[0])]
    span := Span.uninhabited
  }

  let monadRecordType := Value.vPi .omega .explicit "m" starToStar (mkSimpleClosure "Monad")
  env := env.addClass {
    classId := BuiltinClass.monad
    numParams := 1
    paramQuantities := #[.omega]
    recordType := monadRecordType
    superclasses := #[(BuiltinClass.applicative, #[0])]  -- Monad m requires Applicative m
    span := Span.uninhabited
  }

  for prim in [StarPrimitive.int, .long, .short, .byte, .float, .double, .bool, .string] do
    let primTy := Value.vPrimTy prim
    -- Create an instance value that's a record with the eq method
    let eqMethod := mkMethodPlaceholder "eq"
    let instValue := Value.vRecordVal [("eq", eqMethod)]
    env := env.addInstance BuiltinClass.eq #[primTy] #[.omega] #[] instValue

  for prim in [StarPrimitive.int, .long, .short, .byte, .float, .double] do
    let primTy := Value.vPrimTy prim
    let compareMethod := mkMethodPlaceholder "compare"
    let instValue := Value.vRecordVal [("compare", compareMethod)]
    env := env.addInstance BuiltinClass.ord #[primTy] #[.omega]
      #[(BuiltinClass.eq, #[primTy])] instValue

  for prim in [StarPrimitive.int, .long, .short, .byte, .float, .double, .bool, .string] do
    let primTy := Value.vPrimTy prim
    let showMethod := mkMethodPlaceholder "show"
    let instValue := Value.vRecordVal [("show", showMethod)]
    env := env.addInstance BuiltinClass.show_ #[primTy] #[.omega] #[] instValue

  for prim in [StarPrimitive.int, .long, .short, .byte, .float, .double] do
    let primTy := Value.vPrimTy prim
    let addMethod := mkMethodPlaceholder "add"
    let subMethod := mkMethodPlaceholder "sub"
    let mulMethod := mkMethodPlaceholder "mul"
    let negMethod := mkMethodPlaceholder "neg"
    let fromIntMethod := mkMethodPlaceholder "fromInt"
    let instValue := Value.vRecordVal [
      ("add", addMethod),
      ("sub", subMethod),
      ("mul", mulMethod),
      ("neg", negMethod),
      ("fromInt", fromIntMethod)
    ]
    env := env.addInstance BuiltinClass.num #[primTy] #[.omega] #[] instValue

  return env

/-- Create a TCContext with the default instance environment -/
def TCContext.withDefaultInstances (ctx : TCContext := TCContext.empty) : TCContext :=
  { ctx with instanceEnv := defaultInstanceEnv }

end Soma.Dependent
