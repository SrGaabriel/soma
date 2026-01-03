import Soma.Core.Value
import Soma.Core.Quantity
import Soma.Core.Level
import Soma.Core.Eval
import Soma.Dependent.Error
import Soma.Metal.Expr
import Soma.Syntax.Source
import Soma.Unique
import Std.Data.HashMap

namespace Soma.Dependent

open Soma (Unique)
open Soma.Core
open Soma.Metal (Name Expr BinderInfo)
open Soma.Syntax (Span)

/-- An entry in the typing context -/
structure CtxEntry where
  /-- Variable name -/
  name : String
  /-- Variable's type (as a Value) -/
  type : Value
  /-- Quantity annotation -/
  qty : Quantity
  /-- De Bruijn level -/
  level : DeBruijnLvl
  /-- How this variable is bound -/
  binder : BinderInfo
  /-- Span where variable was introduced -/
  span : Span
  deriving Inhabited

/-- A constraint that couldn't be solved immediately -/
inductive Constraint where
  /-- Unify two values -/
  | unify (v1 v2 : Value) (span : Span)
  /-- Check that v1 is a subtype of v2 -/
  | subtype (v1 v2 : Value) (span : Span)
  /-- Solve a level constraint -/
  | levelEq (l1 l2 : Level)
  /-- Solve a level ordering -/
  | levelLe (l1 l2 : Level)
  deriving Inhabited

/-- A tracked constraint with its ID and the metas it references -/
structure TrackedConstraint where
  /-- The underlying constraint -/
  constraint : Constraint
  /-- Constraint ID for dependency tracking -/
  constraintId : ConstraintId
  /-- Metas referenced by this constraint (cached for efficiency) -/
  metas : Array MetaId
  deriving Inhabited

/-- Information about a global definition -/
structure GlobalInfo where
  /-- The canonical Name for this definition -/
  name : Soma.Core.Name
  /-- The type of the definition -/
  type : Value
  /-- The value (for unfolding), if available -/
  value : Option Value := none
  /-- Whether this is a constructor -/
  isConstructor : Bool := false
  /-- Constructor tag (if isConstructor) -/
  ctorTag : Nat := 0

instance : Inhabited GlobalInfo where
  default := {
    name := .user { id := 0, module := "", original := "" }
    type := .vType .zero
  }

/-- Global environment mapping names to their info -/
structure Globals where
  defs : Std.HashMap String GlobalInfo := {}
  /-- Registry mapping type names to their TypeIds -/
  typeIds : Std.HashMap String Soma.Core.TypeId := {}
  deriving Inhabited

namespace Globals

def empty : Globals := ⟨{}, {}⟩

def insert (g : Globals) (name : String) (info : GlobalInfo) : Globals :=
  { g with defs := g.defs.insert name info }

def lookup (g : Globals) (name : String) : Option GlobalInfo :=
  g.defs.get? name

/-- Register a TypeId for a type name -/
def registerTypeId (g : Globals) (name : String) (id : Soma.Core.TypeId) : Globals :=
  { g with typeIds := g.typeIds.insert name id }

/-- Look up a TypeId by name -/
def lookupTypeId (g : Globals) (name : String) : Option Soma.Core.TypeId :=
  g.typeIds.get? name

/-- Convert Globals to GlobalEnv (for evaluation context) -/
def toGlobalEnv (g : Globals) : GlobalEnv :=
  let entries := g.defs.toList
  entries.foldl (fun acc (name, info) =>
    match info.value with
    | some v => acc.insert name v
    | none => acc
  ) GlobalEnv.empty

end Globals

/-- Information about a type class (represented as a record type) -/
structure ClassInfo where
  /-- The class unique identifier -/
  classId : Unique
  /-- Number of type parameters -/
  numParams : Nat
  /-- Quantity annotations for each type parameter (for QTT) -/
  paramQuantities : Array Quantity := #[]
  /-- The record type representing this class (as a Value) -/
  recordType : Value
  /-- Superclass constraints (class uniques with their parameter indices) -/
  superclasses : Array (Unique × Array Nat)
  /-- Source span for error reporting -/
  span : Span

instance : Inhabited ClassInfo where
  default := {
    classId := { id := 0, module := "", original := "" }
    numParams := 0
    paramQuantities := #[]
    recordType := Value.vType .zero
    superclasses := #[]
    span := Span.uninhabited
  }

namespace ClassInfo

/-- Display name for error messages -/
def displayName (c : ClassInfo) : String := c.classId.original

end ClassInfo

/-- Information about a registered instance -/
structure InstanceInfo where
  /-- Unique identifier for this instance -/
  instanceId : Unique
  /-- The class this is an instance for -/
  classId : Unique
  /-- The type arguments to the class (as Values) -/
  args : Array Value
  /-- Quantity annotations for each type argument (for QTT) -/
  argQuantities : Array Quantity := #[]
  /-- Constraints required by this instance (class unique × args) -/
  constraints : Array (Unique × Array Value)
  /-- The instance value (a record value) -/
  value : Value
  /-- Source span for error reporting -/
  span : Span

instance : Inhabited InstanceInfo where
  default := {
    instanceId := { id := 0, module := "", original := "" }
    classId := { id := 0, module := "", original := "" }
    args := #[]
    argQuantities := #[]
    constraints := #[]
    value := Value.vType .zero
    span := Span.uninhabited
  }

namespace InstanceInfo

/-- Check if this instance has no constraints (is a ground instance) -/
def isGround (i : InstanceInfo) : Bool :=
  i.constraints.isEmpty

/-- Display name for error messages -/
def displayName (i : InstanceInfo) : String := i.instanceId.original

end InstanceInfo

/-- Environment tracking all type classes and their instances -/
structure InstanceEnv where
  /-- All registered classes, indexed by unique id -/
  classes : Std.HashMap Unique ClassInfo := {}
  /-- All registered instances, indexed by class unique -/
  instances : Std.HashMap Unique (Array InstanceInfo) := {}
  /-- Next instance ID counter (for generating synthetic instance uniques) -/
  nextInstanceId : Nat := 0
  /-- Module name for generating instance uniques -/
  moduleName : String := ""
  deriving Inhabited

namespace InstanceEnv

/-- Create an empty instance environment -/
def empty : InstanceEnv := {}

/-- Create an instance environment for a module -/
def forModule (moduleName : String) : InstanceEnv :=
  { moduleName := moduleName }

/-- Register a new type class -/
def addClass (env : InstanceEnv) (info : ClassInfo) : InstanceEnv :=
  { env with classes := env.classes.insert info.classId info }

/-- Register a new instance with explicit unique -/
def addInstanceWithId (env : InstanceEnv) (info : InstanceInfo) : InstanceEnv :=
  let existing := env.instances.getD info.classId #[]
  { env with instances := env.instances.insert info.classId (existing.push info) }

/-- Register a new instance, generating a unique if not provided -/
def addInstance (env : InstanceEnv) (classId : Unique) (args : Array Value)
    (argQuantities : Array Quantity)
    (constraints : Array (Unique × Array Value)) (value : Value)
    (instanceName : Option String := none) (span : Span := Span.uninhabited) : InstanceEnv :=
  let name := instanceName.getD s!"$inst_{classId.original}_{env.nextInstanceId}"
  let instId : Unique := {
    id := env.nextInstanceId
    module := env.moduleName
    original := name
  }
  let info : InstanceInfo := {
    instanceId := instId
    classId := classId
    args := args
    argQuantities := argQuantities
    constraints := constraints
    value := value
    span := span
  }
  let existing := env.instances.getD classId #[]
  { env with
    instances := env.instances.insert classId (existing.push info)
    nextInstanceId := env.nextInstanceId + 1
  }

/-- Look up a class by unique -/
def getClass (env : InstanceEnv) (classId : Unique) : Option ClassInfo :=
  env.classes.get? classId

/-- Look up all instances for a class -/
def getInstances (env : InstanceEnv) (classId : Unique) : Array InstanceInfo :=
  env.instances.getD classId #[]

/-- Check if a class exists -/
def hasClass (env : InstanceEnv) (classId : Unique) : Bool :=
  env.classes.contains classId

/-- Get total number of instances -/
def instanceCount (env : InstanceEnv) : Nat :=
  env.instances.fold (fun acc _ insts => acc + insts.size) 0

end InstanceEnv

/-- A pending instance constraint to be resolved -/
structure PendingInstance where
  /-- The metavariable that needs an instance -/
  metaId : MetaId
  /-- The class unique -/
  classId : Unique
  /-- The class arguments -/
  args : Array Value
  /-- Where this constraint came from -/
  span : Span

instance : Inhabited PendingInstance where
  default := {
    metaId := ⟨0⟩
    classId := { id := 0, module := "", original := "" }
    args := #[]
    span := Span.uninhabited
  }

/-- Mutable state for type checking -/
structure TCState where
  /-- Metavariable state -/
  metas : MetaState := MetaState.empty
  /-- Level variable solutions -/
  levelSolutions : Std.HashMap Nat Level := {}
  /-- Next level variable ID -/
  nextLevelVar : Nat := 0
  /-- Postponed constraints (tracked with IDs and meta references) -/
  postponed : Array TrackedConstraint := #[]
  /-- Worklist of constraint IDs to retry (populated when metas are solved) -/
  worklist : Array ConstraintId := #[]
  /-- Accumulated errors -/
  errors : Array TCError := #[]
  /-- Accumulated warnings -/
  warnings : Array TCWarning := #[]
  /-- Fresh name counter -/
  freshCounter : Nat := 0
  /-- Variable usage counts for QTT tracking (name -> accumulated quantity) -/
  usages : Std.HashMap String Quantity := {}
  /-- Pending instance constraints to be resolved -/
  pendingInstances : Array PendingInstance := #[]
  /-- Unique supply for generating compiler-internal names -/
  uniqueSupply : Soma.UniqueSupply := Soma.UniqueSupply.initial ""
  /-- Registry mapping type names to their TypeIds -/
  typeIds : Std.HashMap String Soma.Core.TypeId := {}
  deriving Inhabited

namespace TCState

def empty : TCState := {}

/-- Create an initial state for a module -/
def forModule (moduleName : String) : TCState :=
  { uniqueSupply := Soma.UniqueSupply.initial moduleName }

/-- Create a fresh metavariable -/
def freshMeta (s : TCState) (ty : Value) (ctx : List CtxEntry) : MetaId × TCState :=
  let ctxList := ctx.map fun e => (e.name, e.type, e.qty)
  let (id, metas') := s.metas.fresh ty ctxList
  (id, { s with metas := metas' })

/-- Create a fresh level variable -/
def freshLevelVar (s : TCState) (name : String := "") : LevelVarId × TCState :=
  let id : LevelVarId := ⟨s.nextLevelVar, name⟩
  (id, { s with nextLevelVar := s.nextLevelVar + 1 })

/-- Solve a metavariable -/
def solveMeta (s : TCState) (id : MetaId) (v : Value) : TCState :=
  { s with metas := s.metas.solve id v }

/-- Look up a metavariable -/
def lookupMeta (s : TCState) (id : MetaId) : Option MetaInfo :=
  s.metas.lookup id

/-- Add a postponed constraint (simple version, for backward compatibility) -/
def postpone (s : TCState) (c : Constraint) : TCState :=
  -- Create a tracked constraint with empty metas (will be populated by caller)
  let tc : TrackedConstraint := {
    constraint := c
    constraintId := ⟨0⟩ -- will be assigned when properly tracked
    metas := #[]
  }
  { s with postponed := s.postponed.push tc }

/-- Add a postponed constraint with full dependency tracking -/
def postponeTracked (s : TCState) (c : Constraint) (metas : Array MetaId)
    : ConstraintId × TCState :=
  -- Register the constraint in the dependency system
  let (cid, metas') := s.metas.registerConstraint metas
  let tc : TrackedConstraint := {
    constraint := c
    constraintId := cid
    metas := metas
  }
  (cid, { s with metas := metas', postponed := s.postponed.push tc })

/-- Add constraint IDs to the worklist (to be retried after a meta is solved) -/
def wakeConstraints (s : TCState) (cids : Array ConstraintId) : TCState :=
  { s with worklist := s.worklist ++ cids }

/-- Pop a constraint ID from the worklist -/
def popWorklist (s : TCState) : Option ConstraintId × TCState :=
  if s.worklist.isEmpty then
    (none, s)
  else
    let cid := s.worklist[0]!
    (some cid, { s with worklist := s.worklist.extract 1 s.worklist.size })

/-- Get a tracked constraint by ID -/
def getConstraint (s : TCState) (cid : ConstraintId) : Option TrackedConstraint :=
  s.postponed.find? (·.constraintId == cid)

/-- Remove a constraint by ID (after it's been solved) -/
def removeConstraint (s : TCState) (cid : ConstraintId) : TCState :=
  let postponed' := s.postponed.filter (·.constraintId != cid)
  let metas' := s.metas.removeConstraint cid
  { s with postponed := postponed', metas := metas' }

/-- Add an error -/
def addError (s : TCState) (e : TCError) : TCState :=
  { s with errors := s.errors.push e }

/-- Add a warning -/
def addWarning (s : TCState) (w : TCWarning) : TCState :=
  { s with warnings := s.warnings.push w }

/-- Generate a fresh name -/
def freshName (s : TCState) (base : String) : String × TCState :=
  let name := s!"{base}_{s.freshCounter}"
  (name, { s with freshCounter := s.freshCounter + 1 })

/-- Generate a fresh unique identifier -/
def freshUnique (s : TCState) (original : String) : Unique × TCState :=
  let (u, supply') := s.uniqueSupply.fresh original
  (u, { s with uniqueSupply := supply' })

/-- Record usage of a variable with a given quantity -/
def useVar (s : TCState) (name : String) (qty : Quantity) : TCState :=
  let current := s.usages.getD name .zero
  let newQty := current.add qty
  { s with usages := s.usages.insert name newQty }

/-- Get the usage of a variable -/
def getUsage (s : TCState) (name : String) : Quantity :=
  s.usages.getD name .zero

/-- Clear usages (for starting a new scope) -/
def clearUsages (s : TCState) : TCState :=
  { s with usages := {} }

/-- Save current usages -/
def saveUsages (s : TCState) : Std.HashMap String Quantity :=
  s.usages

/-- Restore usages -/
def restoreUsages (s : TCState) (usages : Std.HashMap String Quantity) : TCState :=
  { s with usages := usages }

/-- Add a pending instance constraint -/
def addPendingInstance (s : TCState) (p : PendingInstance) : TCState :=
  { s with pendingInstances := s.pendingInstances.push p }

/-- Get all pending instances -/
def getPendingInstances (s : TCState) : Array PendingInstance :=
  s.pendingInstances

/-- Clear pending instances -/
def clearPendingInstances (s : TCState) : TCState :=
  { s with pendingInstances := #[] }

end TCState

/-- Immutable context for type checking -/
structure TCContext where
  /-- Local typing context (most recent binding first) -/
  locals : List CtxEntry := []
  /-- HashMap index for O(1) local lookup by name -/
  localsByName : Std.HashMap String CtxEntry := {}
  /-- NbE environment (values for bound variables) -/
  env : Env := Env.empty
  /-- Global definitions -/
  globals : Globals := Globals.empty
  /-- Instance environment (type classes and instances) -/
  instanceEnv : InstanceEnv := InstanceEnv.empty
  /-- Current span (for error reporting) -/
  currentSpan : Span := Span.uninhabited
  /-- Are we in erased context? (under a 0-quantity binder) -/
  inErased : Bool := false
  /-- Current multiplier for quantity tracking (for nested binders) -/
  qtyMultiplier : Quantity := .omega
  /-- Debug mode: print inference trace -/
  debug : Bool := false
  /-- Current indentation level for debug output -/
  debugIndent : Nat := 0
  deriving Inhabited

namespace TCContext

def empty : TCContext := {}

/-- Create a context with debug mode enabled -/
def withDebug (ctx : TCContext) : TCContext :=
  { ctx with debug := true }

/-- Increase debug indentation -/
def indent (ctx : TCContext) : TCContext :=
  { ctx with debugIndent := ctx.debugIndent + 1 }

/-- Get the current De Bruijn level -/
def level (ctx : TCContext) : DeBruijnLvl :=
  ctx.env.level

/-- Number of local bindings -/
def size (ctx : TCContext) : Nat :=
  ctx.locals.length

/-- Look up a local variable by name (O(1) via HashMap) -/
def lookupLocal (ctx : TCContext) (name : String) : Option CtxEntry :=
  ctx.localsByName.get? name

/-- Look up a local variable by De Bruijn level -/
def lookupLevel (ctx : TCContext) (lvl : DeBruijnLvl) : Option CtxEntry :=
  -- Level 0 is oldest, level (size-1) is newest
  -- List is newest first, so we need to reverse index
  let idx := ctx.size - lvl.lvl - 1
  ctx.locals[idx]?

/-- Look up a global -/
def lookupGlobal (ctx : TCContext) (name : String) : Option GlobalInfo :=
  ctx.globals.lookup name

/-- Extend context with a new binding -/
def extend (ctx : TCContext) (name : String) (ty : Value) (qty : Quantity)
    (binder : BinderInfo) (span : Span) : TCContext :=
  let lvl := ctx.level
  let entry : CtxEntry := {
    name := name
    type := ty
    qty := qty
    level := lvl
    binder := binder
    span := span
  }
  -- Create a neutral variable for NbE
  let varVal := Value.vNeutral ty (Neutral.nVar ⟨name, lvl⟩)
  -- When entering a zero-quantity binder, we enter erased context
  -- and set the quantity multiplier to zero (all usages become erased)
  let enteringErased := qty == .zero
  { ctx with
    locals := entry :: ctx.locals
    localsByName := ctx.localsByName.insert name entry
    env := ctx.env.extend name varVal
    inErased := ctx.inErased || enteringErased
    qtyMultiplier := if enteringErased then .zero else ctx.qtyMultiplier
  }

/-- Update the current span -/
def withSpan (ctx : TCContext) (span : Span) : TCContext :=
  { ctx with currentSpan := span }

end TCContext

/-- Type checking monad: Reader + State + Except -/
abbrev TCM := ReaderT TCContext (StateT TCState (Except TCError))

namespace TCM

/-- Run the TCM with initial context and state -/
def run (m : TCM α) (ctx : TCContext := TCContext.empty)
    (state : TCState := TCState.empty) : Except TCError (α × TCState) :=
  m ctx state

/-- Run and extract just the result -/
def run' (m : TCM α) (ctx : TCContext := TCContext.empty)
    (state : TCState := TCState.empty) : Except TCError α :=
  (m.run ctx state).map (·.1)

/-- Get the current context -/
def getCtx : TCM TCContext := read

/-- Get the current state -/
def getState : TCM TCState := get

/-- Modify the state -/
def modifyState (f : TCState → TCState) : TCM Unit := modify f

/-- Get the current span -/
def getSpan : TCM Span := do
  let ctx ← getCtx
  return ctx.currentSpan

/-- Run with a different span -/
def withSpan (span : Span) (m : TCM α) : TCM α :=
  withReader (·.withSpan span) m

/-- Run with an extended context -/
def withBinding (name : String) (ty : Value) (qty : Quantity)
    (binder : BinderInfo) (span : Span) (m : TCM α) : TCM α :=
  withReader (·.extend name ty qty binder span) m

/-- Look up a local variable -/
def lookupLocal (name : String) : TCM (Option CtxEntry) := do
  let ctx ← getCtx
  return ctx.lookupLocal name

/-- Look up a global -/
def lookupGlobal (name : String) : TCM (Option GlobalInfo) := do
  let ctx ← getCtx
  return ctx.lookupGlobal name

/-- Run with updated globals -/
def withGlobals (globals : Globals) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with globals := globals }) m

/-- Look up a TypeId by name (checks both state and global context) -/
def lookupTypeId (name : String) : TCM (Option Soma.Core.TypeId) := do
  let state ← getState
  -- First check state (where we register new TypeIds)
  match state.typeIds.get? name with
  | some id => return some id
  | none =>
    -- Fall back to globals (for pre-registered TypeIds)
    let ctx ← getCtx
    return ctx.globals.lookupTypeId name

/-- Register a TypeId for a type name -/
def registerTypeId (name : String) (id : Soma.Core.TypeId) : TCM Unit := do
  modifyState fun s => { s with typeIds := s.typeIds.insert name id }

/-- Get the current De Bruijn level -/
def currentLevel : TCM DeBruijnLvl := do
  let ctx ← getCtx
  return ctx.level

/-- Get the NbE environment -/
def getEnv : TCM Env := do
  let ctx ← getCtx
  return ctx.env

/-- Get all local bindings as a list for metavariable context -/
def getLocals : TCM (List CtxEntry) := do
  let ctx ← getCtx
  return ctx.locals

-- todo: remove
/-- Throw a type checking error -/
def throw (e : TCError) : TCM α :=
  Except.error e

/-- Add an error but continue (for error recovery) -/
def addError (e : TCError) : TCM Unit := do
  modifyState (·.addError e)

/-- Add a warning -/
def addWarning (w : TCWarning) : TCM Unit := do
  modifyState (·.addWarning w)

/-- Check if there are errors -/
def hasErrors : TCM Bool := do
  let state ← getState
  return !state.errors.isEmpty

/-- Get all errors -/
def getErrors : TCM (Array TCError) := do
  let state ← getState
  return state.errors

/-- Create a fresh metavariable of the given type -/
def freshMeta (ty : Value) : TCM MetaId := do
  let ctx ← getCtx
  let state ← getState
  let (id, state') := state.freshMeta ty ctx.locals
  set state'
  return id

/-- Create a fresh metavariable and return it as a Value -/
def freshMetaVal (ty : Value) : TCM Value := do
  let id ← freshMeta ty
  return .vNeutral ty (.nMeta id)

/-- Solve a metavariable -/
def solveMeta (id : MetaId) (v : Value) : TCM Unit := do
  modifyState (·.solveMeta id v)

/-- Look up metavariable info -/
def lookupMeta (id : MetaId) : TCM (Option MetaInfo) := do
  let state ← getState
  return state.lookupMeta id

/-- Check if a metavariable is solved -/
def isMetaSolved (id : MetaId) : TCM Bool := do
  let state ← getState
  return state.metas.isSolved id

/-- Create a fresh level variable -/
def freshLevelVar (name : String := "") : TCM LevelVarId := do
  let state ← getState
  let (id, state') := state.freshLevelVar name
  set state'
  return id

/-- Create a fresh level and return it -/
def freshLevel (name : String := "") : TCM Level := do
  let id ← freshLevelVar name
  return .var id

/-- Postpone a constraint for later solving (simple version) -/
def postpone (c : Constraint) : TCM Unit := do
  modifyState (·.postpone c)

/-- Postpone a constraint with full dependency tracking -/
def postponeTracked (c : Constraint) (metas : Array MetaId) : TCM ConstraintId := do
  let state ← getState
  let (cid, state') := state.postponeTracked c metas
  set state'
  return cid

/-- Get all postponed constraints (returns TrackedConstraints) -/
def getPostponedTracked : TCM (Array TrackedConstraint) := do
  let state ← getState
  return state.postponed

/-- Get all postponed constraints (returns just Constraints for backward compat) -/
def getPostponed : TCM (Array Constraint) := do
  let state ← getState
  return state.postponed.map (·.constraint)

/-- Clear postponed constraints -/
def clearPostponed : TCM Unit := do
  modifyState fun s => { s with postponed := #[], worklist := #[] }

/-- Wake up constraints that depend on a solved metavariable -/
def wakeConstraintsFor (mid : MetaId) : TCM Unit := do
  let state ← getState
  let affectedCids := state.metas.getAffectedConstraints mid
  modifyState (·.wakeConstraints affectedCids)

/-- Pop a constraint from the worklist -/
def popWorklist : TCM (Option ConstraintId) := do
  let state ← getState
  let (cid?, state') := state.popWorklist
  set state'
  return cid?

/-- Get a constraint by ID -/
def getConstraintById (cid : ConstraintId) : TCM (Option TrackedConstraint) := do
  let state ← getState
  return state.getConstraint cid

/-- Remove a solved constraint -/
def removeConstraint (cid : ConstraintId) : TCM Unit := do
  modifyState (·.removeConstraint cid)

/-- Get constraint complexity (number of unsolved metas) -/
def constraintComplexity (cid : ConstraintId) : TCM Nat := do
  let state ← getState
  return state.metas.constraintComplexity cid

/-- Generate a fresh name -/
def freshName (base : String := "x") : TCM String := do
  let state ← getState
  let (name, state') := state.freshName base
  set state'
  return name

/-- Generate a fresh unique identifier -/
def freshUnique (original : String) : TCM Unique := do
  let state ← getState
  let (u, state') := state.freshUnique original
  set state'
  return u

/-- Record usage of a variable. The quantity is multiplied by the current context multiplier. -/
def useVar (name : String) (qty : Quantity := .omega) : TCM Unit := do
  let ctx ← getCtx
  -- Multiply by context multiplier
  let effectiveQty := ctx.qtyMultiplier.mul qty
  modifyState (·.useVar name effectiveQty)

/-- Get the recorded usage of a variable -/
def getUsage (name : String) : TCM Quantity := do
  let state ← getState
  return state.getUsage name

/-- Check that a variable's usage is compatible with its declared quantity -/
def checkUsage (name : String) (declared : Quantity) (span : Span) : TCM Unit := do
  let actual ← getUsage name
  -- Check: actual ≤ declared (in the quantity semiring ordering)
  if !actual.le declared then
    throw (.quantityMismatch declared actual name span)

/-- Check all linear variables in scope are used exactly once -/
def checkLinearVarsUsed : TCM Unit := do
  let ctx ← getCtx
  for entry in ctx.locals do
    if entry.qty == .one then
      let usage ← getUsage entry.name
      if usage == .zero then
        throw (.linearNotUsed entry.name entry.span)
      else if usage != .one then
        -- Used more than once
        addError (.quantityMismatch .one usage entry.name entry.span)

/-- Run an action with quantity multiplier set (for checking under binders) -/
def withQtyMultiplier (qty : Quantity) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with qtyMultiplier := ctx.qtyMultiplier.mul qty }) m

/-- Run an action in erased context (quantity 0) -/
def inErasedContext (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with inErased := true, qtyMultiplier := .zero }) m

/-- Run an action with fresh usage tracking, returning the usages -/
def withFreshUsages (m : TCM α) : TCM (α × Std.HashMap String Quantity) := do
  let state ← getState
  let savedUsages := state.saveUsages
  modifyState (·.clearUsages)
  let result ← m
  let state' ← getState
  let newUsages := state'.usages
  modifyState (·.restoreUsages savedUsages)
  return (result, newUsages)

/-! ## Evaluation -/

/-- Convert TCM globals to EvalCtx globals -/
private def globalsToEvalGlobals (g : Globals) : GlobalEnv :=
  let entries := g.defs.toList
  entries.foldl (fun acc (name, info) =>
    match info.value with
    | some v => acc.insert name v
    | none => acc
  ) GlobalEnv.empty

/-- Evaluate an untyped expression to a Value using the current environment -/
def eval (e : Expr Unit scope) : TCM Value := do
  let ctx ← getCtx
  let state ← getState
  let evalCtx : EvalCtx := {
    env := ctx.env
    globals := globalsToEvalGlobals ctx.globals
    metas := state.metas
  }
  return Soma.Core.eval evalCtx e

/-- Evaluate a typed expression by first stripping type annotations -/
def evalTyped (e : Expr Value scope) : TCM Value := do
  let ctx ← getCtx
  let state ← getState
  let evalCtx : EvalCtx := {
    env := ctx.env
    globals := globalsToEvalGlobals ctx.globals
    metas := state.metas
  }
  -- Strip type annotations and evaluate
  let untyped := e.mapInfo (fun _ => ())
  return Soma.Core.eval evalCtx untyped

/-- Evaluate a Term to a Value using the current environment.
    This is useful when working with closures or pattern solutions that use Terms. -/
def evalTerm (t : Term) : TCM Value := do
  let ctx ← getCtx
  let state ← getState
  let evalCtx : EvalCtx := {
    env := ctx.env
    globals := globalsToEvalGlobals ctx.globals
    metas := state.metas
  }
  return Soma.Core.evalTerm evalCtx t

/-- Create a Pi type value -/
def mkPi (qty : Quantity) (binder : BinderInfo) (name : String) (domain : Value)
    (codomain : Closure) : Value :=
  .vPi qty binder name domain codomain

/-- Create a simple (non-dependent) function type -/
def mkArrow (domain codomain : Value) : TCM Value := do
  -- For non-dependent function types, use HOAS-style closure
  -- The codomain doesn't depend on the argument, so just store it directly
  return .vPi .omega .explicit "_" domain (Closure.const "_" codomain)

/-- Check if we're currently in erased context -/
def isInErasedContext : TCM Bool := do
  let ctx ← getCtx
  return ctx.inErased

/-- Check if debug mode is enabled -/
def isDebug : TCM Bool := do
  let ctx ← getCtx
  return ctx.debug

/-- Get the current indentation string -/
def debugIndentStr : TCM String := do
  let ctx ← getCtx
  return String.ofList (List.replicate (ctx.debugIndent * 2) ' ')

/-- Print a debug message if debug mode is enabled -/
def debug (msg : String) : TCM Unit := do
  let ctx ← getCtx
  if ctx.debug then
    let indent := String.ofList (List.replicate (ctx.debugIndent * 2) ' ')
    dbg_trace s!"{indent}{msg}"
    pure ()

/-- Run an action with increased debug indentation -/
def withDebugIndent (m : TCM α) : TCM α :=
  withReader (·.indent) m

/-- Debug trace entering a function with its expression kind -/
def debugEnter (kind : String) (info : String := "") : TCM Unit := do
  if info.isEmpty then
    debug s!"┌─ {kind}"
  else
    debug s!"┌─ {kind}: {info}"

/-- Debug trace leaving a function with result -/
def debugLeave (kind : String) (result : String) : TCM Unit := do
  debug s!"└─ {kind} => {result}"

/-- Debug trace for intermediate steps -/
def debugStep (msg : String) : TCM Unit := do
  debug s!"│  {msg}"

/-- Get the instance environment -/
def getInstanceEnv : TCM InstanceEnv := do
  let ctx ← getCtx
  return ctx.instanceEnv

/-- Run with a modified instance environment -/
def withInstanceEnv (env : InstanceEnv) (m : TCM α) : TCM α :=
  withReader (fun ctx => { ctx with instanceEnv := env }) m

/-- Add a pending instance constraint -/
def addPendingInstance (classId : Unique) (args : Array Value) (metaId : MetaId)
    (span : Span) : TCM Unit := do
  let pending : PendingInstance := {
    metaId := metaId
    classId := classId
    args := args
    span := span
  }
  modifyState (·.addPendingInstance pending)

/-- Get all pending instance constraints -/
def getPendingInstances : TCM (Array PendingInstance) := do
  let state ← getState
  return state.getPendingInstances

/-- Clear pending instance constraints -/
def clearPendingInstances : TCM Unit := do
  modifyState (·.clearPendingInstances)

/-- Look up a class by unique -/
def lookupClass (classId : Unique) : TCM (Option ClassInfo) := do
  let env ← getInstanceEnv
  return env.getClass classId

/-- Get all instances for a class -/
def getClassInstances (classId : Unique) : TCM (Array InstanceInfo) := do
  let env ← getInstanceEnv
  return env.getInstances classId

/-- Check if a class exists -/
def hasClass (classId : Unique) : TCM Bool := do
  let env ← getInstanceEnv
  return env.hasClass classId

/-- Create a fresh metavariable for an instance argument -/
def freshInstanceMeta (classId : Unique) (args : Array Value) (span : Span) : TCM Value := do
  -- Create a placeholder type for the instance
  -- todo: make this the actual class record type
  let instTy := Value.vType .zero
  let metaId ← freshMeta instTy
  -- Register this as a pending instance to resolve
  addPendingInstance classId args metaId span
  return .vNeutral instTy (.nMeta metaId)

/-- Create a constant closure (for non-dependent types) -/
def mkConstClosure (name : String) (result : Value) : TCM Closure := do
  return Closure.const name result

/-- Create an empty/placeholder closure from the current environment -/
def mkEmptyClosure (name : String) : TCM Closure := do
  let ctx ← getCtx
  return Closure.mkEmpty name ctx.env

/-- Create a closure with a specific term body -/
def mkClosureWithTerm (name : String) (body : Term) : TCM Closure := do
  let ctx ← getCtx
  return Closure.mkWithBody name ctx.env body

/-- Run an action, rolling back state if it throws an error -/
def withRollbackOnFailure (action : TCM α) : TCM α := do
  let stateBefore ← getState
  try
    action
  catch e =>
    set stateBefore
    throw e

/-- Try an action, rolling back state if it fails -/
def tryWithRollback (action : TCM α) : TCM (Option α) := do
  let stateBefore ← getState
  try
    let result ← action
    return some result
  catch _ =>
    set stateBefore
    return none

/-- Run an action speculatively: if it succeeds, keep the state changes,
    If it fails, rollback state and return the given default value -/
def speculatively (action : TCM α) (default : α) : TCM α := do
  let stateBefore ← getState
  try
    action
  catch _ =>
    set stateBefore
    return default

/-- Try multiple alternatives in order, with state rollback between attempts -/
def tryAlternatives (actions : List (TCM α)) : TCM α := do
  let stateBefore ← getState
  let mut lastError : Option TCError := none
  for action in actions do
    try
      let result ← action
      return result
    catch e =>
      set stateBefore
      lastError := some e
  match lastError with
  | some e => throw e
  | none => throw (.internalError "tryAlternatives: empty action list" Span.uninhabited)

end TCM

end Soma.Dependent
