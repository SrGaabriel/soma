import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quantity
import Soma.Core.Primitive
import Soma.Dependent.Monad
import Soma.Dependent.Convert
import Soma.Dependent.Unify
import Soma.Syntax.Source
import Soma.Unique

namespace Soma.Dependent

open Soma (Unique)
open Soma.Core
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

def tabledIterationCap : Nat := 100000

private abbrev NormMap := Std.HashMap Nat Nat

mutual

partial def normKey (v : Value) (depth : Nat) (m : NormMap)
    : TCM (String × NormMap) := do
  let v' ← force v
  match v' with
  | .vType lvl         => return (s!"T{toString lvl}", m)
  | .vRowSort          => return ("RS", m)
  | .vLabelSort        => return ("LS", m)
  | .vRowEmpty         => return ("RE", m)
  | .vLabelLit s       => return (s!"L{s}", m)
  | .vIntLit n         => return (s!"i{n}", m)
  | .vFloatLit f       => return (s!"f{f}", m)
  | .vStringLit s      => return (s!"s{s}", m)
  | .vDataType id ps   =>
    let (parts, m') ← normKeyList ps depth m
    return (s!"D{id.id}[{parts}]", m')
  | .vConstructor _ tag as _ =>
    let (parts, m') ← normKeyList as depth m
    return (s!"C{tag}[{parts}]", m')
  | .vRecord row =>
    let (r, m') ← normKey row depth m
    return (s!"R({r})", m')
  | .vVariant row =>
    let (r, m') ← normKey row depth m
    return (s!"V({r})", m')
  | .vRowExtend l f t =>
    let (ls, m₁) ← normKey l depth m
    let (fs, m₂) ← normKey f depth m₁
    let (ts, m₃) ← normKey t depth m₂
    return (s!"RX({ls}:{fs}|{ts})", m₃)
  | .vRecordVal fields =>
    let mut m' := m
    let mut parts : List String := []
    for (name, val) in fields do
      let (sv, m'') ← normKey val depth m'
      m' := m''
      parts := parts ++ [s!"{name}={sv}"]
    let body := ",".intercalate parts
    return ("RV{" ++ body ++ "}", m')
  | .vPi qty binder _ dom cod =>
    let (ds, m₁) ← normKey dom depth m
    let dummy := Value.vNeutral dom (.nVar ⟨"_κ", ⟨depth⟩⟩)
    let codV ← applyClosure cod dummy
    let (cs, m₂) ← normKey codV (depth + 1) m₁
    return (s!"Π{toString qty}{toString binder}({ds}→{cs})", m₂)
  | .vLam _ body =>
    let dummy := Value.vNeutral (.vType .zero) (.nVar ⟨"_λ", ⟨depth⟩⟩)
    let bV ← applyClosure body dummy
    let (bs, m') ← normKey bV (depth + 1) m
    return (s!"λ.{bs}", m')
  | .vNeutral _ neu =>
    normNeuKey neu depth m

partial def normNeuKey (neu : Neutral) (depth : Nat) (m : NormMap)
    : TCM (String × NormMap) := do
  let (hs, m₁) ← normHeadKey neu.head depth m
  let mut m' := m₁
  let mut parts : List String := []
  for e in neu.spine do
    let (es, m'') ← normElimKey e depth m'
    m' := m''
    parts := parts ++ [es]
  return (s!"{hs}·[{",".intercalate parts}]", m')

partial def normHeadKey (h : Head) (depth : Nat) (m : NormMap)
    : TCM (String × NormMap) := do
  match h with
  | .hMeta mid =>
    match m.get? mid.id with
    | some idx => return (s!"θ{idx}", m)
    | none     => let idx := m.size; return (s!"θ{idx}", m.insert mid.id idx)
  | .hVar bv    => return (s!"B{bv.level.lvl}", m)
  | .hConst n _ => return (s!"K{n.id}", m)
  | .hErrored   => return ("⊥", m)
  | .hCase scruts motive _ =>
    let mut m' := m
    let mut parts : List String := []
    for s in scruts do
      let (x, m'') ← normKey s depth m'
      m' := m''
      parts := parts ++ [x]
    let (ms, m'') ← normKey motive depth m'
    return (s!"case[{",".intercalate parts}/{ms}]", m'')

partial def normElimKey (e : Elim) (depth : Nat) (m : NormMap)
    : TCM (String × NormMap) := do
  match e with
  | .eApp a    => let (s, m') ← normKey a depth m; return (s!"@{s}", m')
  | .eField n  => return (s!".{n}", m)

partial def normKeyList (vs : List Value) (depth : Nat) (m : NormMap)
    : TCM (String × NormMap) := do
  let mut m' := m
  let mut parts : List String := []
  for v in vs do
    let (s, m'') ← normKey v depth m'
    m' := m''
    parts := parts ++ [s]
  return (",".intercalate parts, m')

end

/-- Produce the canonical α-normalized key for a `(classId, args)` subgoal -/
def normalizeGoalKey (classId : Unique) (args : Array Value) : TCM String := do
  let mut m : NormMap := {}
  let mut parts : List String := []
  for a in args do
    let (s, m') ← normKey a 0 m
    m := m'
    parts := parts ++ [s]
  return s!"#{classId.id}|{",".intercalate parts}"

/-- One solution attached to a table entry -/
structure Solution where
  value : Value
  usedInstances : Array Unique
  deriving Inhabited

/-- Entry in the resolver table, one per α-distinct subgoal -/
structure TableEntry where
  /-- The class being resolved -/
  classId : Unique
  /-- The args at first registration -/
  args : Array Value
  /-- Solutions discovered so far -/
  solutions : Array Solution := #[]
  /-- Consumer ids currently suspended on a solution from this entry -/
  dependents : Array Nat := #[]
  /-- Whether the generator for this entry has popped -/
  generatorDone : Bool := false
  deriving Inhabited

/-- A generator node -/
structure GenNode where
  key : String
  classId : Unique
  args : Array Value
  instances : Array InstanceInfo
  nextIdx : Nat := 0
  baseEnv : Soma.Dependent.TCState
  deriving Inhabited

/-- A remaining subgoal within a consumer's workqueue -/
structure PendingGoal where
  classId : Unique
  args : Array Value
  isDictConstraint : Bool
  deriving Inhabited

/-- A consumer node -/
structure ConsNode where
  /-- Ancestor goal key -/
  ancestorKey : String
  /-- Trail of instance ids that contributed to this consumer -/
  usedInstances : Array Unique
  /-- Base instance value -/
  instValue : Value
  /-- Whether the base instance value needs `applyConstraintDicts` -/
  usesDicts : Bool
  /-- Dict values from already satisfied constraints -/
  accumDicts : Array Value := #[]
  /-- Subgoals that we still need to discharge -/
  remaining : Array PendingGoal
  /-- Elaborator state at suspension -/
  savedEnv : Soma.Dependent.TCState
  deriving Inhabited

/-- The resolver's internal state -/
structure TabledState where
  table : Std.HashMap String TableEntry := {}
  consumers : Array ConsNode := #[]
  genStack : Array GenNode := #[]
  resumeStack : Array (Nat × Nat) := #[]
  originalKey : String := ""
  fuel : Nat := tabledIterationCap

abbrev TabledM := StateT TabledState TCM

namespace TabledM

def lookupEntry (key : String) : TabledM (Option TableEntry) :=
  return (← get).table.get? key

def setEntry (key : String) (entry : TableEntry) : TabledM Unit :=
  modify fun s => { s with table := s.table.insert key entry }

def addSolution (key : String) (sol : Solution) : TabledM (Option Nat) := do
  match ← lookupEntry key with
  | none => return none
  | some entry =>
    let idx := entry.solutions.size
    setEntry key { entry with solutions := entry.solutions.push sol }
    for dep in entry.dependents do
      modify fun s => { s with resumeStack := s.resumeStack.push (dep, idx) }
    return some idx

def addDependent (key : String) (cid : Nat) : TabledM Unit := do
  match ← lookupEntry key with
  | none => pure ()
  | some entry =>
    setEntry key { entry with dependents := entry.dependents.push cid }

def pushGen (g : GenNode) : TabledM Unit :=
  modify fun s => { s with genStack := s.genStack.push g }

/-- Mark a subgoal's generator as exhausted -/
def markGeneratorDone (key : String) : TabledM Unit := do
  match ← lookupEntry key with
  | none => pure ()
  | some entry =>
    setEntry key { entry with generatorDone := true }

/-- Check if a table entry is exhausted and prune it if so -/
def pruneIfExhausted (key : String) : TabledM Bool := do
  let s ← get
  match s.table.get? key with
  | none => return false
  | some entry =>
    let exhausted :=
      entry.generatorDone &&
      entry.solutions.isEmpty &&
      entry.dependents.isEmpty &&
      key != s.originalKey
    if exhausted then
      set { s with table := s.table.erase key }
      return true
    else
      return false

def popGen : TabledM Unit := do
  let s ← get
  if let some g := s.genStack.back? then
    set { s with genStack := s.genStack.pop }
    markGeneratorDone g.key
    let _ ← pruneIfExhausted g.key
  else
    pure ()

def peekGen : TabledM (Option GenNode) := do
  let s ← get
  return s.genStack.back?

/-- Replace the top generator node; used to advance `nextIdx` after a try -/
def updateTopGen (f : GenNode → GenNode) : TabledM Unit :=
  modify fun s =>
    if s.genStack.size > 0 then
      let i := s.genStack.size - 1
      let g := s.genStack[i]!
      { s with genStack := s.genStack.set! i (f g) }
    else s

def newConsumer (c : ConsNode) : TabledM Nat :=
  modifyGet fun s =>
    let id := s.consumers.size
    (id, { s with consumers := s.consumers.push c })

def getConsumer (cid : Nat) : TabledM ConsNode := do
  let s ← get
  return s.consumers[cid]!

def popResume : TabledM (Option (Nat × Nat)) :=
  modifyGet fun s =>
    match s.resumeStack.back? with
    | none => (none, s)
    | some r => (some r, { s with resumeStack := s.resumeStack.pop })

def consumeFuel : TabledM Bool :=
  modifyGet fun s =>
    if s.fuel == 0 then (false, s)
    else (true, { s with fuel := s.fuel - 1 })

def originalHasSolution : TabledM (Option Solution) := do
  let s ← get
  match s.table.get? s.originalKey with
  | some entry => return entry.solutions[0]?
  | none => return none

end TabledM

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

def toString : ResolutionResult → String
  | .found _ ids => s!"found (used {ids.size} instances)"
  | .notFound cid _ reason => s!"not found for '{cid.original}': {reason}"
  | .cycle cid _ => s!"cycle detected: {cid.original}"
  | .depthExceeded cid => s!"search depth exceeded: {cid.original}"

def isFound : ResolutionResult → Bool
  | .found _ _ => true
  | _ => false

def getClassId? : ResolutionResult → Option Unique
  | .notFound cid _ _ => some cid
  | .cycle cid _ => some cid
  | .depthExceeded cid => some cid
  | .found _ _ => none

instance : ToString ResolutionResult := ⟨ResolutionResult.toString⟩

end ResolutionResult

/-- Result of trying to match an instance -/
inductive MatchResult where
  /-- Instance matches with the given substitutions -/
  | matched (instValue : Value) (substitutions : Array (MetaId × Value))
      (refreshedConstraints : Array (Unique × Array Value))
      (metaMapping : Std.HashMap Nat MetaId)
  /-- Instance doesn't match -/
  | noMatch
  /-- Matching failed with an error -/
  | error (msg : String)
  deriving Inhabited

/-- Refresh stale metavariables in a Value -/
private partial def refreshStaleMetas (v : Value) (mapping : Std.HashMap Nat MetaId)
    : TCM (Value × Std.HashMap Nat MetaId) := do
  match v with
  | .vNeutral _ty (.nMeta m) =>
    match mapping.get? m.id with
    | some freshId =>
      return (Value.vNeutral (.vType .zero) (.nMeta freshId), mapping)
    | none =>
      let freshMeta ← TCM.freshMetaVal (.vType .zero)
      let freshId ← match freshMeta with
        | .vNeutral _ (.nMeta fid) => pure fid
        | _ => pure m
      return (freshMeta, mapping.insert m.id freshId)
  | .vNeutral ty neu =>
    let (ty', mapping') ← refreshStaleMetas ty mapping
    let (neu', mapping'') ← refreshStaleMetasNeutral neu mapping'
    return (.vNeutral ty' neu', mapping'')
  | .vDataType id params =>
    let mut mapping' := mapping
    let mut params' : List Value := []
    for p in params do
      let (p', m) ← refreshStaleMetas p mapping'
      mapping' := m
      params' := params' ++ [p']
    return (.vDataType id params', mapping')
  | .vPi qty binder name dom cod =>
    let (dom', mapping') ← refreshStaleMetas dom mapping
    return (.vPi qty binder name dom' cod, mapping')
  | .vRowExtend label fieldTy tail =>
    let (label', mapping') ← refreshStaleMetas label mapping
    let (fieldTy', mapping'') ← refreshStaleMetas fieldTy mapping'
    let (tail', mapping''') ← refreshStaleMetas tail mapping''
    return (.vRowExtend label' fieldTy' tail', mapping''')
  | .vRecord row =>
    let (row', mapping') ← refreshStaleMetas row mapping
    return (.vRecord row', mapping')
  | .vVariant row =>
    let (row', mapping') ← refreshStaleMetas row mapping
    return (.vVariant row', mapping')
  | .vLam name body => return (.vLam name body, mapping)
  | .vRecordVal fields =>
    let mut mapping' := mapping
    let mut fields' : List (String × Value) := []
    for (name, val) in fields do
      let (val', m) ← refreshStaleMetas val mapping'
      mapping' := m
      fields' := fields' ++ [(name, val')]
    return (.vRecordVal fields', mapping')
  | .vConstructor name tag args resultTy =>
    let mut mapping' := mapping
    let mut args' : List Value := []
    for arg in args do
      let (arg', m) ← refreshStaleMetas arg mapping'
      mapping' := m
      args' := args' ++ [arg']
    let (resultTy', mapping'') ← refreshStaleMetas resultTy mapping'
    return (.vConstructor name tag args' resultTy', mapping'')
  | other => return (other, mapping)
where
  refreshStaleMetasNeutral (n : Neutral) (mapping : Std.HashMap Nat MetaId)
      : TCM (Neutral × Std.HashMap Nat MetaId) := do
    let (head', mapping') ← refreshStaleMetasHead n.head mapping
    let mut currentMapping := mapping'
    let mut refreshedSpine : Array Elim := #[]
    for e in n.spine do
      let (e', m'') ← refreshStaleMetasElim e currentMapping
      currentMapping := m''
      refreshedSpine := refreshedSpine.push e'
    return (.mk head' refreshedSpine, currentMapping)

  refreshStaleMetasHead (h : Head) (mapping : Std.HashMap Nat MetaId)
      : TCM (Head × Std.HashMap Nat MetaId) := do
    match h with
    | .hMeta m =>
      match mapping.get? m.id with
      | some freshId => return (.hMeta freshId, mapping)
      | none =>
        let freshMeta ← TCM.freshMetaVal (.vType .zero)
        let freshId ← match freshMeta with
          | .vNeutral _ neu =>
            match neu.head with
            | .hMeta fid => pure fid
            | _ => pure m
          | _ => pure m
        return (.hMeta freshId, mapping.insert m.id freshId)
    | .hVar _ => return (h, mapping)
    | .hConst _ _ => return (h, mapping)
    | .hErrored => return (h, mapping)
    | .hCase scrutinees motive arms =>
      let mut currentMapping := mapping
      let mut refreshed : Array Value := #[]
      for s in scrutinees do
        let (s', m') ← refreshStaleMetas s currentMapping
        currentMapping := m'
        refreshed := refreshed.push s'
      let (motive', finalMapping) ← refreshStaleMetas motive currentMapping
      return (.hCase refreshed motive' arms, finalMapping)

  refreshStaleMetasElim (e : Elim) (mapping : Std.HashMap Nat MetaId)
      : TCM (Elim × Std.HashMap Nat MetaId) := do
    match e with
    | .eApp arg =>
      let (arg', mapping') ← refreshStaleMetas arg mapping
      return (.eApp arg', mapping')
    | .eField _ => return (e, mapping)

/-- Try to match instance arguments against goal arguments using unification.
    Creates fresh metavariables for polymorphic type parameters in the instance.
    Returns the instantiated instance value if matching succeeds. -/
def tryMatchInstanceUnify (inst : InstanceInfo) (goalArgs : Array Value)
    : TCM MatchResult := do
  if inst.args.size != goalArgs.size then
    return .noMatch

  -- Save state for potential rollback
  let stateBefore ← TCM.getState

  let mut metaMapping : Std.HashMap Nat MetaId := {}
  let mut refreshedArgs : Array Value := #[]
  for arg in inst.args do
    let (arg', mapping') ← refreshStaleMetas arg metaMapping
    metaMapping := mapping'
    refreshedArgs := refreshedArgs.push arg'
  let mut refreshedConstraints : Array (Unique × Array Value) := #[]
  for (cid, cargs) in inst.constraints do
    let mut cargs' : Array Value := #[]
    for carg in cargs do
      let (carg', mapping') ← refreshStaleMetas carg metaMapping
      metaMapping := mapping'
      cargs' := cargs'.push carg'
    refreshedConstraints := refreshedConstraints.push (cid, cargs')

  -- Create fresh metavariables for any polymorphic parameters in the instance
  let mut substitutions : Array (MetaId × Value) := #[]

  for i in [:refreshedArgs.size] do
    if let (some instArg, some goalArg) := (refreshedArgs[i]?, goalArgs[i]?) then
      let instArg' ← force instArg
      let goalArg' ← force goalArg

      try
        unify instArg' goalArg'
      catch _ =>
        TCM.modifyState fun _ => stateBefore
        return .error "unification failed during instance matching"

  -- Check that all created metas during unification are solved and collect the substitutions
  let stateAfter ← TCM.getState
  for id in [stateBefore.metas.nextId:stateAfter.metas.nextId] do
    let metaId : MetaId := ⟨id⟩
    if let some info := stateAfter.metas.lookup metaId then
      if let some sol := info.solution then
        substitutions := substitutions.push (metaId, sol)

  return .matched inst.value substitutions refreshedConstraints metaMapping

/-- Result of matching an instance: value + refreshed constraints -/
structure InstanceMatch where
  value : Value
  refreshedConstraints : Array (Unique × Array Value)
  metaMapping : Std.HashMap Nat MetaId

/-- Check if an instance matches a goal using unification -/
def matchInstance (inst : InstanceInfo) (classId : Unique) (args : Array Value)
    : TCM (Option InstanceMatch) := do
  -- Check class id matches
  if inst.classId != classId then
    return none

  -- Try to match arguments using unification
  let result ← tryMatchInstanceUnify inst args
  match result with
  | .matched value _ constraints metaMapping =>
    return some ⟨value, constraints, metaMapping⟩
  | .noMatch =>
    return none
  | .error _ =>
    return none

/-- Apply resolved constraint dicts to a dictionary-passing instance value -/
private def applyConstraintDicts (instValue : Value) (constraintDicts : Array Value)
    : TCM Value := do
  let mut result := instValue
  for dict in constraintDicts do
    result ← match result with
      | .vLam _ body => applyClosure body dict
      | .vNeutral ty neu => pure (.vNeutral ty (.nApp neu dict))
      | other => pure other
  return result

/-- Extract the pending subgoals that an instance match leaves behind -/
private def buildRemainingGoals
    (instMatch : InstanceMatch) (classInfo? : Option ClassInfo)
    (goalArgs : Array Value) : TCM (Array PendingGoal) := do
  let mut out : Array PendingGoal := #[]
  for (cid, cargs) in instMatch.refreshedConstraints do
    let forced ← cargs.mapM force
    out := out.push ⟨cid, forced, true⟩
  match classInfo? with
  | none => pure ()
  | some info =>
    for (scid, paramIdxs) in info.superclasses do
      let mut sArgs : Array Value := #[]
      let mut ok := true
      for idx in paramIdxs do
        if let some a := goalArgs[idx]? then sArgs := sArgs.push a
        else ok := false
      if ok then out := out.push ⟨scid, sArgs, false⟩
  return out

/-- Ensure the goal `(classId, args)` has an entry in the table -/
private partial def ensureSubgoal (key : String) (classId : Unique) (args : Array Value)
    : TabledM Unit := do
  match ← TabledM.lookupEntry key with
  | some _ => pure ()
  | none =>
    let argsF ← match args[0]? with
      | some a => do let af ← force a; pure (args.set! 0 af)
      | none   => pure args
    let instances ← TCM.getCandidateInstances classId argsF
    let baseEnv ← TCM.getState
    TabledM.setEntry key { classId, args := argsF, solutions := #[], dependents := #[] }
    TabledM.pushGen { key, classId, args := argsF, instances, nextIdx := 0, baseEnv }

/-- Install a newly-created consumer -/
private partial def installConsumer (c : ConsNode) : TabledM Unit := do
  if c.remaining.isEmpty then
    -- No more subgoals so we complete and publish the solution
    let value ←
      if c.usesDicts && !c.accumDicts.isEmpty then
        applyConstraintDicts c.instValue c.accumDicts
      else
        pure c.instValue
    let _ ← TabledM.addSolution c.ancestorKey { value, usedInstances := c.usedInstances }
    return
  let cid ← TabledM.newConsumer c
  let first := c.remaining[0]!
  let firstKey ← normalizeGoalKey first.classId first.args
  match ← TabledM.lookupEntry firstKey with
  | some entry =>
    -- Already tabled
    TabledM.addDependent firstKey cid
    for i in [:entry.solutions.size] do
      modify fun s => { s with resumeStack := s.resumeStack.push (cid, i) }
  | none =>
    ensureSubgoal firstKey first.classId first.args
    TabledM.addDependent firstKey cid

/-- Resume a suspended consumer with one of the solutions its first-remaining subgoal has accumulated -/
private partial def resumeConsumer (cid : Nat) (solIdx : Nat) : TabledM Unit := do
  let c ← TabledM.getConsumer cid
  if c.remaining.isEmpty then return
  let first := c.remaining[0]!
  let firstKey ← normalizeGoalKey first.classId first.args
  match ← TabledM.lookupEntry firstKey with
  | none => return
  | some entry =>
    if h : solIdx < entry.solutions.size then
      let sol := entry.solutions[solIdx]
      TCM.modifyState fun _ => c.savedEnv
      let mut unifyOk := true
      for i in [:first.args.size] do
        if let (some a, some b) := (first.args[i]?, entry.args[i]?) then
          let af ← force a
          let bf ← force b
          try unify af bf catch _ => unifyOk := false
        if !unifyOk then break
      if !unifyOk then return
      let dicts' :=
        if first.isDictConstraint then c.accumDicts.push sol.value
        else c.accumDicts
      let newEnv ← TCM.getState
      let advanced : ConsNode := {
        ancestorKey := c.ancestorKey
        usedInstances := c.usedInstances ++ sol.usedInstances
        instValue := c.instValue
        usesDicts := c.usesDicts
        accumDicts := dicts'
        remaining := c.remaining.extract 1 c.remaining.size
        savedEnv := newEnv
      }
      installConsumer advanced
    else return

/-- Advance the top generator by one instance attempt -/
private partial def extendGenerator : TabledM Unit := do
  match ← TabledM.peekGen with
  | none => pure ()
  | some g =>
    if g.nextIdx >= g.instances.size then
      TabledM.popGen
      return
    let inst := g.instances[g.nextIdx]!
    TabledM.updateTopGen fun g => { g with nextIdx := g.nextIdx + 1 }
    TCM.modifyState fun _ => g.baseEnv
    match ← matchInstance inst g.classId g.args with
    | none => return
    | some instMatch =>
      let classInfo? ← TCM.lookupClass g.classId
      let remaining ← buildRemainingGoals instMatch classInfo? g.args
      let envAfterMatch ← TCM.getState
      let cons : ConsNode := {
        ancestorKey := g.key
        usedInstances := #[inst.instanceId]
        instValue := instMatch.value
        usesDicts := inst.constraintDictCount > 0
        accumDicts := #[]
        remaining
        savedEnv := envAfterMatch
      }
      installConsumer cons

/-- The main loop -/
private partial def mainLoop (classId : Unique) (args : Array Value)
    : TabledM ResolutionResult := do
  let rec step : Unit → TabledM ResolutionResult := fun _ => do
    if !(← TabledM.consumeFuel) then
      return .depthExceeded classId
    if let some sol ← TabledM.originalHasSolution then
      return .found sol.value sol.usedInstances
    match ← TabledM.popResume with
    | some (cid, solIdx) =>
      resumeConsumer cid solIdx
      step ()
    | none =>
      match ← TabledM.peekGen with
      | some _ =>
        extendGenerator
        step ()
      | none =>
        match ← TabledM.originalHasSolution with
        | some sol => return .found sol.value sol.usedInstances
        | none =>
          return .notFound classId args
            s!"no matching instance for '{classId.original}' with given arguments"
  step ()

/-- Public resolver entry -/
partial def resolveInstance (classId : Unique) (args : Array Value)
    : TCM ResolutionResult := do
  let key ← normalizeGoalKey classId args
  let action : TabledM ResolutionResult := do
    ensureSubgoal key classId args
    mainLoop classId args
  let (r, _) ← action.run { originalKey := key }
  return r

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

/-- Deeply force metavariables inside values -/
partial def deepForceValue (v : Value) : TCM Value := do
  let v' ← force v
  match v' with
  | .vDataType id params =>
    let params' ← params.mapM deepForceValue
    return .vDataType id params'
  | .vPi qty binder name dom cod =>
    let dom' ← deepForceValue dom
    return .vPi qty binder name dom' cod
  | .vRowExtend label fieldTy tail =>
    let label' ← deepForceValue label
    let fieldTy' ← deepForceValue fieldTy
    let tail' ← deepForceValue tail
    return .vRowExtend label' fieldTy' tail'
  | .vRecord row =>
    let row' ← deepForceValue row
    return .vRecord row'
  | .vVariant row =>
    let row' ← deepForceValue row
    return .vVariant row'
  | other => return other

/-- Deep-force every argument of an `InstanceInfo` -/
def forceInstanceInfoArgs (inst : InstanceInfo) : TCM InstanceInfo := do
  let forcedArgs ← inst.args.mapM deepForceValue
  return { inst with args := forcedArgs }

namespace InstanceEnv

/-- Force args before storing, then delegate to the pure update -/
def addInstanceWithIdForced (env : InstanceEnv) (inst : InstanceInfo)
    : TCM InstanceEnv := do
  let inst' ← forceInstanceInfoArgs inst
  return env.addInstanceWithId inst'

end InstanceEnv

/-- Create an empty closure for non-dependent types -/
private def mkSimpleClosure (name : String) : Closure :=
  Closure.mkEmpty name Env.empty

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

  return env

/-- Create a TCContext with the default instance environment -/
def TCContext.withDefaultInstances (ctx : TCContext := TCContext.empty) : TCContext :=
  { ctx with instanceEnv := defaultInstanceEnv }

end Soma.Dependent
