import Soma.Core.Value
import Soma.Core.Module
import Soma.Dependent.Monad
import Soma.Dependent.Error
import Soma.Dependent.TraitElaborate
import Std.Data.HashMap
import Std.Data.HashSet

namespace Soma.Dependent.Incremental

open Soma.Core (Value)
open Soma.Dependent.TraitElaborate (InstanceMap)
open Std (HashMap HashSet)

/-- Uniquely identifies a definition within a project -/
structure DefId where
  /-- Module containing the definition -/
  module : String
  /-- Name of the definition -/
  name : String
  deriving Repr, BEq, Hashable, Inhabited

instance : ToString DefId where
  toString d := s!"{d.module}.{d.name}"

namespace DefId

/-- Create a DefId for a local definition (same module) -/
def local_ (name : String) (currentModule : String) : DefId := ⟨currentModule, name⟩

end DefId

/-- The kind of a definition, for more precise dependency tracking -/
inductive DefKind where
  /-- A function definition -/
  | function
  /-- A data type definition -/
  | dataType
  /-- A constructor -/
  | constructor (parentType : String)
  /-- A type class -/
  | typeClass
  /-- A type class instance -/
  | instance_ (className : String)
  /-- A type class method -/
  | method (className : String)
  deriving Repr, BEq, Inhabited

/-- Cached information for a single definition -/
structure DefCache where
  /-- Hash of the source syntax for this definition -/
  syntaxHash : UInt64
  /-- The inferred/checked type (may contain unsolved metas if checking failed) -/
  type : Value
  /-- What kind of definition this is -/
  kind : DefKind
  /-- Whether type checking succeeded completely -/
  isComplete : Bool
  /-- Errors encountered during checking (empty if isComplete) -/
  errors : Array TCError := #[]
  /-- Cached GlobalInfo to avoid reconstruction (None if checking failed) -/
  globalInfo : Option GlobalInfo := none
  deriving Inhabited

namespace DefCache

/-- Create a successful cache entry -/
def success (hash : UInt64) (ty : Value) (kind : DefKind) (info : GlobalInfo) : DefCache :=
  { syntaxHash := hash, type := ty, kind := kind, isComplete := true, globalInfo := some info }

/-- Create a failed cache entry with errors -/
def failure (hash : UInt64) (ty : Value) (kind : DefKind) (errs : Array TCError) : DefCache :=
  { syntaxHash := hash, type := ty, kind := kind, isComplete := false, errors := errs, globalInfo := none }

end DefCache

/-- Dependency graph tracking relationships between definitions -/
structure DepGraph where
  /-- Forward dependencies: def -> definitions it uses -/
  deps : HashMap DefId (HashSet DefId) := {}
  /-- Reverse dependencies: def -> definitions that use it -/
  rdeps : HashMap DefId (HashSet DefId) := {}
  deriving Inhabited

namespace DepGraph

def empty : DepGraph := {}

/-- Add a dependency: `from` depends on `to` -/
def addDep (g : DepGraph) (from_ to : DefId) : DepGraph :=
  let emptySet : HashSet DefId := {}
  let deps' := match g.deps.get? from_ with
    | some set => g.deps.insert from_ (set.insert to)
    | none => g.deps.insert from_ (emptySet.insert to)
  let rdeps' := match g.rdeps.get? to with
    | some set => g.rdeps.insert to (set.insert from_)
    | none => g.rdeps.insert to (emptySet.insert from_)
  { deps := deps', rdeps := rdeps' }

/-- Get all definitions that `def` depends on -/
def getDeps (g : DepGraph) (def_ : DefId) : HashSet DefId :=
  g.deps.getD def_ {}

/-- Get all definitions that depend on `def` -/
def getRdeps (g : DepGraph) (def_ : DefId) : HashSet DefId :=
  g.rdeps.getD def_ {}

/-- Remove a definition and all its edges -/
def remove (g : DepGraph) (def_ : DefId) : DepGraph :=
  -- Remove from deps
  let deps' := g.deps.erase def_
  -- Remove from all rdeps sets
  let deps'' := deps'.fold (init := deps') fun acc k v =>
    acc.insert k (v.erase def_)
  -- Remove from rdeps
  let rdeps' := g.rdeps.erase def_
  -- Remove from all deps sets
  let rdeps'' := rdeps'.fold (init := rdeps') fun acc k v =>
    acc.insert k (v.erase def_)
  { deps := deps'', rdeps := rdeps'' }

/-- Get all reverse dependencies transitively (definitions affected by a change) -/
partial def getTransitiveRdeps (g : DepGraph) (def_ : DefId) : HashSet DefId :=
  let emptySet : HashSet DefId := {}
  go emptySet #[def_]
where
  go (visited : HashSet DefId) (worklist : Array DefId) : HashSet DefId :=
    if worklist.isEmpty then visited
    else
      let current := worklist[0]!
      let rest := worklist.extract 1 worklist.size
      if visited.contains current then
        go visited rest
      else
        let visited' := visited.insert current
        let rdeps := g.getRdeps current
        let newWork := rdeps.fold (init := rest) fun acc d =>
          if visited'.contains d then acc else acc.push d
        go visited' newWork

end DepGraph

/-- Full incremental type checking state -/
structure IncrementalState where
  /-- Cached type information for each definition -/
  cache : HashMap DefId DefCache := {}
  /-- Dependency graph (within-module) -/
  depGraph : DepGraph := DepGraph.empty
  /-- Set of definitions that need re-checking -/
  dirty : HashSet DefId := {}
  /-- Cached globals (merged from all successful definitions) -/
  cachedGlobals : Globals := Globals.empty
  /-- Cached instance environment -/
  cachedInstanceEnv : InstanceEnv := InstanceEnv.empty
  /-- Cached instance map (span -> instance info correlation) -/
  cachedInstanceMap : InstanceMap := {}
  /-- External module dependencies: definition → set of (module name, symbol name) pairs -/
  externalDeps : HashMap DefId (HashSet (String × String)) := {}
  /-- Modules this module imports (for tracking what to invalidate) -/
  importedModules : HashSet String := {}
  deriving Inhabited

namespace IncrementalState

def empty : IncrementalState := {}

/-- Create initial state for a module -/
def forModule (_moduleName : String) : IncrementalState := {}

/-- Check if a definition is cached -/
def isCached (s : IncrementalState) (def_ : DefId) : Bool :=
  s.cache.contains def_

/-- Get cached info for a definition -/
def getCache (s : IncrementalState) (def_ : DefId) : Option DefCache :=
  s.cache.get? def_

/-- Check if a definition needs re-checking -/
def isDirty (s : IncrementalState) (def_ : DefId) : Bool :=
  s.dirty.contains def_

/-- Mark a definition as dirty -/
def markDirty (s : IncrementalState) (def_ : DefId) : IncrementalState :=
  { s with dirty := s.dirty.insert def_ }

/-- Mark a definition and all its transitive dependents as dirty -/
def markDirtyTransitive (s : IncrementalState) (def_ : DefId) : IncrementalState :=
  let affected := s.depGraph.getTransitiveRdeps def_
  let dirty' := affected.fold (init := s.dirty) fun acc d => acc.insert d
  { s with dirty := dirty' }

/-- Update the cache for a definition -/
def updateCache (s : IncrementalState) (def_ : DefId) (cache : DefCache) : IncrementalState :=
  { s with
    cache := s.cache.insert def_ cache
    dirty := s.dirty.erase def_ }

/-- Add a dependency relationship -/
def addDependency (s : IncrementalState) (from_ to : DefId) : IncrementalState :=
  { s with depGraph := s.depGraph.addDep from_ to }

/-- Clear dependencies for a definition (before re-computing them) -/
def clearDeps (s : IncrementalState) (def_ : DefId) : IncrementalState :=
  { s with
    depGraph := s.depGraph.remove def_
    externalDeps := s.externalDeps.erase def_ }

/-- Add an external dependency (dependency on a symbol from another module) -/
def addExternalDep (s : IncrementalState) (def_ : DefId) (extModule : String) (symbolName : String) : IncrementalState :=
  let existing := s.externalDeps.getD def_ {}
  { s with externalDeps := s.externalDeps.insert def_ (existing.insert (extModule, symbolName)) }

/-- Get all external dependencies for a definition -/
def getExternalDeps (s : IncrementalState) (def_ : DefId) : HashSet (String × String) :=
  s.externalDeps.getD def_ {}

/-- Get all definitions that depend on a specific external module -/
def getDefsUsingModule (s : IncrementalState) (extModule : String) : Array DefId :=
  s.externalDeps.fold (init := #[]) fun acc defId deps =>
    if deps.any (fun (mod, _) => mod == extModule) then acc.push defId else acc

/-- Get all definitions that depend on a specific symbol from an external module -/
def getDefsUsingSymbol (s : IncrementalState) (extModule : String) (symbolName : String) : Array DefId :=
  s.externalDeps.fold (init := #[]) fun acc defId deps =>
    if deps.contains (extModule, symbolName) then acc.push defId else acc

/-- Mark all definitions that use a specific external module as dirty -/
def markDirtyByExternalModule (s : IncrementalState) (extModule : String) : IncrementalState :=
  let affectedDefs := s.getDefsUsingModule extModule
  affectedDefs.foldl (fun acc def_ => acc.markDirtyTransitive def_) s

/-- Mark all definitions that use specific symbols from an external module as dirty -/
def markDirtyByExternalSymbols (s : IncrementalState) (extModule : String) (symbols : Array String) : IncrementalState :=
  symbols.foldl (fun acc sym =>
    let affectedDefs := acc.getDefsUsingSymbol extModule sym
    affectedDefs.foldl (fun acc' def_ => acc'.markDirtyTransitive def_) acc
  ) s

/-- Record that this module imports another module -/
def addImportedModule (s : IncrementalState) (modName : String) : IncrementalState :=
  { s with importedModules := s.importedModules.insert modName }

/-- Get all imported modules -/
def getImportedModules (s : IncrementalState) : HashSet String :=
  s.importedModules

/-- Get all dirty definitions in topological order (dependencies before dependents) -/
def getDirtyInOrder (s : IncrementalState) : Array DefId := Id.run do
  -- Simple topological sort using Kahn's algorithm
  let mut result : Array DefId := #[]
  let mut remaining := s.dirty
  let mut inDegree : HashMap DefId Nat := {}

  -- Compute in-degrees (only counting edges within dirty set)
  for def_ in remaining do
    let deps := s.depGraph.getDeps def_
    let dirtyDeps := deps.fold (init := 0) fun count d =>
      if remaining.contains d then count + 1 else count
    inDegree := inDegree.insert def_ dirtyDeps

  -- Process nodes with in-degree 0
  let mut worklist : Array DefId := #[]
  for def_ in remaining do
    if inDegree.getD def_ 0 == 0 then
      worklist := worklist.push def_

  while !worklist.isEmpty do
    let current := worklist[0]!
    worklist := worklist.extract 1 worklist.size
    result := result.push current
    remaining := remaining.erase current

    -- Decrease in-degree of dependents
    let rdeps := s.depGraph.getRdeps current
    for dep in rdeps do
      if remaining.contains dep then
        let newDegree := inDegree.getD dep 1 - 1
        inDegree := inDegree.insert dep newDegree
        if newDegree == 0 then
          worklist := worklist.push dep

  -- Add any remaining (cycles) at the end
  for def_ in remaining do
    result := result.push def_

  return result

/-- Invalidate cache based on syntax hash changes -/
def invalidateChanged (s : IncrementalState) (currentHashes : HashMap DefId UInt64)
    : IncrementalState := Id.run do
  let mut dirty := s.dirty

  -- Check each definition in current hashes
  for (def_, newHash) in currentHashes do
    match s.cache.get? def_ with
    | none =>
      -- New definition, needs checking
      dirty := dirty.insert def_
    | some cached =>
      if cached.syntaxHash != newHash then
        -- Hash changed, mark dirty and propagate
        let affected := s.depGraph.getTransitiveRdeps def_
        dirty := affected.fold (init := dirty) fun acc d => acc.insert d

  -- Also check for removed definitions
  for (def_, _) in s.cache do
    if !currentHashes.contains def_ then
      -- Definition was removed, mark dependents as dirty
      let affected := s.depGraph.getTransitiveRdeps def_
      dirty := affected.fold (init := dirty) fun acc d => acc.insert d

  return { s with
    cache := s.cache
    depGraph := s.depGraph
    dirty := dirty
    cachedGlobals := s.cachedGlobals
    cachedInstanceEnv := s.cachedInstanceEnv }

/-- Merge globals from cached definitions -/
def rebuildGlobals (s : IncrementalState) : Globals := Id.run do
  let mut globals := Globals.empty
  for (def_, cache) in s.cache do
    if cache.isComplete then
      -- Use cached GlobalInfo if available, otherwise reconstruct
      match cache.globalInfo with
      | some info =>
        globals := globals.insert def_.name info
      | none =>
        -- Fallback reconstruction (shouldn't happen if cache.isComplete is true)
        let info : GlobalInfo := {
          name := ⟨{ id := 0, module := def_.module, original := def_.name }⟩
          type := cache.type
          isConstructor := match cache.kind with
            | .constructor _ => true
            | _ => false
          origin := match cache.kind with
            | .function => .function
            | .dataType => .typeDecl
            | .constructor _ => .constructor
            | .typeClass => .typeDecl
            | .instance_ _ => .generated
            | .method _ => .traitMethod
        }
        globals := globals.insert def_.name info
  return globals

end IncrementalState

/-- Context for tracking dependencies during type checking -/
structure DepTrackingCtx where
  /-- Current definition being checked -/
  currentDef : DefId
  /-- Module name -/
  moduleName : String
  /-- Accumulated dependencies -/
  deps : HashSet DefId := {}
  deriving Inhabited

/-- Monad transformer for dependency tracking -/
abbrev DepTrackM := StateT DepTrackingCtx TCM

namespace DepTrackM

/-- Record a dependency on another definition -/
def recordDep (def_ : DefId) : DepTrackM Unit := do
  modify fun ctx => { ctx with deps := ctx.deps.insert def_ }

/-- Record a dependency on a local definition -/
def recordLocalDep (name : String) : DepTrackM Unit := do
  let ctx ← get
  recordDep (DefId.local_ name ctx.moduleName)

/-- Get all recorded dependencies -/
def getDeps : DepTrackM (HashSet DefId) := do
  let ctx ← get
  return ctx.deps

/-- Run with dependency tracking, returning result and dependencies -/
def runTracking (def_ : DefId) (moduleName : String) (action : DepTrackM α)
    : TCM (α × HashSet DefId) := do
  let ctx : DepTrackingCtx := { currentDef := def_, moduleName := moduleName, deps := {} }
  let (result, ctx') ← action.run ctx
  return (result, ctx'.deps)

end DepTrackM

/-- Hash a string for use in syntax hashing -/
def hashString (s : String) : UInt64 :=
  hash s

/-- Combine two hashes -/
def combineHash (h1 h2 : UInt64) : UInt64 :=
  h1 ^^^ (h2 * 0x9e3779b97f4a7c15)  -- Golden ratio constant for mixing

/-- Combine multiple hashes -/
def combineHashes (hashes : Array UInt64) : UInt64 :=
  hashes.foldl combineHash 0

/-- Tag values for expression constructors (ensures different constructors hash differently) -/
private def exprTag : Nat → UInt64
  | 0 => 0x1000  -- var
  | 1 => 0x1001  -- lit
  | 2 => 0x1002  -- call
  | 3 => 0x1004  -- lam
  | 4 => 0x1005  -- closure
  | 5 => 0x1006  -- construct
  | 6 => 0x1007  -- tuple
  | 7 => 0x1008  -- record
  | 8 => 0x1009  -- recordUpdate
  | 9 => 0x100A  -- inject
  | 10 => 0x100B -- array
  | 11 => 0x100C -- if_
  | 12 => 0x100D -- case
  | 13 => 0x100E -- fieldAccess
  | 14 => 0x100F -- global
  | 15 => 0x1010 -- panic
  | 16 => 0x1011 -- proj
  | 17 => 0x1012 -- typeApp
  | 18 => 0x1013 -- type
  | 19 => 0x1014 -- pi
  | 20 => 0x1015 -- sigma
  | 21 => 0x1016 -- pair
  | 22 => 0x1017 -- fst
  | 23 => 0x1018 -- snd
  | 24 => 0x1019 -- primTy
  | 26 => 0x101B -- rowEmpty
  | 27 => 0x101C -- rowExtend
  | 28 => 0x101D -- recordTy
  | 29 => 0x101E -- variantTy
  | 30 => 0x101F -- labelLit
  | 31 => 0x1020 -- dataTy
  | 32 => 0x1021 -- ann
  | 33 => 0x1022 -- hole
  | 34 => 0x1023 -- mvar
  | 35 => 0x1024 -- eq
  | 36 => 0x1025 -- refl
  | 37 => 0x1026 -- transport
  | 38 => 0x1027 -- rowSort
  | 39 => 0x1028 -- labelSort
  | _ => 0x1FFF

/-- Hash a TypeExpr from the AST -/
partial def hashTypeExpr (te : Soma.Syntax.TypeExpr) : UInt64 :=
  match te with
  | .var name => combineHash 0x6000 (hashString name.value)
  | .con name => combineHash 0x6001 (hashString name.value)
  | .app fn arg _ =>
    combineHashes #[0x6002, hashTypeExpr fn, hashTypeExpr arg]
  | .arrow from_ to _ =>
    combineHashes #[0x6003, hashTypeExpr from_, hashTypeExpr to]
  | .tuple elements _ =>
    let elemsHash := elements.foldl (fun acc te => combineHash acc (hashTypeExpr te)) 0
    combineHash 0x6004 elemsHash
  | .list elem _ =>
    combineHash 0x6005 (hashTypeExpr elem)
  | .forall_ vars body _ =>
    let varsHash := vars.foldl (fun acc v =>
      combineHash acc (hashString v.name.value)) 0
    combineHashes #[0x6006, varsHash, hashTypeExpr body]
  | .constrained constraints body _ =>
    let constrHash := constraints.foldl (fun acc (name, args, _) =>
      let argsHash := args.foldl (fun h te => combineHash h (hashTypeExpr te)) 0
      combineHashes #[acc, hashString name.value, argsHash]) 0
    combineHashes #[0x6007, constrHash, hashTypeExpr body]
  | .parens inner _ =>
    combineHash 0x6008 (hashTypeExpr inner)
  | .kinded ty kind _ =>
    combineHashes #[0x6009, hashTypeExpr ty, hashTypeExpr kind]
  | .record fields tail _ =>
    let fieldsHash := fields.foldl (fun acc (name, te) =>
      combineHashes #[acc, hashString name.value, hashTypeExpr te]) 0
    let tailHash := match tail with | none => 0 | some n => hashString n.value
    combineHashes #[0x600A, fieldsHash, tailHash]
  | .variant cases tail _ =>
    let casesHash := cases.foldl (fun acc (name, te) =>
      combineHashes #[acc, hashString name.value, hashTypeExpr te]) 0
    let tailHash := match tail with | none => 0 | some n => hashString n.value
    combineHashes #[0x600B, casesHash, tailHash]
  | .pi qty name domain codomain _ =>
    combineHashes #[0x600C, hash qty, hashString name.value, hashTypeExpr domain, hashTypeExpr codomain]
  | .sigma qty name fst snd _ =>
    combineHashes #[0x600D, hash qty, hashString name.value, hashTypeExpr fst, hashTypeExpr snd]
  | .implicit name domain codomain _ =>
    let nameHash := match name with | none => 0 | some n => hashString n.value
    combineHashes #[0x600E, nameHash, hashTypeExpr domain, hashTypeExpr codomain]

/-- Hash a level -/
def hashLevel (l : Soma.Core.Level) : UInt64 :=
  match l with
  | .lit n => combineHash 0x5000 (hash n)
  | .var v => combineHash 0x5001 (hash v.id)
  | .max l1 l2 => combineHashes #[0x5002, hashLevel l1, hashLevel l2]
  | .succ l => combineHash 0x5003 (hashLevel l)

/-- Hash a Syntax.Expr by traversing its structure -/
partial def hashSyntaxExpr (e : Soma.Syntax.Expr) : UInt64 :=
  match e with
  | .var name => combineHash (exprTag 0) (hashString name.value)
  | .lit l => combineHash (exprTag 1) (match l with
      | .int n _ => hash n
      | .string s _ => hashString s
      | .bool b _ => hash b)
  | .app fn arg _ => combineHashes #[exprTag 2, hashSyntaxExpr fn, hashSyntaxExpr arg]
  | .infix op l r _ => combineHashes #[exprTag 3, hashString op.value, hashSyntaxExpr l, hashSyntaxExpr r]
  | .lambda params body _ => combineHashes #[exprTag 4, hash params.size, hashSyntaxExpr body]
  | .if_ cond then_ else_ _ => combineHashes #[exprTag 5, hashSyntaxExpr cond, hashSyntaxExpr then_, hashSyntaxExpr else_]
  | .case scruts arms _ =>
    let scrutsHash := scruts.foldl (fun acc s => combineHash acc (hashSyntaxExpr s)) 0
    let armsHash := arms.foldl (fun acc a => combineHash acc (hashSyntaxExpr a.body)) 0
    combineHashes #[exprTag 6, scrutsHash, armsHash]
  | .tuple elems _ => combineHash (exprTag 7) (elems.foldl (fun acc e => combineHash acc (hashSyntaxExpr e)) 0)
  | .list elems _ => combineHash (exprTag 8) (elems.foldl (fun acc e => combineHash acc (hashSyntaxExpr e)) 0)
  | .record fields _ => combineHash (exprTag 9) (fields.foldl (fun acc (_, v) => combineHash acc (hashSyntaxExpr v)) 0)
  | .recordUpdate base updates _ => combineHashes #[exprTag 10, hashSyntaxExpr base,
      updates.foldl (fun acc (_, v) => combineHash acc (hashSyntaxExpr v)) 0]
  | .fieldAccess expr field _ => combineHashes #[exprTag 11, hashSyntaxExpr expr, hashString field.value]
  | .projection typeName fieldName _ => combineHashes #[exprTag 12, hashString typeName.value, hashString fieldName.value]
  | .parens inner _ => hashSyntaxExpr inner
  | .typeAnnot expr ty _ => combineHashes #[exprTag 13, hashSyntaxExpr expr, hashTypeExpr ty]
  | .typeApp arg _ => combineHash (exprTag 14) (match arg with
      | .type ty => hashTypeExpr ty
      | .label name => hashString name.value)
  | .composeBlock stmts final_ _ =>
    let stmtHash := stmts.foldl (fun acc s => combineHash acc (match s with
      | .expr e _ => hashSyntaxExpr e
      | .let_ n v _ => combineHash (hashString n.value) (hashSyntaxExpr v)
      | .bind_ n a _ => combineHash (hashString n.value) (hashSyntaxExpr a))) 0
    combineHashes #[exprTag 16, stmtHash, hashSyntaxExpr final_]
  | .variant label arg _ => combineHashes #[exprTag 15, hashString label.value,
      match arg with | some a => hashSyntaxExpr a | none => 0]

/-- Hash a function by traversing its expression tree -/
def hashFunction (fn : Soma.Core.UntypedFunction) : UInt64 :=
  let nameHash := hashString fn.name.display
  let paramsHash := fn.params.foldl (fun acc name =>
    combineHash acc (hashString name)) 0
  let bodyHash := hashSyntaxExpr fn.body
  -- Also hash the declared type if present
  let typeHash := match fn.declaredTypeSyntax with
    | none => 0
    | some tyExpr => hashTypeExpr tyExpr
  combineHashes #[nameHash, paramsHash, bodyHash, typeHash]

/-- Hash a type definition for incremental checking -/
def hashTypeDef (td : Soma.Core.TypeDef) : UInt64 :=
  match td with
  | .algebraic attrs name typeVars ctors =>
    let attrsHash := attrs.foldl (fun acc a => combineHash acc (hashString a.name.value)) 0
    let nameHash := hashString name.display
    let varsHash := typeVars.foldl (fun acc v => combineHash acc (hashString v)) 0
    let ctorsHash := ctors.foldl (fun acc ctor =>
      combineHash acc (hashString ctor.name.display)) 0
    combineHashes #[0, attrsHash, nameHash, varsHash, ctorsHash]  -- 0 = algebraic tag
  | .record attrs name typeVars ctorName fields =>
    let attrsHash := attrs.foldl (fun acc a => combineHash acc (hashString a.name.value)) 0
    let nameHash := hashString name.display
    let varsHash := typeVars.foldl (fun acc v => combineHash acc (hashString v)) 0
    let ctorHash := hashString ctorName.display
    let fieldsHash := fields.foldl (fun acc (nameOpt, _) =>
      combineHash acc (hashString (nameOpt.getD "_"))) 0
    combineHashes #[1, attrsHash, nameHash, varsHash, ctorHash, fieldsHash]  -- 1 = record tag

/-- Hash all definitions in a module, returning a map from DefId to hash -/
def hashModuleDefinitions (moduleName : String) (module : Soma.Core.UntypedModule)
    : HashMap DefId UInt64 := Id.run do
  let mut hashes : HashMap DefId UInt64 := {}

  -- Hash functions
  for fn in module.functions do
    let defId := DefId.mk moduleName fn.name.display
    let fnHash := hashFunction fn
    hashes := hashes.insert defId fnHash

  -- Hash types
  for td in module.types do
    let typeName := match td with
      | .algebraic _ name _ _ => name.display
      | .record _ name _ _ _ => name.display
    let defId := DefId.mk moduleName typeName
    let typeHash := hashTypeDef td
    hashes := hashes.insert defId typeHash

  return hashes

end Soma.Dependent.Incremental
