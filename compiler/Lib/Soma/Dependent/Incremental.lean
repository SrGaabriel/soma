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
  deriving Inhabited

namespace IncrementalState

def empty : IncrementalState := {}

/-- Create initial state for a module -/
def forModule (_moduleName : String) : IncrementalState := {}

/-- Check if a definition is cached -/
def isCached (s : IncrementalState) (def_ : DefId) : Bool :=
  s.cache.contains def_

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
  { s with depGraph := s.depGraph.remove def_ }

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

end IncrementalState

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
  | 38 => 0x1027 -- rowSort
  | 39 => 0x1028 -- labelSort
  | _ => 0x1FFF

/-- Hash a level -/
def hashLevel (l : Soma.Core.Level) : UInt64 :=
  match l with
  | .prop => 0x5004
  | .lit n => combineHash 0x5000 (hash n)
  | .var v => combineHash 0x5001 (hash v.id)
  | .max l1 l2 => combineHashes #[0x5002, hashLevel l1, hashLevel l2]
  | .succ l => combineHash 0x5003 (hashLevel l)

/-- Hash a Syntax.Expr by traversing its structure -/
partial def hashSyntaxExpr (e : Soma.Syntax.Expr) : UInt64 :=
  match e with
  | .var name => combineHash (exprTag 0) (hashString name.name)
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
  | .fieldAccess expr field _ => combineHashes #[exprTag 11, hashSyntaxExpr expr, hashString field.name]
  | .projection typeName fieldName _ => combineHashes #[exprTag 12, hashString typeName.name, hashString fieldName.name]
  | .parens inner _ => hashSyntaxExpr inner
  | .typeAnnot expr ty _ => combineHashes #[exprTag 13, hashSyntaxExpr expr, hashSyntaxExpr ty]
  | .typeApp arg _ => combineHash (exprTag 14) (match arg with
      | .type ty => hashSyntaxExpr ty
      | .label name => hashString name.name)
  | .composeBlock stmts final_ _ =>
    let stmtHash := stmts.foldl (fun acc s => combineHash acc (match s with
      | .expr e _ => hashSyntaxExpr e
      | .let_ n v _ => combineHash (hashString n.name) (hashSyntaxExpr v)
      | .bind_ n a _ => combineHash (hashString n.name) (hashSyntaxExpr a))) 0
    combineHashes #[exprTag 16, stmtHash, hashSyntaxExpr final_]
  | .variant label arg _ => combineHashes #[exprTag 15, hashString label.name,
      match arg with | some a => hashSyntaxExpr a | none => 0]
  | .con name => combineHash (exprTag 17) (hashString name.name)
  | .arrow from_ to _ =>
    combineHashes #[exprTag 18, hashSyntaxExpr from_, hashSyntaxExpr to]
  | .pi qty binder name dom cod _ =>
    combineHashes #[exprTag 19, hash qty, hash binder, hashString name.name,
      hashSyntaxExpr dom, hashSyntaxExpr cod]
  | .sigma qty name fst snd _ =>
    combineHashes #[exprTag 20, hash qty, hashString name.name,
      hashSyntaxExpr fst, hashSyntaxExpr snd]
  | .forall_ vars body _ =>
    let varsHash := vars.foldl (fun acc v =>
      combineHash acc (hashString v.name.name)) 0
    combineHashes #[exprTag 21, varsHash, hashSyntaxExpr body]
  | .recordTy fields tail _ =>
    let fieldsHash := fields.foldl (fun acc (name, te) =>
      combineHashes #[acc, hashString name.name, hashSyntaxExpr te]) 0
    let tailHash := match tail with | none => 0 | some n => hashString n.name
    combineHashes #[exprTag 23, fieldsHash, tailHash]
  | .variantTy cases tail _ =>
    let casesHash := cases.foldl (fun acc (name, te) =>
      combineHashes #[acc, hashString name.name, hashSyntaxExpr te]) 0
    let tailHash := match tail with | none => 0 | some n => hashString n.name
    combineHashes #[exprTag 24, casesHash, tailHash]
  | .listTy elem _ => combineHash (exprTag 25) (hashSyntaxExpr elem)

/-- Hash a function by traversing its expression tree -/
def hashFunction (fn : Soma.Core.UntypedFunction) : UInt64 :=
  let nameHash := hashString fn.name.display
  let paramsHash := fn.params.foldl (fun acc p =>
    let nameHash := combineHash acc (hashString p.name)
    match p.typeSyntax with
    | none => nameHash
    | some tyExpr => combineHash nameHash (hashSyntaxExpr tyExpr)) 0
  let bodyHash := hashSyntaxExpr fn.body
  -- Also hash the declared type if present
  let typeHash := match fn.declaredTypeSyntax with
    | none => 0
    | some tyExpr => hashSyntaxExpr tyExpr
  combineHashes #[nameHash, paramsHash, bodyHash, typeHash]

/-- Hash a type definition for incremental checking -/
def hashTypeDef (td : Soma.Core.TypeDef) : UInt64 :=
  match td with
  | .algebraic attrs name binders paramCount ctors headSort _ =>
    let attrsHash := attrs.foldl (fun acc a => combineHash acc (hashString a.name.name)) 0
    let nameHash := hashString name.display
    let varsHash := binders.foldl
      (fun acc v =>
        let kHash := match v.kind with
          | some k => hashSyntaxExpr k
          | none => 0
        combineHash (combineHash acc (hashString v.name.name)) kHash) 0
    let ctorsHash := ctors.foldl (fun acc ctor =>
      combineHash acc (hashString ctor.name.display)) 0
    let sortHash := hashLevel headSort
    let pCountHash : UInt64 := UInt64.ofNat paramCount
    combineHashes #[0, attrsHash, nameHash, varsHash, ctorsHash, sortHash, pCountHash]
  | .record attrs name binders ctorName fields _ =>
    let attrsHash := attrs.foldl (fun acc a => combineHash acc (hashString a.name.name)) 0
    let nameHash := hashString name.display
    let varsHash := binders.foldl
      (fun acc v =>
        let kHash := match v.kind with
          | some k => hashSyntaxExpr k
          | none => 0
        combineHash (combineHash acc (hashString v.name.name)) kHash) 0
    let ctorHash := hashString ctorName.display
    let fieldsHash := fields.foldl (fun acc f =>
      let nameHash := hashString (f.name.getD "_")
      let tyHash := hashSyntaxExpr f.type
      let biHash : UInt64 := match f.binderInfo with
        | .explicit => 0 | .implicit => 1 | .instance_ => 2 | .strictImplicit => 3
      let qHash : UInt64 := match f.quantity with
        | .zero => 0 | .one => 1 | .omega => 2
      combineHashes #[acc, nameHash, tyHash, biHash, qHash]) 0
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
      | .algebraic _ name _ _ _ _ _ => name.display
      | .record _ name _ _ _ _ => name.display
    let defId := DefId.mk moduleName typeName
    let typeHash := hashTypeDef td
    hashes := hashes.insert defId typeHash

  return hashes

end Soma.Dependent.Incremental
