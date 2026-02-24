import Std.Data.HashSet
import Soma.Syntax
import Soma.Core.Module
import Soma.Core.Function
import Soma.Unique
import Soma.Project.Module
import Soma.Project.Graph
import Soma.Project.Symbol
import Soma.Dependent
import Soma.Dependent.Lower
import Soma.Dependent.Driver
import Soma.Dependent.Incremental
import Soma.Core.Value

namespace Soma.Project.Check

open Std (HashSet HashMap)
open Soma.Syntax
open Soma.Core
open Soma.Project
open Soma (UniqueSupply)
open Soma.Dependent (Globals GlobalInfo TCContext TCState InstanceEnv InstanceInfo ClassInfo AbbrevEnv AbbrevInfo TCM)
open Soma.Dependent.TraitElaborate (InstanceMap)
open Soma.Dependent.Incremental (DefId DefCache DefKind DepGraph IncrementalState hashString
  hashFunction hashModuleDefinitions)

/-- Derive module name from file path -/
def moduleNameFromPath (filePath : String) : String :=
  let parts := filePath.splitOn "/"
  let fileName := parts.getLast!
  let nameParts := fileName.splitOn "."
  if nameParts.isEmpty then fileName else nameParts.head!

/-- Create a file ID from path -/
def fileIdFromPath (filePath : String) : FileId :=
  ⟨filePath.hash.toNat⟩

/-- Result of parsing -/
structure ParseResult where
  sourceFile : SourceFile
  tree : ParsedTree
  diagnostics : Diagnostics

/-- Result of CST → AST lowering -/
structure LowerResult where
  ast : Syntax.Module
  diagnostics : Diagnostics

/-- Result of AST → Core untyped-module lowering -/
structure ElaborationResult where
  module : Soma.Core.UntypedModule
  diagnostics : Diagnostics

private def lowerModuleFromSyntax (ast : Syntax.Module) : ElaborationResult :=
  let lowered := Soma.Dependent.Lower.lowerModule ast
  { module := lowered.module, diagnostics := lowered.diagnostics }

/-- Phase 1+2: Parse source code (lex + parse combined) -/
def parse (filePath : String) (content : String) : ParseResult :=
  let sourceFile := SourceFile.create (fileIdFromPath filePath) filePath content
  let (tree, diags) := parseToTree sourceFile
  { sourceFile, tree, diagnostics := diags }

/-- Phase 2b: Incremental reparse -/
def reparse (oldTree : ParsedTree) (filePath : String) (content : String)
    : ParseResult × HashSet NodeId :=
  let sourceFile := SourceFile.create (fileIdFromPath filePath) filePath content
  let (tree, diags) := reparseToTree oldTree sourceFile
  let oldIds := oldTree.red.idToIdx
  let newIds := tree.red.idToIdx
  let changedIds := newIds.fold (init := {}) fun acc nodeId _ =>
    if oldIds.contains nodeId then acc else acc.insert nodeId
  ({ sourceFile, tree, diagnostics := diags }, changedIds)

/-- Phase 3: Lower CST to AST -/
def lower (tree : ParsedTree) (moduleName : String) : LowerResult :=
  let (ast, diags) := Syntax.lower tree moduleName
  { ast, diagnostics := diags }

/-- Phase 4: Lower AST to Core untyped module -/
def elaborate (ast : Syntax.Module) : ElaborationResult :=
  lowerModuleFromSyntax ast

/-- Phase 4 with external symbols: Lower AST to Core untyped module with pre-populated GlobalEnv -/
def elaborateWithExternals (ast : Syntax.Module) : ElaborationResult :=
  lowerModuleFromSyntax ast

/-- Phase 4b: Incremental elaboration -/
def elaborateIncremental (ast : Syntax.Module) (changedNames : Array String)
    (_oldResult : ElaborationResult) : ElaborationResult :=
  -- We lower directly from Syntax in one pass.
  let _ := changedNames
  elaborate ast

/-- Errors that can occur during project checking -/
inductive CheckError where
  | parseError (module : String) (message : String)
  | typeError (module : String) (errors : Array String)
  | cyclicDependency (modules : Array String)
  | dependencyNotFound (name : String) (path : String)
  | dependencyLoadError (name : String) (message : String)
  deriving Repr

instance : ToString CheckError where
  toString
    | .parseError m msg => s!"Parse error in {m}: {msg}"
    | .typeError m errs => s!"Type errors in {m}:\n" ++ String.intercalate "\n" errs.toList
    | .cyclicDependency mods => s!"Cyclic dependency: {mods.toList}"
    | .dependencyNotFound name path => s!"Dependency '{name}' not found at {path}"
    | .dependencyLoadError name msg => s!"Failed to load dependency '{name}': {msg}"

/-- A fully checked module with typed IR and public exports -/
structure CheckedModule where
  /-- Module name -/
  name : String
  /-- Resolved AST after parsing and lowering -/
  resolvedAst : Syntax.Module
  /-- The untyped Core module (declarations lowered from syntax) -/
  untypedModule : Soma.Core.UntypedModule
  /-- Globals environment from type checking (contains all definitions with types) -/
  globals : Globals
  /-- Instance environment from type checking -/
  instanceEnv : InstanceEnv
  /-- Abbreviation environment from type checking -/
  abbrevEnv : AbbrevEnv
  /-- Map from instance source spans to elaborated InstanceInfo -/
  instanceMap : InstanceMap
  /-- Public symbols exported by this module (symbol -> type as Value) -/
  publicSymbols : SymbolEnv
  /-- Public type class instances exported by this module -/
  publicInstances : InstanceMetadata
  /-- Source file for error reporting -/
  sourceFile : SourceFile
  /-- Incremental checking state (dependency tracking and caching) -/
  incrementalState : IncrementalState := IncrementalState.empty
  /-- Typed function bodies from type checking -/
  typedFunctions : Std.HashMap String Soma.Core.TypedFunction := {}
  /-- Usage counts from type checking -/
  usages : Std.HashMap Soma.Unique Nat := {}

namespace CheckedModule

/-- Extract constructor metadata from this module -/
def constructorMetadata (m : CheckedModule) : Std.HashMap String Nat :=
  let fromInductives := m.globals.inductives.fold (init := {}) fun acc _ indInfo =>
    indInfo.ctors.foldl (init := acc) fun acc2 ctor =>
      acc2.insert ctor.name.display ctor.tag
  m.globals.foldDecls (init := fromInductives) fun acc name info =>
    if info.isConstructor && !acc.contains name then
      acc.insert name info.ctorTag
    else acc

end CheckedModule

/-- External dependency loaded from metadata JSON -/
structure ExternalDependency where
  /-- Dependency name -/
  name : String
  /-- Metadata version -/
  version : Option String := none
  /-- Symbols by module name (symbol -> type as Value) -/
  symbols : Std.HashMap String SymbolEnv
  /-- Instances by module name -/
  instances : Std.HashMap String InstanceMetadata
  /-- Constructor tags by name -/
  constructors : Std.HashMap String Nat
  /-- Globals for type checking context -/
  globals : Globals
  /-- Instance environment -/
  instanceEnv : InstanceEnv
  /-- Abbreviation environment -/
  abbrevEnv : AbbrevEnv

/-- Configuration for project checking -/
structure ProjectConfig where
  /-- Root input path (file or directory) -/
  input : System.FilePath
  /-- Optional package/module name override -/
  name : Option String := none
  /-- External dependency paths: (name, path to .meta.json) -/
  deps : Array (String × System.FilePath) := #[]

/-- Result of project checking (type-checking phase) -/
structure ProjectResult where
  /-- Whether checking succeeded without errors -/
  success : Bool
  /-- All diagnostics (errors and warnings) -/
  diagnostics : Diagnostics
  /-- Name of the package/module -/
  packageName : String
  /-- Checked modules in dependency order -/
  checkedModules : Array CheckedModule
  /-- Aggregated public symbols from all modules -/
  symbols : SymbolEnv
  /-- Aggregated public instances from all modules -/
  instances : InstanceMetadata
  /-- Constructor metadata (name → tag) -/
  constructors : Std.HashMap String Nat
  /-- Merged globals for the entire project -/
  globals : Globals
  /-- Merged instance environment -/
  instanceEnv : InstanceEnv
  /-- Merged abbreviation environment -/
  abbrevEnv : AbbrevEnv
  /-- Source file map for resolving diagnostic spans -/
  sourceFiles : SourceFileMap

namespace ProjectResult

def failed (name : String) (diags : Diagnostics) (sourceFiles : SourceFileMap := SourceFileMap.empty) : ProjectResult :=
  { success := false, diagnostics := diags, packageName := name,
    checkedModules := #[], symbols := {}, instances := {}, constructors := {},
    globals := Globals.empty, instanceEnv := InstanceEnv.empty, abbrevEnv := AbbrevEnv.empty, sourceFiles }

def succeeded (name : String) (diags : Diagnostics) (modules : Array CheckedModule)
    (symbols : SymbolEnv) (instances : InstanceMetadata)
    (constructors : Std.HashMap String Nat)
    (globals : Globals) (instanceEnv : InstanceEnv) (abbrevEnv : AbbrevEnv)
    (sourceFiles : SourceFileMap) : ProjectResult :=
  { success := true, diagnostics := diags, packageName := name,
    checkedModules := modules, symbols, instances, constructors, globals, instanceEnv, abbrevEnv, sourceFiles }

end ProjectResult

/-- Merge two instance environments -/
def mergeInstanceEnvs (e1 e2 : InstanceMetadata) : InstanceMetadata :=
  e2.fold (init := e1) fun acc className instances =>
    match acc.get? className with
    | none => acc.insert className instances
    | some existing => acc.insert className (existing ++ instances)

/-- Merge Globals environments -/
def mergeGlobals (g1 g2 : Globals) : Globals :=
  -- Merge namespace trees recursively
  let mergedRoot := Soma.Dependent.Namespace.merge g1.root g2.root
  let intrinsics := g2.intrinsics.fold (init := g1.intrinsics) fun acc qn info =>
    acc.insert qn info
  let uniques := g2.uniques.fold (init := g1.uniques) fun acc name id =>
    acc.insert name id
  let structFields := g2.structFields.fold (init := g1.structFields) fun acc typeName fields =>
    acc.insert typeName fields
  let inductives := g2.inductives.fold (init := g1.inductives) fun acc typeName metaInfo =>
    acc.insert typeName metaInfo
  let ctorToInductive := g2.ctorToInductive.fold (init := g1.ctorToInductive) fun acc ctorName typeName =>
    acc.insert ctorName typeName
  let openNs := g2.openNamespaces.foldl (init := g1.openNamespaces) fun acc ns =>
    if acc.contains ns then acc else acc.push ns
  let wiredRoles := g2.wiredIn.roles.fold (init := g1.wiredIn.roles) fun acc role info =>
    if acc.contains role then acc else acc.insert role info
  { root := mergedRoot
    openNamespaces := openNs
    intrinsics := intrinsics
    uniques := uniques
    structFields := structFields
    inductives := inductives
    ctorToInductive := ctorToInductive
    wiredIn := { roles := wiredRoles }
  }

/-- Merge InstanceEnv (type class registry), deduplicating instances by instanceId -/
def mergeInstanceEnv (e1 e2 : InstanceEnv) : InstanceEnv :=
  -- Merge classes
  let classes := e2.classes.fold (init := e1.classes) fun acc uid info =>
    acc.insert uid info
  -- Merge instances, deduplicating by instanceId
  let instances := e2.instances.fold (init := e1.instances) fun acc uid insts =>
    match e1.instances.get? uid with
    | none => acc.insert uid insts
    | some existing =>
      -- Deduplicate: only add instances from insts that aren't already in existing
      let existingIds : Std.HashSet (Nat × String) := existing.foldl (init := {}) fun s inst =>
        s.insert (inst.instanceId.id, inst.instanceId.module)
      let newInsts := insts.filter fun inst =>
        !existingIds.contains (inst.instanceId.id, inst.instanceId.module)
      acc.insert uid (existing ++ newInsts)
  { classes := classes
    instances := instances
    nextInstanceId := max e1.nextInstanceId e2.nextInstanceId
    moduleName := e1.moduleName }

/-! ## Shared Type Checking Core

These functions provide the core type checking logic that can be shared between
the CLI (Check.lean) and LSP (Analysis.lean). They handle building globals,
instance environments, and checking functions with proper incremental state tracking.
-/

/-- Result of checking functions in a module -/
structure FunctionCheckResult where
  /-- Final TC state after checking all functions -/
  finalState : TCState
  /-- Updated incremental state with caches and dependencies -/
  incrementalState : IncrementalState
  /-- Typed function bodies (function name -> typed fn) -/
  typedFunctions : Std.HashMap String Soma.Core.TypedFunction
  /-- Errors encountered during checking -/
  errors : Array Soma.Dependent.TCError
  deriving Inhabited

/-- Check all functions in a module, tracking dependencies and caching results.
    This is the core function-checking loop shared by both CLI and LSP.

    Parameters:
    - `untypedModule`: The untyped Core module to check
    - `moduleName`: Name of the module (for DefId construction)
    - `ctx`: Type checking context with globals and instances
    - `initialState`: Initial TC state
    - `prevIncrState`: Previous incremental state (for caching)
    - `dirtyNames`: If Some, only check functions in this set; if None, check all -/
def checkFunctionsCore
  (untypedModule : Soma.Core.UntypedModule)
    (moduleName : String)
    (ctx : TCContext)
    (initialState : TCState)
    (prevIncrState : IncrementalState)
    (dirtyNames : Option (HashSet String))
    : FunctionCheckResult := Id.run do
  let mut errors : Array Soma.Dependent.TCError := #[]
  let mut currentState := initialState
  let mut incrState := prevIncrState
  let mut typedFns : Std.HashMap String Soma.Core.TypedFunction := {}

  for fn in untypedModule.functions do
    let fnName := fn.name.display
    let defId := DefId.mk moduleName fnName

    -- Determine if we should check this function
    let shouldCheck := match dirtyNames with
      | none => true  -- Check all
      | some dirty => dirty.contains fnName || !prevIncrState.isCached defId

    if shouldCheck then
      -- Clear dependency tracking before checking this function
      let stateWithClearedDeps := { currentState with globalDeps := {} }

      let checkResult := (Soma.Dependent.Driver.checkFunction fn).run ctx stateWithClearedDeps
      match checkResult with
      | .error e =>
        -- Record error but continue with next function
        errors := errors.push e
        -- Cache the failure for incremental re-checking
        let syntaxHash := hashFunction fn
        let cache := DefCache.failure syntaxHash (Value.vType Level.zero) DefKind.function #[e]
        incrState := incrState.updateCache defId cache
      | .ok ((fnType, typedBody, generatedParams), newState) =>
        -- Also collect any accumulated errors from error recovery
        errors := errors ++ newState.errors

        -- Store the typed function for downstream passes
        let typedFn : Soma.Core.TypedFunction := {
          name := fn.name
          params := generatedParams
          body := typedBody
          fnType := fnType
          closureInfo := fn.closureInfo
          attrs := fn.attrs
        }
        typedFns := typedFns.insert fnName typedFn

        -- Clear old dependencies and record new ones
        incrState := incrState.clearDeps defId
        let deps := newState.globalDeps
        for depName in deps do
          -- Only track dependencies on definitions in globals
          if ctx.globals.lookup depName |>.isSome then
            let depId := DefId.mk moduleName depName
            incrState := incrState.addDependency defId depId

        -- Cache successful result
        let syntaxHash := hashFunction fn
        let isComplete := newState.errors.isEmpty
        let cache := if isComplete then
          -- Look up the GlobalInfo from the context (it should be registered already)
          match ctx.globals.lookup fnName with
          | some info => DefCache.success syntaxHash fnType DefKind.function info
          | none =>
            -- Fallback: create a basic GlobalInfo if not found (shouldn't happen)
            let info : GlobalInfo := {
              name := fn.name
              type := fnType
              value := none
              isConstructor := false
              origin := .function
            }
            DefCache.success syntaxHash fnType DefKind.function info
        else
          DefCache.failure syntaxHash fnType DefKind.function newState.errors
        incrState := incrState.updateCache defId cache

        currentState := newState
    -- else: not dirty, keep cached result (already in incrState)

  return { finalState := currentState, incrementalState := incrState, typedFunctions := typedFns, errors := errors }

/-- Result of building globals and instance environment -/
structure GlobalsAndInstancesResult where
  /-- The built globals environment -/
  globals : Globals
  /-- The built instance environment -/
  instanceEnv : InstanceEnv
  /-- The built abbreviation environment -/
  abbrevEnv : AbbrevEnv
  /-- Map from instance source spans to elaborated InstanceInfo -/
  instanceMap : InstanceMap
  /-- Final TC state -/
  finalState : TCState
  /-- Errors encountered -/
  errors : Array Soma.Dependent.TCError
  deriving Inhabited

/-- Build globals and instance environment for a module with error recovery.
    Returns partial results even if some definitions fail.

    Parameters:
    - `untypedModule`: The untyped Core module
    - `moduleName`: Name of the module
    - `seedGlobals`: Globals inherited from dependencies
    - `seedInstanceEnv`: Instance env inherited from dependencies
    - `seedAbbrevEnv`: Abbreviation env inherited from dependencies
    - `prevGlobals`: Previous globals for incremental reuse (optional)
    - `prevInstanceEnv`: Previous instance env for incremental reuse (optional)
    - `prevInstanceMap`: Previous instance map for incremental reuse (optional)
    - `dirtyNames`: If Some, only rebuild dirty definitions; if None, rebuild all -/
def buildGlobalsAndInstances
  (untypedModule : Soma.Core.UntypedModule)
    (moduleName : String)
    (seedGlobals : Globals)
    (seedInstanceEnv : InstanceEnv)
    (seedAbbrevEnv : AbbrevEnv)
    (prevGlobals : Option Globals := none)
    (prevInstanceEnv : Option InstanceEnv := none)
    (prevInstanceMap : Option InstanceMap := none)
    (dirtyNames : Option (HashSet String) := none)
    : GlobalsAndInstancesResult := Id.run do
  let baseCtx := TCContext.withDefaultInstances
  let state := TCState.forModule moduleName
  let mut allErrors : Array Soma.Dependent.TCError := #[]

  -- Build abbreviation environment for this module
  let abbrevResult := (Soma.Dependent.Driver.buildAbbrevEnv untypedModule).run
    { baseCtx with globals := seedGlobals, abbrevEnv := seedAbbrevEnv } state

  let (moduleAbbrevEnv, state0, abbrevErrors) := match abbrevResult with
    | .error e => (AbbrevEnv.empty, state, #[e])
    | .ok (abbrevEnv, st) => (abbrevEnv, st, st.errors)

  allErrors := allErrors ++ abbrevErrors

  -- Merge with seed abbreviations
  let fullAbbrevEnv := AbbrevEnv.merge seedAbbrevEnv moduleAbbrevEnv

  -- Build globals with the full abbreviation environment
  let globalsResult := match dirtyNames, prevGlobals with
    | some dirty, some prev =>
      (Soma.Dependent.Driver.buildGlobalsIncremental untypedModule prev dirty).run
        { baseCtx with globals := seedGlobals, abbrevEnv := fullAbbrevEnv } state0
    | _, _ =>
      (Soma.Dependent.Driver.buildGlobals untypedModule).run
        { baseCtx with globals := seedGlobals, abbrevEnv := fullAbbrevEnv } state0

  let (moduleGlobals, state', globalsErrors) := match globalsResult with
    | .error e => (Globals.empty, state0, #[e])
    | .ok (globals, st) => (globals, st, st.errors)

  allErrors := allErrors ++ globalsErrors

  -- Merge with seed globals
  let fullGlobals := mergeGlobals seedGlobals moduleGlobals
  let ctx := { baseCtx with globals := fullGlobals, instanceEnv := seedInstanceEnv, abbrevEnv := fullAbbrevEnv }

  -- Build instance environment
  let instanceEnvResult := match dirtyNames, prevInstanceEnv, prevInstanceMap with
    | some dirty, some prev, some prevMap =>
      (Soma.Dependent.Driver.buildInstanceEnvIncremental untypedModule moduleName prev prevMap dirty).run ctx state'
    | _, _, _ =>
      (Soma.Dependent.Driver.buildInstanceEnv untypedModule moduleName).run ctx state'

  let (moduleInstanceEnv, instanceMap, state'', instanceErrors) := match instanceEnvResult with
    | .error e => (InstanceEnv.empty, {}, state', #[e])
    | .ok ((instEnv, instMap), st) => (instEnv, instMap, st, st.errors)

  allErrors := allErrors ++ instanceErrors

  let fullInstanceEnv := mergeInstanceEnv seedInstanceEnv moduleInstanceEnv

  return {
    globals := fullGlobals
    instanceEnv := fullInstanceEnv
    abbrevEnv := fullAbbrevEnv
    instanceMap := instanceMap
    finalState := state''
    errors := allErrors
  }

/-- Result of type checking a module -/
structure TypeCheckResult where
  globals : Globals
  instanceEnv : InstanceEnv
  abbrevEnv : AbbrevEnv
  instanceMap : InstanceMap
  incrementalState : IncrementalState
  usages : Std.HashMap Soma.Unique Nat
  /-- Typed function bodies (function name -> typed fn) -/
  typedFunctions : Std.HashMap String Soma.Core.TypedFunction
  errors : Array Soma.Dependent.TCError
  deriving Inhabited

def typeCheckModule
  (untypedModule : Soma.Core.UntypedModule)
    (moduleName : String)
    (seedGlobals : Globals)
    (seedInstanceEnv : InstanceEnv)
    (seedAbbrevEnv : AbbrevEnv)
    (prevIncrState : Option IncrementalState := none)
    : TypeCheckResult := Id.run do
  -- Determine dirty names if we have previous state
  let (dirtyNames, baseIncrState) := match prevIncrState with
    | some prev =>
      let currentHashes := hashModuleDefinitions moduleName untypedModule
      let updated := prev.invalidateChanged currentHashes
      let dirtyDefs := updated.getDirtyInOrder
      let dirty : HashSet String := dirtyDefs.foldl (init := {}) fun (acc : HashSet String) (defId : DefId) =>
        acc.insert defId.name
      (some dirty, updated)
    | none =>
      (none, IncrementalState.forModule moduleName)

  -- Get previous globals/instanceEnv/instanceMap for incremental building
  let prevGlobals : Option Globals := prevIncrState.map (fun (s : IncrementalState) => s.cachedGlobals)
  let prevInstanceEnv : Option InstanceEnv := prevIncrState.map (fun (s : IncrementalState) => s.cachedInstanceEnv)
  let prevInstanceMap : Option InstanceMap := prevIncrState.map (fun (s : IncrementalState) => s.cachedInstanceMap)

  -- Build globals, instance environment, and abbreviation environment
  let globalsResult := buildGlobalsAndInstances
    untypedModule moduleName seedGlobals seedInstanceEnv seedAbbrevEnv prevGlobals prevInstanceEnv prevInstanceMap dirtyNames

  let mut allErrors := globalsResult.errors

  -- Prepare context for function checking
  let baseCtx := TCContext.withDefaultInstances
  let ctx := { baseCtx with
    globals := globalsResult.globals
    instanceEnv := globalsResult.instanceEnv
    abbrevEnv := globalsResult.abbrevEnv }

  -- Check functions
  let fnResult := checkFunctionsCore
    untypedModule moduleName ctx globalsResult.finalState baseIncrState dirtyNames

  allErrors := allErrors ++ fnResult.errors

  let usages : Std.HashMap Soma.Unique Nat :=
    fnResult.finalState.usages.fold (init := {}) fun acc bindingId count =>
      acc.insert
        { id := bindingId.id, module := bindingId.module, original := bindingId.original }
        count

  -- Update incremental state with final globals and instance map
  let finalIncrState := { fnResult.incrementalState with
    cachedGlobals := globalsResult.globals
    cachedInstanceEnv := globalsResult.instanceEnv
    cachedInstanceMap := globalsResult.instanceMap }

  return {
    globals := globalsResult.globals
    instanceEnv := globalsResult.instanceEnv
    abbrevEnv := globalsResult.abbrevEnv
    instanceMap := globalsResult.instanceMap
    incrementalState := finalIncrState
    usages := usages
    typedFunctions := fnResult.typedFunctions
    errors := allErrors
  }

/-- Extract public symbols from a type-checked module -/
def extractPublicSymbols
  (untypedModule : Soma.Core.UntypedModule)
    (globals : Globals)
    (packageName : String)
    (moduleName : String)
    (seed : SymbolEnv)
    (supply : UniqueSupply)
    (explicitExports : Option (Array String) := none)
    (seedSymbols : SymbolEnv := {})
    : SymbolEnv × UniqueSupply := Id.run do
  let mut acc := seed
  let mut sup := supply

  -- Track which symbols we've already added (to avoid duplicates)
  let mut addedNames : Std.HashSet String := {}

  -- Helper to check if a name should be exported
  let shouldExport (name : String) : Bool :=
    match explicitExports with
    | none => true -- No explicit exports means export everything defined
    | some exports => exports.contains name

  -- Extract function symbols
  for fn in untypedModule.functions do
    let fnName := fn.name.display
    if shouldExport fnName then
      match globals.lookup fnName with
      | some info =>
        let unique := fn.name.id
        let sup' := sup
        sup := sup'
        let sym : Symbol := {
          unique := unique
          name := fnName
          kind := .binding
          module := moduleName
          package := packageName
          span := fn.span
        }
        acc := acc.insert sym info.type
        addedNames := addedNames.insert fnName
      | none => pure ()

  -- Extract type definitions and constructors
  for typeDef in untypedModule.types do
    match typeDef with
    | .algebraic typeName _typeVars constructors =>
      let typeNameStr := typeName.display
      if shouldExport typeNameStr then
        -- Register type
        let (typeUnique, sup') := sup.fresh typeNameStr
        sup := sup'
        let typeSym : Symbol := {
          unique := typeUnique
          name := typeNameStr
          kind := .type
          module := moduleName
          package := packageName
          span := Span.uninhabited
        }
        -- Type itself maps to Type₀
        acc := acc.insert typeSym (Value.vType Level.zero)
        addedNames := addedNames.insert typeNameStr

      -- Register constructors
      for ctor in constructors do
        let ctorSimpleName := ctor.name.id.original
        if shouldExport ctorSimpleName then
          let ctorQualified := s!"{typeNameStr}::{ctorSimpleName}"
          match globals.lookup ctorQualified with
          | some ctorInfo =>
            let (ctorUnique, sup') := sup.fresh ctorSimpleName
            sup := sup'
            let ctorSym : Symbol := {
              unique := ctorUnique
              name := ctorSimpleName
              kind := .dataCon typeNameStr ctor.tag
              module := moduleName
              package := packageName
              span := Span.uninhabited
            }
            acc := acc.insert ctorSym ctorInfo.type
            addedNames := addedNames.insert ctorSimpleName
          | none => pure ()

    | .struct structName _typeVars _ctorName fields =>
      let structNameStr := structName.display
      if shouldExport structNameStr then
        let (structUnique, sup') := sup.fresh structNameStr
        sup := sup'
        let structSym : Symbol := {
          unique := structUnique
          name := structNameStr
          kind := .type
          module := moduleName
          package := packageName
          span := Span.uninhabited
        }
        acc := acc.insert structSym (Value.vType Level.zero)
        addedNames := addedNames.insert structNameStr

      -- Register struct constructor (named "new" in namespace)
      let ctorQualified := s!"{structNameStr}::new"
      if shouldExport structNameStr then
        match globals.lookup ctorQualified with
        | some ctorInfo =>
          let (ctorUnique, sup') := sup.fresh ctorQualified
          sup := sup'
          let ctorSym : Symbol := {
            unique := ctorUnique
            name := ctorQualified
            kind := .dataCon structNameStr 0
            module := moduleName
            package := packageName
            span := Span.uninhabited
          }
          acc := acc.insert ctorSym ctorInfo.type
          addedNames := addedNames.insert ctorQualified
        | none => pure ()

      -- Register field accessors
      for (fieldNameOpt, _) in fields do
        if let some fieldName := fieldNameOpt then
          let accessorName := s!"{structNameStr}::{fieldName}"
          if shouldExport accessorName then
            match globals.lookup accessorName with
            | some accessorInfo =>
              let (accessorUnique, sup') := sup.fresh accessorName
              sup := sup'
              let accessorSym : Symbol := {
                unique := accessorUnique
                name := accessorName
                kind := .binding
                module := moduleName
                package := packageName
                span := Span.uninhabited
              }
              acc := acc.insert accessorSym accessorInfo.type
              addedNames := addedNames.insert accessorName
            | none => pure ()

    | .record _ _ _ => pure ()

  -- Extract type class methods
  for typeClass in untypedModule.typeClasses do
    let className := typeClass.name.display
    if shouldExport className then
      addedNames := addedNames.insert className
    for (methodName, _) in typeClass.methodSignatures do
      let methodNameStr := methodName.display
      if shouldExport methodNameStr then
        match globals.lookup methodNameStr with
        | some methodInfo =>
          let (methodUnique, sup') := sup.fresh methodNameStr
          sup := sup'
          let methodSym : Symbol := {
            unique := methodUnique
            name := methodNameStr
            kind := .typeClassMethod className
            module := moduleName
            package := packageName
            span := Span.uninhabited
          }
          acc := acc.insert methodSym methodInfo.type
          addedNames := addedNames.insert methodNameStr
        | none => pure ()

  if let some exports := explicitExports then
    for exportName in exports do
      if !addedNames.contains exportName then
        -- This is a re-exported symbol from a dependency
        for (sym, ty) in seedSymbols.toArray do
          if sym.name == exportName then
            -- Re-export with updated module attribution
            let (newUnique, sup') := sup.fresh exportName
            sup := sup'
            let reexportSym : Symbol := {
              unique := newUnique
              name := sym.name
              kind := sym.kind
              module := moduleName
              package := packageName
              span := Span.uninhabited
            }
            acc := acc.insert reexportSym ty
            break

  pure (acc, sup)

/-- Extract public instances from a type-checked module -/
def extractPublicInstances
  (untypedModule : Soma.Core.UntypedModule)
    (instanceMap : InstanceMap)
    (packageName : String)
    (moduleName : String)
    (seed : InstanceMetadata)
    (supply : UniqueSupply)
    : InstanceMetadata × UniqueSupply := Id.run do
  let mut acc := seed
  let mut sup := supply

  for inst in untypedModule.instances do
    let className := inst.className
    let instanceName := s!"{inst.className}$inst{inst.typeArgsSyntax.size}"
    let (unique, sup') := sup.fresh instanceName
    sup := sup'
    let sym : Symbol := {
      unique := unique
      name := className
      kind := .instanceMethod instanceName className
      module := moduleName
      package := packageName
      span := inst.span
    }
    -- Look up the elaborated instance info directly by span
    let typeArgs : Array Value := match instanceMap.get? inst.span with
      | some instInfo => instInfo.args
      | none => #[]
    match acc.get? className with
    | none => acc := acc.insert className #[(typeArgs, sym)]
    | some existing => acc := acc.insert className (existing.push (typeArgs, sym))

  pure (acc, sup)

/-- Process external dependencies into lookup tables -/
def processExternalDependencies (deps : Array ExternalDependency)
    : Std.HashMap String SymbolEnv × Std.HashMap String InstanceMetadata × Std.HashMap String Nat × Globals × InstanceEnv × AbbrevEnv :=
  deps.foldl (init := ({}, {}, {}, Globals.empty, InstanceEnv.empty, AbbrevEnv.empty)) fun (symbols, instances, constructors, globals, instEnv, abbrevEnv) dep =>
    let symbols' := dep.symbols.fold (init := symbols) fun acc modName env =>
      acc.insert modName env
    let instances' := dep.instances.fold (init := instances) fun acc modName env =>
      acc.insert modName env
    let constructors' := dep.constructors.fold (init := constructors) fun acc ctorName tag =>
      acc.insert ctorName tag
    let globals' := mergeGlobals globals dep.globals
    let instEnv' := mergeInstanceEnv instEnv dep.instanceEnv
    let abbrevEnv' := AbbrevEnv.merge abbrevEnv dep.abbrevEnv
    (symbols', instances', constructors', globals', instEnv', abbrevEnv')

/-- Extract prelude symbols from external dependencies -/
def extractPreludeSymbols (extSymbols : Std.HashMap String SymbolEnv) : Array String :=
  match extSymbols.get? preludeModuleName with
  | none => #[]
  | some env => env.toArray.map fun (sym, _) => sym.name

/-- Check a single module with access to already-checked dependencies using dependent types.
    Uses error recovery to continue checking and produce partial results even on errors. -/
def checkModule
    (info : ModuleInfo)
    (checkedDeps : Std.HashMap String CheckedModule)
    (externalGlobals : Globals)
    (externalInstanceEnv : InstanceEnv)
    (externalAbbrevEnv : AbbrevEnv)
    (externalSymbols : SymbolEnv)
    (packageName : String)
    (supply : UniqueSupply)
    : Diagnostics × Option CheckedModule × UniqueSupply := Id.run do
  let modName := info.name.toString

  -- Collect globals from checked dependencies
  let seedGlobals := checkedDeps.fold (init := externalGlobals) fun acc _ dep =>
    mergeGlobals acc dep.globals

  -- Collect instance env from checked dependencies
  let seedInstanceEnv := checkedDeps.fold (init := externalInstanceEnv) fun acc _ dep =>
    mergeInstanceEnv acc dep.instanceEnv

  -- Collect abbrev env from checked dependencies
  let seedAbbrevEnv := checkedDeps.fold (init := externalAbbrevEnv) fun acc _ dep =>
    AbbrevEnv.merge acc dep.abbrevEnv

  -- Collect symbol env from checked dependencies
  let _seedSymbols := checkedDeps.fold (init := externalSymbols) fun acc _ dep =>
    dep.publicSymbols.fold (init := acc) fun env sym ty => env.insert sym ty

  -- Lower AST to Core untyped module
  let elabRes := elaborateWithExternals info.ast
  if elabRes.diagnostics.hasErrors then
    return (elabRes.diagnostics, none, supply)

  -- Use the shared type checking pipeline (fresh check, no previous state)
  let tcResult := typeCheckModule elabRes.module modName seedGlobals seedInstanceEnv seedAbbrevEnv none

  let allDiags := tcResult.errors.map (·.toDiagnostic)

  -- Extract public symbols and instances (always do this, even with errors)
  let depSymbols : SymbolEnv := checkedDeps.fold (init := externalSymbols) fun acc _ dep =>
    dep.publicSymbols.fold (init := acc) fun env sym ty => env.insert sym ty

  -- Check for explicit exports in the AST
  let explicitExports : Option (Array String) := info.ast.decls.findSome? fun decl =>
    match decl with
    | .export_ items _ => some (items.map (·.value))
    | _ => none

  let (publicSymbols, supply') := extractPublicSymbols
    elabRes.module tcResult.globals packageName modName {} supply explicitExports depSymbols

  let depInstances : InstanceMetadata := checkedDeps.fold (init := {}) fun acc _ dep =>
    mergeInstanceEnvs acc dep.publicInstances

  let (publicInstances, supply'') := extractPublicInstances
    elabRes.module tcResult.instanceMap packageName modName depInstances supply'

  -- Always produce a CheckedModule, even with errors
  -- This enables IDE features to work with partial information
  let checkedModule : CheckedModule := {
    name := modName
    resolvedAst := info.ast
    untypedModule := elabRes.module
    globals := tcResult.globals
    instanceEnv := tcResult.instanceEnv
    abbrevEnv := tcResult.abbrevEnv
    instanceMap := tcResult.instanceMap
    publicSymbols := publicSymbols
    publicInstances := publicInstances
    sourceFile := info.sourceFile
    incrementalState := tcResult.incrementalState
    typedFunctions := tcResult.typedFunctions
    usages := tcResult.usages
  }

  (elabRes.diagnostics ++ allDiags, some checkedModule, supply'')

/-- Check a single module incrementally, reusing cached results for unchanged definitions.
    This is the main entry point for incremental type checking in the LSP. -/
def checkModuleIncremental
    (info : ModuleInfo)
    (prevModule : CheckedModule)
    (checkedDeps : Std.HashMap String CheckedModule)
    (externalGlobals : Globals)
    (externalInstanceEnv : InstanceEnv)
    (externalAbbrevEnv : AbbrevEnv)
    (externalSymbols : SymbolEnv)
    (packageName : String)
    (supply : UniqueSupply)
    : Diagnostics × Option CheckedModule × UniqueSupply := Id.run do
  let modName := info.name.toString

  -- Collect globals from checked dependencies
  let seedGlobals := checkedDeps.fold (init := externalGlobals) fun acc _ dep =>
    mergeGlobals acc dep.globals

  let seedInstanceEnv := checkedDeps.fold (init := externalInstanceEnv) fun acc _ dep =>
    mergeInstanceEnv acc dep.instanceEnv

  let seedAbbrevEnv := checkedDeps.fold (init := externalAbbrevEnv) fun acc _ dep =>
    AbbrevEnv.merge acc dep.abbrevEnv

  let _seedSymbols := checkedDeps.fold (init := externalSymbols) fun acc _ dep =>
    dep.publicSymbols.fold (init := acc) fun env sym ty => env.insert sym ty

  -- Lower AST to Core untyped module
  let elabRes := elaborateWithExternals info.ast
  if elabRes.diagnostics.hasErrors then
    return (elabRes.diagnostics, none, supply)

  -- Use the shared type checking pipeline with previous state for incremental checking
  let tcResult := typeCheckModule elabRes.module modName seedGlobals seedInstanceEnv seedAbbrevEnv (some prevModule.incrementalState)

  -- If nothing changed (empty errors and same state), we could reuse previous result
  -- But for correctness, we rebuild anyway since the lowered module might have changed

  let allDiags := tcResult.errors.map (·.toDiagnostic)

  -- Extract public symbols and instances
  let depSymbols : SymbolEnv := checkedDeps.fold (init := externalSymbols) fun acc _ dep =>
    dep.publicSymbols.fold (init := acc) fun env sym ty => env.insert sym ty

  -- Check for explicit exports in the AST
  let explicitExports : Option (Array String) := info.ast.decls.findSome? fun decl =>
    match decl with
    | .export_ items _ => some (items.map (·.value))
    | _ => none

  let (publicSymbols, supply') := extractPublicSymbols
    elabRes.module tcResult.globals packageName modName {} supply explicitExports depSymbols

  let depInstances : InstanceMetadata := checkedDeps.fold (init := {}) fun acc _ dep =>
    mergeInstanceEnvs acc dep.publicInstances

  let (publicInstances, supply'') := extractPublicInstances
    elabRes.module tcResult.instanceMap packageName modName depInstances supply'

  let checkedModule : CheckedModule := {
    name := modName
    resolvedAst := info.ast
    untypedModule := elabRes.module
    globals := tcResult.globals
    instanceEnv := tcResult.instanceEnv
    abbrevEnv := tcResult.abbrevEnv
    instanceMap := tcResult.instanceMap
    publicSymbols := publicSymbols
    publicInstances := publicInstances
    sourceFile := info.sourceFile
    incrementalState := tcResult.incrementalState
    typedFunctions := tcResult.typedFunctions
    usages := tcResult.usages
  }

  (elabRes.diagnostics ++ allDiags, some checkedModule, supply'')

/-- Check all modules in topological order -/
def checkModulesInOrder
    (sortedNames : Array String)
    (graph : ModuleGraph)
    (externalGlobals : Globals)
    (externalInstanceEnv : InstanceEnv)
    (externalAbbrevEnv : AbbrevEnv)
    (externalSymbols : SymbolEnv)
    (packageName : String)
    (supply : UniqueSupply)
    : Diagnostics × Array CheckedModule × UniqueSupply :=
  let (allDiags, _, results, finalSupply) := sortedNames.foldl
    (init := (#[], ({} : Std.HashMap String CheckedModule), #[], supply))
    fun (diags, checked, results, sup) modName =>
      match graph.get? modName with
      | none => (diags, checked, results, sup)
      | some info =>
        let (moduleDiags, cmOpt, sup') := checkModule info checked externalGlobals externalInstanceEnv externalAbbrevEnv externalSymbols packageName sup
        match cmOpt with
        | some cm => (diags ++ moduleDiags, checked.insert modName cm, results.push cm, sup')
        | none => (diags ++ moduleDiags, checked, results, sup')
  (allDiags, results, finalSupply)

/-- Parse a single source file into a ModuleInfo -/
def parseModuleFile (moduleName : String) (path : System.FilePath) : IO (Except Diagnostics ModuleInfo) := do
  let content ← IO.FS.readFile path
  let parseRes := parse path.toString content
  if parseRes.diagnostics.hasErrors then
    pure (.error parseRes.diagnostics)
  else
    let lowerRes := lower parseRes.tree moduleName
    let allDiags := parseRes.diagnostics ++ lowerRes.diagnostics
    if allDiags.hasErrors then
      pure (.error allDiags)
    else
      let modName := ModuleName.fromString moduleName
      pure (.ok {
        name := modName
        path := path
        content := content
        sourceFile := parseRes.sourceFile
        ast := lowerRes.ast
        contentHash := some (hash content)
      })

/-- Parse all modules in a list, collecting errors -/
def parseModuleFiles (modules : Array (String × System.FilePath)) : IO (Diagnostics × ModuleGraph × SourceFileMap) := do
  let mut graph : ModuleGraph := {}
  let mut sourceMap : SourceFileMap := SourceFileMap.empty
  let mut allDiags : Diagnostics := #[]

  for (name, path) in modules do
    match ← parseModuleFile name path with
    | .ok info =>
      graph := graph.insert name info
      sourceMap := sourceMap.insert info.sourceFile
    | .error diags => allDiags := allDiags ++ diags

  pure (allDiags, graph, sourceMap)

/-- Check a single .soma file -/
def checkSingleFile
    (config : ProjectConfig)
    (loadDeps : Array (String × System.FilePath) → IO (Except CheckError (Array ExternalDependency)))
    : IO ProjectResult := do
  let path := config.input
  let name := config.name.getD (path.fileStem.getD "Main")

  match ← parseModuleFile name path with
  | .error diags =>
    pure (ProjectResult.failed name diags)

  | .ok info =>
    let sourceMap := SourceFileMap.fromSingle info.sourceFile
    let graph : ModuleGraph := ({} : ModuleGraph).insert name info
    let depGraph := buildDependencyGraph graph

    match topoSortModules depGraph with
    | .cycles cyclicDeps =>
      let diags := cyclicDeps.filterMap fun cycle =>
        cycle.imports[0]?.map fun edge =>
          let msg := s!"Cyclic import detected: {cycle.modules.toList}"
          Diagnostic.error msg edge.importSpan
      pure (ProjectResult.failed name diags sourceMap)

    | .sorted sortedNames =>
      match ← loadDeps config.deps with
      | .error e =>
        pure (ProjectResult.failed name #[Diagnostic.error (toString e) Span.uninhabited] sourceMap)

      | .ok deps =>
        let (extSymbolsByModule, _, extConstructors, extGlobals, extInstanceEnv, extAbbrevEnv) := processExternalDependencies deps
        -- Flatten external symbols into a single SymbolEnv
        let extSymbols : SymbolEnv := extSymbolsByModule.fold (init := {}) fun acc _ env =>
          env.fold (init := acc) fun e sym ty => e.insert sym ty
        let supply := UniqueSupply.initial name

        let (checkDiags, checkedModules, _) := checkModulesInOrder
          sortedNames graph extGlobals extInstanceEnv extAbbrevEnv extSymbols name supply

        let symbols := checkedModules.foldl (init := {}) fun acc m =>
          m.publicSymbols.fold (init := acc) fun env sym val => env.insert sym val
        let instances := checkedModules.foldl (init := {}) fun acc m =>
          mergeInstanceEnvs acc m.publicInstances
        let constructors := checkedModules.foldl (init := extConstructors) fun acc m =>
          let ctors := m.constructorMetadata
          ctors.fold (init := acc) fun env n tag => env.insert n tag
        let globals := checkedModules.foldl (init := extGlobals) fun acc m =>
          mergeGlobals acc m.globals
        let instanceEnv := checkedModules.foldl (init := extInstanceEnv) fun acc m =>
          mergeInstanceEnv acc m.instanceEnv
        let abbrevEnv := checkedModules.foldl (init := extAbbrevEnv) fun acc m =>
          AbbrevEnv.merge acc m.abbrevEnv

        if checkDiags.hasErrors then
          pure (ProjectResult.failed name checkDiags sourceMap)
        else
          pure (ProjectResult.succeeded name checkDiags checkedModules symbols instances constructors globals instanceEnv abbrevEnv sourceMap)

/-- Check a project directory -/
def checkDirectory
    (config : ProjectConfig)
    (loadDeps : Array (String × System.FilePath) → IO (Except CheckError (Array ExternalDependency)))
    : IO ProjectResult := do
  let rootDir := config.input
  let packageName := config.name.getD (rootDir.fileName.getD "app")

  let modules ← findModules packageName rootDir

  let (parseDiags, graph, sourceMap) ← parseModuleFiles modules

  if parseDiags.hasErrors then
    pure (ProjectResult.failed packageName parseDiags sourceMap)
  else
    let depGraph := buildDependencyGraph graph

    match topoSortModules depGraph with
    | .cycles cyclicDeps =>
      let diags := cyclicDeps.filterMap fun cycle =>
        cycle.imports[0]?.map fun edge =>
          let msg := s!"Cyclic import detected: {cycle.modules.toList}"
          Diagnostic.error msg edge.importSpan
      pure (ProjectResult.failed packageName diags sourceMap)

    | .sorted sortedNames =>
      match ← loadDeps config.deps with
      | .error e =>
        pure (ProjectResult.failed packageName #[Diagnostic.error (toString e) Span.uninhabited] sourceMap)

      | .ok deps =>
        let (extSymbolsByModule, _, extConstructors, extGlobals, extInstanceEnv, extAbbrevEnv) := processExternalDependencies deps

        -- Optionally inject prelude
        let preludeSymbols := extractPreludeSymbols extSymbolsByModule
        let graph := if preludeSymbols.isEmpty then graph
                     else injectPreludeIntoGraph preludeSymbols graph

        -- Flatten external symbols into a single SymbolEnv
        let extSymbols : SymbolEnv := extSymbolsByModule.fold (init := {}) fun acc _ env =>
          env.fold (init := acc) fun e sym ty => e.insert sym ty

        let supply := UniqueSupply.initial packageName

        let (checkDiags, checkedModules, _) := checkModulesInOrder
          sortedNames graph extGlobals extInstanceEnv extAbbrevEnv extSymbols packageName supply

        let symbols := checkedModules.foldl (init := {}) fun acc m =>
          m.publicSymbols.fold (init := acc) fun env sym val => env.insert sym val
        let instances := checkedModules.foldl (init := {}) fun acc m =>
          mergeInstanceEnvs acc m.publicInstances
        let constructors := checkedModules.foldl (init := extConstructors) fun acc m =>
          let ctors := m.constructorMetadata
          ctors.fold (init := acc) fun env n tag => env.insert n tag
        let globals := checkedModules.foldl (init := extGlobals) fun acc m =>
          mergeGlobals acc m.globals
        let instanceEnv := checkedModules.foldl (init := extInstanceEnv) fun acc m =>
          mergeInstanceEnv acc m.instanceEnv
        let abbrevEnv := checkedModules.foldl (init := extAbbrevEnv) fun acc m =>
          AbbrevEnv.merge acc m.abbrevEnv

        let allDiags := parseDiags ++ checkDiags

        if allDiags.hasErrors then
          pure (ProjectResult.failed packageName allDiags sourceMap)
        else
          pure (ProjectResult.succeeded packageName allDiags checkedModules symbols instances constructors globals instanceEnv abbrevEnv sourceMap)

/-- Check a project (file or directory) -/
def checkProject
    (config : ProjectConfig)
    (loadDeps : Array (String × System.FilePath) → IO (Except CheckError (Array ExternalDependency)))
    : IO ProjectResult := do
  if ← config.input.isDir then
    checkDirectory config loadDeps
  else if config.input.extension == some "soma" then
    checkSingleFile config loadDeps
  else
    let msg := s!"Input is neither a .soma file nor a directory: {config.input}"
    let name := config.name.getD "unknown"
    pure (ProjectResult.failed name #[Diagnostic.error msg Span.uninhabited])

/-- Parse only -/
def parseOnly (filePath : String) (content : String) : ParseResult :=
  parse filePath content

/-- Parse + lower to AST -/
def toAst (filePath : String) (content : String) (moduleName : Option String := none) : ParseResult × LowerResult :=
  let parseRes := parse filePath content
  let modName := moduleName.getD (moduleNameFromPath filePath)
  let lowerRes := lower parseRes.tree modName
  (parseRes, lowerRes)

/-- Parse + lower to Core untyped module -/
def toElaborated (filePath : String) (content : String) : ParseResult × LowerResult × ElaborationResult :=
  let (parseRes, lowerRes) := toAst filePath content
  let elabRes := elaborate lowerRes.ast
  (parseRes, lowerRes, elabRes)

end Soma.Project.Check
