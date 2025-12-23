import Somac.Build.Pipeline
import Somac.Build.Compiled
import Somac.Build.Driver
import Soma.Project
import Soma.Driver.Options
import Soma.Logging
import Soma.Unique

namespace Somac.Build.Metadata

open Soma
open Soma.Project
open Soma.Driver
open Soma.Logging
open Soma.Syntax (Diagnostic Diagnostics Span)
open Soma.Typing
open Soma (UniqueSupply)

/-! # Metadata Generation

This module generates type-level metadata for a compiled module,
suitable for consumption by downstream compilation units without
requiring a full build. This enables fast `check` workflows similar
to `cargo check` / `rustc --emit=metadata`.

The metadata includes:
- Public symbols with their qualified types
- Type class instances
- Constructor metadata (tags and field types)
-/

/-- Serialize a Kind to JSON -/
def kindToJson : Kind → Lean.Json
  | .star => .str "*"
  | .arrow k1 k2 => .mkObj [("arrow", .arr #[kindToJson k1, kindToJson k2])]

/-- Serialize a TypeId to JSON -/
def typeIdToJson (id : TypeId) : Lean.Json :=
  .mkObj [("name", .str id.name), ("module", .str id.module), ("unique", .num id.unique)]

/-- Serialize higher-kinded types to JSON -/
partial def tyToJsonHK : {k : Kind} → Ty k → Lean.Json
  | _, .var v => .mkObj [("var", .mkObj [("name", .str v.name), ("id", .num v.id)])]
  | _, .starPrim p => .mkObj [("prim", .str p.name)]
  | _, .higherPrim p => .mkObj [("higherPrim", .str p.name)]
  | k, .userCon _ id => .mkObj [("con", .mkObj [("name", .str id.name), ("module", .str id.module), ("unique", .num id.unique), ("kind", kindToJson k)])]
  | _, .app f a => .mkObj [("app", .arr #[tyToJsonHK f, tyToJsonHK a])]
  | _, .arrow from_ to => .mkObj [("arrow", .arr #[tyToJsonHK from_, tyToJsonHK to])]
  | _, .tuple2 a b => .mkObj [("tuple", .arr #[tyToJsonHK a, tyToJsonHK b])]
  | _, .tuple3 a b c => .mkObj [("tuple", .arr #[tyToJsonHK a, tyToJsonHK b, tyToJsonHK c])]
  | _, .tuple4 a b c d => .mkObj [("tuple", .arr #[tyToJsonHK a, tyToJsonHK b, tyToJsonHK c, tyToJsonHK d])]
  | _, .tuple5 a b c d e => .mkObj [("tuple", .arr #[tyToJsonHK a, tyToJsonHK b, tyToJsonHK c, tyToJsonHK d, tyToJsonHK e])]
  | _, .tuple6 a b c d e f => .mkObj [("tuple", .arr #[tyToJsonHK a, tyToJsonHK b, tyToJsonHK c, tyToJsonHK d, tyToJsonHK e, tyToJsonHK f])]
  | _, .tuple7 a b c d e f g => .mkObj [("tuple", .arr #[tyToJsonHK a, tyToJsonHK b, tyToJsonHK c, tyToJsonHK d, tyToJsonHK e, tyToJsonHK f, tyToJsonHK g])]
  | _, .tuple8 a b c d e f g h => .mkObj [("tuple", .arr #[tyToJsonHK a, tyToJsonHK b, tyToJsonHK c, tyToJsonHK d, tyToJsonHK e, tyToJsonHK f, tyToJsonHK g, tyToJsonHK h])]

/-- Serialize a MonoTy to JSON -/
def tyToJson (t : MonoTy) : Lean.Json := tyToJsonHK t

/-- Serialize a TyVarId to JSON -/
def tyVarIdToJson (v : TyVarId) : Lean.Json :=
  .mkObj [("name", .str v.name), ("id", .num v.id), ("kind", kindToJson v.kind)]

/-- Serialize a TyCon to JSON -/
def tyConToJson : TyCon → Lean.Json
  | .prim p => .mkObj [("prim", .str p.name)]
  | .user id => .mkObj [("user", typeIdToJson id)]

/-- Serialize a Constraint to JSON -/
def constraintToJson (c : Constraint) : Lean.Json :=
  .mkObj [
    ("class", tyConToJson c.className),
    ("args", .arr (c.args.map tyToJson))
  ]

/-- Serialize a QualifiedType to JSON -/
def qualTypeToJson (qt : QualifiedType) : Lean.Json :=
  .mkObj [
    ("vars", .arr (qt.vars.map tyVarIdToJson)),
    ("constraints", .arr (qt.constraints.map constraintToJson)),
    ("body", tyToJson qt.body)
  ]

/-- Serialize a SymbolKind to JSON -/
def symbolKindToJson : SymbolKind → Lean.Json
  | .binding => .str "binding"
  | .dataCon parent => .mkObj [("dataCon", .str parent)]
  | .type => .str "type"
  | .typeClass => .str "typeClass"
  | .typeClassMethod cls => .mkObj [("typeClassMethod", .str cls)]
  | .instanceMethod inst cls => .mkObj [("instanceMethod", .mkObj [("instance", .str inst), ("class", .str cls)])]
  | .letBinding => .str "letBinding"
  | .lambdaParam => .str "lambdaParam"
  | .patternVar => .str "patternVar"
  | .patternAs => .str "patternAs"
  | .composeBinding => .str "composeBinding"
  | .intrinsicBinding => .str "intrinsicBinding"
  | .intrinsicType => .str "intrinsicType"

/-- Serialize a Symbol to JSON -/
def symbolToJson (sym : Symbol) : Lean.Json :=
  .mkObj [
    ("name", .str sym.name),
    ("kind", symbolKindToJson sym.kind),
    ("module", .str sym.module),
    ("unique", .mkObj [
      ("id", .num sym.unique.id),
      ("module", .str sym.unique.module),
      ("original", .str sym.unique.original)
    ])
  ]

/-- Serialize a symbol with its type to JSON -/
def symbolEntryToJson (sym : Symbol) (qt : QualifiedType) : Lean.Json :=
  .mkObj [
    ("symbol", symbolToJson sym),
    ("type", qualTypeToJson qt)
  ]

/-- Serialize SymbolEnv to JSON -/
def symbolEnvToJson (env : SymbolEnv) : Lean.Json :=
  let entries := env.fold (init := #[]) fun acc sym qt =>
    acc.push (symbolEntryToJson sym qt)
  .arr entries

/-- Serialize an instance entry to JSON -/
def instanceEntryToJson (typeArgs : Array MonoTy) (sym : Symbol) : Lean.Json :=
  .mkObj [
    ("typeArgs", .arr (typeArgs.map tyToJson)),
    ("symbol", symbolToJson sym)
  ]

/-- Serialize InstanceEnv to JSON -/
def instanceEnvToJson (env : InstanceEnv) : Lean.Json :=
  let entries := env.fold (init := #[]) fun acc className instances =>
    let classInstances := instances.map fun (typeArgs, sym) => instanceEntryToJson typeArgs sym
    acc.push (.mkObj [("class", .str className), ("instances", .arr classInstances)])
  .arr entries

/-- Serialize constructor metadata to JSON -/
def constructorMetadataToJson (ctors : Std.HashMap Metal.Name Nat) : Lean.Json :=
  let entries := ctors.fold (init := #[]) fun acc name tag =>
    acc.push (.mkObj [("name", .str name.display), ("tag", .num tag)])
  .arr entries

/-- Project metadata structure for JSON output -/
structure ProjectMetadata where
  version : String := "1"
  module : String
  symbols : SymbolEnv
  instances : InstanceEnv
  constructors : Std.HashMap Metal.Name Nat

/-- Convert ProjectMetadata to JSON -/
def ProjectMetadata.toJson (pm : ProjectMetadata) : Lean.Json :=
  .mkObj [
    ("version", .str pm.version),
    ("module", .str pm.module),
    ("symbols", symbolEnvToJson pm.symbols),
    ("instances", instanceEnvToJson pm.instances),
    ("constructors", constructorMetadataToJson pm.constructors)
  ]

/-- Result of metadata generation -/
structure MetadataResult where
  success : Bool
  diagnostics : Array Diagnostic
  metadata : Option ProjectMetadata

namespace MetadataResult

def failed (diags : Array Diagnostic) : MetadataResult :=
  { success := false, diagnostics := diags, metadata := none }

def succeeded (pm : ProjectMetadata) : MetadataResult :=
  { success := true, diagnostics := #[], metadata := some pm }

end MetadataResult

/-- Generate metadata for a single .soma file -/
def metadataSingleFile (opts : MetadataOptions) : IO MetadataResult := do
  let path : System.FilePath := opts.input
  let name := opts.name.getD (path.fileStem.getD "Main")

  -- Parse the module
  match ← parseModule name path with
  | .error diags =>
    pure (MetadataResult.failed diags)

  | .ok info =>
    let graph : ModuleGraph := ({} : ModuleGraph).insert name info
    let depGraph := buildDependencyGraph graph

    -- Check for cycles
    match topoSortModules depGraph with
    | .cycles groups =>
      let msg := s!"Cyclic imports detected: {groups.map (·.toList)}"
      pure (MetadataResult.failed #[Diagnostic.error msg Span.uninhabited])

    | .sorted sortedNames =>
      -- Load external dependencies
      let externalDeps ← loadExternalDependencies (opts.deps.map fun (n, p) => (n, ⟨p⟩))
      match externalDeps with
      | .error e =>
        pure (MetadataResult.failed #[Diagnostic.error (toString e) Span.uninhabited])

      | .ok deps =>
        let (extSymbols, extInstances, extConstructors) := processExternalDependencies deps

        -- Initialize UniqueSupply
        let supply := UniqueSupply.initial name

        -- Compile (type check only)
        let (compileDiags, compiledModules, _) := compileModulesInOrder sortedNames graph extSymbols extInstances extConstructors name supply

        if Diagnostics.hasErrors compileDiags then
          pure (MetadataResult.failed compileDiags)
        else
          -- Extract metadata from compiled modules
          let pm : ProjectMetadata := {
            module := name
            symbols := compiledModules.foldl (init := {}) fun acc m =>
              m.publicSymbols.fold (init := acc) fun env sym qt => env.insert sym qt
            instances := compiledModules.foldl (init := {}) fun acc m =>
              mergeInstanceEnvs acc m.publicInstances
            constructors := compiledModules.foldl (init := {}) fun acc m =>
              m.constructorMetadata.fold (init := acc) fun env name tag => env.insert name tag
          }
          pure (MetadataResult.succeeded pm)

/-- Generate metadata for a project directory -/
def metadataDirectory (opts : MetadataOptions) : IO MetadataResult := do
  let rootDir : System.FilePath := opts.input
  let packageName := opts.name.getD (rootDir.fileName.getD "app")

  -- Find all modules
  let modules ← findModules packageName rootDir

  -- Parse all modules
  match ← parseModules modules with
  | (#[], graph) =>
    let depGraph := buildDependencyGraph graph

    -- Topological sort
    match topoSortModules depGraph with
    | .cycles groups =>
      let msg := s!"Cyclic imports: {groups.map (·.toList)}"
      pure (MetadataResult.failed #[Diagnostic.error msg Span.uninhabited])

    | .sorted sortedNames =>
      -- Load external dependencies
      let externalDeps ← loadExternalDependencies (opts.deps.map fun (n, p) => (n, ⟨p⟩))
      match externalDeps with
      | .error e =>
        pure (MetadataResult.failed #[Diagnostic.error (toString e) Span.uninhabited])

      | .ok deps =>
        let (extSymbols, extInstances, extConstructors) := processExternalDependencies deps

        -- Optionally inject prelude
        let preludeSymbols := extractPreludeSymbols extSymbols
        let graph := if preludeSymbols.isEmpty then graph
                     else injectPreludeIntoGraph preludeSymbols graph

        -- Initialize UniqueSupply
        let supply := UniqueSupply.initial packageName

        -- Compile all modules (type check only)
        let (compileDiags, compiledModules, _) := compileModulesInOrder sortedNames graph extSymbols extInstances extConstructors packageName supply

        if Diagnostics.hasErrors compileDiags then
          pure (MetadataResult.failed compileDiags)
        else
          -- Extract metadata
          let pm : ProjectMetadata := {
            module := packageName
            symbols := compiledModules.foldl (init := {}) fun acc m =>
              m.publicSymbols.fold (init := acc) fun env sym qt => env.insert sym qt
            instances := compiledModules.foldl (init := {}) fun acc m =>
              mergeInstanceEnvs acc m.publicInstances
            constructors := compiledModules.foldl (init := {}) fun acc m =>
              m.constructorMetadata.fold (init := acc) fun env name tag => env.insert name tag
          }
          pure (MetadataResult.succeeded pm)

  | (diags, _) =>
    pure (MetadataResult.failed diags)

/-- Main metadata entry point -/
def metadata (opts : MetadataOptions) : IO MetadataResult := do
  let inputPath : System.FilePath := opts.input

  if ← inputPath.isDir then
    metadataDirectory opts
  else if inputPath.extension == some "soma" then
    metadataSingleFile opts
  else
    let msg := s!"Input is neither a .soma file nor a directory: {opts.input}"
    pure (MetadataResult.failed #[Diagnostic.error msg Span.uninhabited])

end Somac.Build.Metadata
