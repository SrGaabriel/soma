import Somac.Build.Pipeline
import Soma.Project
import Soma.Project.Check
import Soma.Driver.Options

namespace Somac.Build.Metadata

open Soma
open Soma.Project
open Soma.Driver
open Soma.Syntax (Diagnostic Diagnostics Span)
open Soma.Typing
open Soma.Check

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

/-! ## JSON Serialization -/

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

/-- Serialize a Span to JSON -/
def spanToJson (s : Span) : Lean.Json :=
  .mkObj [
    ("fileId", .num s.start.file.id),
    ("startOffset", .num s.start.byteOffset),
    ("endOffset", .num s.stop.byteOffset),
    ("startLine", .num s.start.line),
    ("startColumn", .num s.start.column),
    ("endLine", .num s.stop.line),
    ("endColumn", .num s.stop.column)
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
    ("package", .str sym.package),
    ("span", spanToJson sym.span),
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

/-- Serialize InstanceMetadata to JSON -/
def instanceMetadataToJson (env : Project.InstanceMetadata) : Lean.Json :=
  let entries := env.fold (init := #[]) fun acc className instances =>
    let classInstances := instances.map fun (typeArgs, sym) => instanceEntryToJson typeArgs sym
    acc.push (.mkObj [("class", .str className), ("instances", .arr classInstances)])
  .arr entries

/-- Serialize constructor metadata to JSON -/
def constructorMetadataToJson (ctors : Std.HashMap Metal.Name Nat) : Lean.Json :=
  let entries := ctors.fold (init := #[]) fun acc name tag =>
    acc.push (.mkObj [("name", .str name.display), ("tag", .num tag)])
  .arr entries

/-! ## Metadata Types -/

/-- Project metadata structure for JSON output -/
structure ProjectMetadata where
  version : String := "1"
  module : String
  symbols : SymbolEnv
  instances : Project.InstanceMetadata
  constructors : Std.HashMap Metal.Name Nat

/-- Convert ProjectMetadata to JSON -/
def ProjectMetadata.toJson (pm : ProjectMetadata) : Lean.Json :=
  .mkObj [
    ("version", .str pm.version),
    ("module", .str pm.module),
    ("symbols", symbolEnvToJson pm.symbols),
    ("instances", instanceMetadataToJson pm.instances),
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

/-! ## Main Entry Point -/

/-- Generate metadata for a project (file or directory) -/
def metadata (opts : MetadataOptions) : IO MetadataResult := do
  let config : ProjectConfig := {
    input := opts.input
    name := opts.name
    deps := opts.deps.map fun (n, p) => (n, ⟨p⟩)
  }

  let result ← checkProject config Somac.Build.loadExternalDependencies

  if result.success then
    let pm : ProjectMetadata := {
      module := result.packageName
      symbols := result.symbols
      instances := result.instances
      constructors := result.constructors
    }
    pure (MetadataResult.succeeded pm)
  else
    pure (MetadataResult.failed result.diagnostics)

end Somac.Build.Metadata
