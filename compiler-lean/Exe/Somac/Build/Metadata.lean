import Somac.Build.Pipeline
import Soma.Project
import Soma.Project.Check
import Soma.Driver.Options
import Soma.Core.Value
import Soma.Core.Level
import Soma.Core.Quantity
import Soma.Core.Primitive
import Soma.Core.TypeId
import Soma.Dependent.Monad

namespace Somac.Build.Metadata

open Soma
open Soma.Project
open Soma.Driver
open Soma.Syntax (Diagnostic Diagnostics Span)
open Soma.Core
open Soma.Check
open Soma.Dependent (Globals GlobalInfo InstanceEnv InstanceInfo ClassInfo)

/-! # Metadata Generation

This module generates type-level metadata for a compiled module,
suitable for consumption by downstream compilation units without
requiring a full build. This enables fast `check` workflows similar
to `cargo check` / `rustc --emit=metadata`.

The metadata includes:
- Public symbols with their qualified types (as Core.Value)
- Type class instances
- Constructor metadata (tags and field types)
- Globals environment for dependent type checking
-/

/-! ## JSON Serialization for Core.Value -/

-- Note: Quantity, Level, LevelVarId, TypeId, Unique, and BinderInfo
-- have ToJson/FromJson instances defined in their respective modules.

/-- Serialize a StarPrimitive to JSON -/
def starPrimitiveToJson (p : StarPrimitive) : Lean.Json :=
  .str p.name

/-- Serialize a HigherPrimitive to JSON -/
def higherPrimitiveToJson (p : HigherPrimitive) : Lean.Json :=
  .str p.name

/-- Serialize a LocalPrefix to JSON -/
def localPrefixToJson : LocalPrefix → Lean.Json
  | .temp => .str "temp"
  | .block => .str "block"
  | .param => .str "param"
  | .reg => .str "reg"
  | .patternVar => .str "patternVar"
  | .closureSelf => .str "closureSelf"
  | .dictParam => .str "dictParam"
  | .refParam => .str "refParam"
  | .erasure => .str "erasure"
  | .forkedTask => .str "forkedTask"

/-- Serialize a SyntheticKind to JSON -/
def syntheticKindToJson : SyntheticKind → Lean.Json
  | .liftedLambda => .mkObj [("tag", .str "liftedLambda")]
  | .closureEnv => .mkObj [("tag", .str "closureEnv")]
  | .monomorphized typeStrs => .mkObj [
      ("tag", .str "monomorphized"),
      ("typeStrs", .arr (typeStrs.map .str))
    ]
  | .instanceMethod forTypeStr => .mkObj [
      ("tag", .str "instanceMethod"),
      ("forTypeStr", .str forTypeStr)
    ]
  | .dictParam className forTypeStr => .mkObj [
      ("tag", .str "dictParam"),
      ("className", .str className),
      ("forTypeStr", .str forTypeStr)
    ]
  | .dictGlobal className forTypeStr => .mkObj [
      ("tag", .str "dictGlobal"),
      ("className", .str className),
      ("forTypeStr", .str forTypeStr)
    ]
  | .dictStruct className => .mkObj [
      ("tag", .str "dictStruct"),
      ("className", .str className)
    ]
  | .refParam blockName => .mkObj [
      ("tag", .str "refParam"),
      ("blockName", .str blockName)
    ]
  | .erasure => .mkObj [("tag", .str "erasure")]
  | .temp => .mkObj [("tag", .str "temp")]

/-- Serialize a RuntimeFn to JSON -/
def runtimeFnToJson : RuntimeFn → Lean.Json
  | .printInt => .str "printInt"
  | .printStr => .str "printStr"
  | .panic => .str "panic"
  | .trace => .str "trace"
  | .alloc => .str "alloc"
  | .free => .str "free"

/-- Serialize a PrimOp to JSON -/
def primOpToJson : PrimOp → Lean.Json
  | .add => .str "add" | .sub => .str "sub" | .mul => .str "mul"
  | .div => .str "div" | .mod => .str "mod" | .eq => .str "eq"
  | .ne => .str "ne" | .lt => .str "lt" | .le => .str "le"
  | .gt => .str "gt" | .ge => .str "ge" | .and => .str "and"
  | .or => .str "or" | .not => .str "not" | .neg => .str "neg"

/-- Serialize an Intrinsic to JSON -/
def intrinsicToJson : Intrinsic → Lean.Json
  | .llvm name => .mkObj [("llvm", .str name)]
  | .runtime fn => .mkObj [("runtime", runtimeFnToJson fn)]
  | .primOp op => .mkObj [("primOp", primOpToJson op)]

/-- Serialize a Core.Name to JSON -/
def coreNameToJson : Core.Name → Lean.Json
  | .user u => .mkObj [("user", Lean.toJson u)]
  | .synthetic base kind disc => .mkObj [("synthetic", .mkObj [
      ("base", Lean.toJson base),
      ("kind", syntheticKindToJson kind),
      ("disc", .num disc)
    ])]
  | .intrinsic i => .mkObj [("intrinsic", intrinsicToJson i)]
  | .local_ l => .mkObj [("local", .mkObj [
      ("kind", localPrefixToJson l.kind),
      ("index", .num l.index)
    ])]
  | .projection base idx => .mkObj [("projection", .mkObj [
      ("base", coreNameToJson base),
      ("index", .num idx)
    ])]
  | .dict d => .mkObj [("dict", .mkObj [
      ("module", .str d.module),
      ("className", .str d.className),
      ("instanceTypeStr", .str d.instanceTypeStr),
      ("kind", .str (match d.kind with | .global => "global" | .struct => "struct"))
    ])]
  | .ctor u c t => .mkObj [("ctor", .mkObj [
      ("unique", Lean.toJson u),
      ("name", .str c),
      ("tag", .num t)
    ])]

/-- Serialize a BoundVar to JSON -/
def boundVarToJson (v : BoundVar) : Lean.Json :=
  .mkObj [("name", .str v.name), ("level", .num v.level.lvl)]

/-- Serialize a MetaId to JSON -/
def metaIdToJson (m : MetaId) : Lean.Json :=
  .mkObj [("id", .num m.id)]

-- Use derived instances for simple types
def levelToJson (l : Level) : Lean.Json := Lean.toJson l
def quantityToJson (q : Quantity) : Lean.Json := Lean.toJson q
def binderInfoToJson (b : Soma.Metal.BinderInfo) : Lean.Json := Lean.toJson b
def typeIdToJson (id : TypeId) : Lean.Json := Lean.toJson id

mutual

/-- Serialize a Term to JSON (for closures) -/
partial def termToJson : Term → Lean.Json
  | .var idx name => .mkObj [("var", .mkObj [("idx", .num idx), ("name", .str name)])]
  | .lit l => .mkObj [("lit", .str (toString l))]
  | .app fn args => .mkObj [("app", .mkObj [
      ("fn", termToJson fn),
      ("args", .arr (args.toArray.map termToJson))
    ])]
  | .lam names body => .mkObj [("lam", .mkObj [
      ("names", .arr (names.toArray.map Lean.Json.str)),
      ("body", termToJson body)
    ])]
  | .if_ cond then_ else_ => .mkObj [("if", .mkObj [
      ("cond", termToJson cond),
      ("then", termToJson then_),
      ("else", termToJson else_)
    ])]
  | .pair fst snd => .mkObj [("pair", .arr #[termToJson fst, termToJson snd])]
  | .fst e => .mkObj [("fst", termToJson e)]
  | .snd e => .mkObj [("snd", termToJson e)]
  | .pi qty binder name dom cod => .mkObj [("pi", .mkObj [
      ("qty", quantityToJson qty),
      ("binder", binderInfoToJson binder),
      ("name", .str name),
      ("domain", termToJson dom),
      ("codomain", termToJson cod)
    ])]
  | .sigma qty name fst snd => .mkObj [("sigma", .mkObj [
      ("qty", quantityToJson qty),
      ("name", .str name),
      ("fst", termToJson fst),
      ("snd", termToJson snd)
    ])]
  | .type level => .mkObj [("type", levelToJson level)]
  | .primTy p => .mkObj [("primTy", starPrimitiveToJson p)]
  | .higherPrimTy p => .mkObj [("higherPrimTy", higherPrimitiveToJson p)]
  | .intLit n => .mkObj [("intLit", .num n.toNat)]  -- Simplified for now
  | .stringLit s => .mkObj [("stringLit", .str s)]
  | .recordTy row => .mkObj [("recordTy", termToJson row)]
  | .variantTy row => .mkObj [("variantTy", termToJson row)]
  | .rowEmpty => .mkObj [("rowEmpty", .bool true)]
  | .rowExtend label fieldTy tail => .mkObj [("rowExtend", .mkObj [
      ("label", termToJson label),
      ("fieldTy", termToJson fieldTy),
      ("tail", termToJson tail)
    ])]
  | .labelLit name => .mkObj [("labelLit", .str name)]
  | .record fields => .mkObj [("record", .arr (fields.toArray.map fun (n, t) =>
      .mkObj [("name", .str n), ("value", termToJson t)]))]
  | .fieldAccess e field => .mkObj [("fieldAccess", .mkObj [
      ("expr", termToJson e),
      ("field", .str field)
    ])]
  | .construct name tag args => .mkObj [("construct", .mkObj [
      ("name", coreNameToJson name),
      ("tag", .num tag),
      ("args", .arr (args.toArray.map termToJson))
    ])]
  | .case scrutinee arms => .mkObj [("case", .mkObj [
      ("scrutinee", termToJson scrutinee),
      ("arms", .arr (arms.toArray.map fun (name, tag, body) =>
        .mkObj [("name", .str name), ("tag", .num tag), ("body", termToJson body)]))
    ])]
  | .global name => .mkObj [("global", coreNameToJson name)]
  | .eq tyLevel ty lhs rhs => .mkObj [("eq", .mkObj [
      ("tyLevel", levelToJson tyLevel),
      ("ty", termToJson ty),
      ("lhs", termToJson lhs),
      ("rhs", termToJson rhs)
    ])]
  | .refl ty x => .mkObj [("refl", .mkObj [("ty", termToJson ty), ("x", termToJson x)])]
  | .transport tyLevel ty motive lhs rhs eq body => .mkObj [("transport", .mkObj [
      ("tyLevel", levelToJson tyLevel),
      ("ty", termToJson ty),
      ("motive", termToJson motive),
      ("lhs", termToJson lhs),
      ("rhs", termToJson rhs),
      ("eq", termToJson eq),
      ("body", termToJson body)
    ])]
  | .mvar id => .mkObj [("mvar", .num id)]
  | .panic msg => .mkObj [("panic", .str msg)]

/-- Serialize an Env to JSON -/
partial def envToJson (env : Env) : Lean.Json :=
  .mkObj [
    ("values", .arr (env.values.toArray.map fun (name, val) =>
      .mkObj [("name", .str name), ("value", valueToJson val)])),
    ("size", .num env.size)
  ]

/-- Serialize a Closure to JSON -/
partial def closureToJson : Closure → Lean.Json
  | .term name env body => .mkObj [("term", .mkObj [
      ("name", .str name),
      ("env", envToJson env),
      ("body", termToJson body)
    ])]
  | .const name value => .mkObj [("const", .mkObj [
      ("name", .str name),
      ("value", valueToJson value)
    ])]

/-- Serialize an ArmClosure to JSON -/
partial def armClosureToJson (ac : ArmClosure) : Lean.Json :=
  .mkObj [("pattern", .str ac.pattern), ("closure", closureToJson ac.closure)]

/-- Serialize a Neutral to JSON -/
partial def neutralToJson : Neutral → Lean.Json
  | .nVar v => .mkObj [("nVar", boundVarToJson v)]
  | .nMeta id => .mkObj [("nMeta", metaIdToJson id)]
  | .nApp fn arg => .mkObj [("nApp", .mkObj [
      ("fn", neutralToJson fn),
      ("arg", valueToJson arg)
    ])]
  | .nFst pair => .mkObj [("nFst", neutralToJson pair)]
  | .nSnd pair => .mkObj [("nSnd", neutralToJson pair)]
  | .nFieldAccess record field => .mkObj [("nFieldAccess", .mkObj [
      ("record", neutralToJson record),
      ("field", .str field)
    ])]
  | .nCase scrutinee arms => .mkObj [("nCase", .mkObj [
      ("scrutinee", neutralToJson scrutinee),
      ("arms", .arr (arms.toArray.map armClosureToJson))
    ])]

/-- Serialize a Value to JSON -/
partial def valueToJson : Value → Lean.Json
  | .vType level => .mkObj [("vType", levelToJson level)]
  | .vPi qty binder name domain codomain => .mkObj [("vPi", .mkObj [
      ("qty", quantityToJson qty),
      ("binder", binderInfoToJson binder),
      ("name", .str name),
      ("domain", valueToJson domain),
      ("codomain", closureToJson codomain)
    ])]
  | .vLam qty binder name domain body => .mkObj [("vLam", .mkObj [
      ("qty", quantityToJson qty),
      ("binder", binderInfoToJson binder),
      ("name", .str name),
      ("domain", valueToJson domain),
      ("body", closureToJson body)
    ])]
  | .vSigma qty name fst snd => .mkObj [("vSigma", .mkObj [
      ("qty", quantityToJson qty),
      ("name", .str name),
      ("fst", valueToJson fst),
      ("snd", closureToJson snd)
    ])]
  | .vPair fst snd => .mkObj [("vPair", .arr #[valueToJson fst, valueToJson snd])]
  | .vNeutral ty neu => .mkObj [("vNeutral", .mkObj [
      ("ty", valueToJson ty),
      ("neutral", neutralToJson neu)
    ])]
  | .vPrimTy p => .mkObj [("vPrimTy", starPrimitiveToJson p)]
  | .vHigherPrim p => .mkObj [("vHigherPrim", higherPrimitiveToJson p)]
  | .vIntLit n => .mkObj [("vIntLit", .num n.toNat)]
  | .vStringLit s => .mkObj [("vStringLit", .str s)]
  | .vRowEmpty => .mkObj [("vRowEmpty", .bool true)]
  | .vRowExtend label fieldTy tail => .mkObj [("vRowExtend", .mkObj [
      ("label", valueToJson label),
      ("fieldTy", valueToJson fieldTy),
      ("tail", valueToJson tail)
    ])]
  | .vRecord row => .mkObj [("vRecord", valueToJson row)]
  | .vVariant row => .mkObj [("vVariant", valueToJson row)]
  | .vLabelLit name => .mkObj [("vLabelLit", .str name)]
  | .vRecordVal fields => .mkObj [("vRecordVal", .arr (fields.toArray.map fun (n, v) =>
      .mkObj [("name", .str n), ("value", valueToJson v)]))]
  | .vDataType id params => .mkObj [("vDataType", .mkObj [
      ("id", typeIdToJson id),
      ("params", .arr (params.toArray.map valueToJson))
    ])]
  | .vConstructor name tag args => .mkObj [("vConstructor", .mkObj [
      ("name", coreNameToJson name),
      ("tag", .num tag),
      ("args", .arr (args.toArray.map valueToJson))
    ])]
  | .vEq tyLevel ty lhs rhs => .mkObj [("vEq", .mkObj [
      ("tyLevel", levelToJson tyLevel),
      ("ty", valueToJson ty),
      ("lhs", valueToJson lhs),
      ("rhs", valueToJson rhs)
    ])]
  | .vRefl ty x => .mkObj [("vRefl", .mkObj [
      ("ty", valueToJson ty),
      ("x", valueToJson x)
    ])]
  | .vTransport tyLevel ty motive lhs rhs eq body => .mkObj [("vTransport", .mkObj [
      ("tyLevel", levelToJson tyLevel),
      ("ty", valueToJson ty),
      ("motive", valueToJson motive),
      ("lhs", valueToJson lhs),
      ("rhs", valueToJson rhs),
      ("eq", valueToJson eq),
      ("body", valueToJson body)
    ])]

end

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
  | .dataCon parent tag => .mkObj [("dataCon", .mkObj [("parent", .str parent), ("tag", .num tag)])]
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
def symbolEntryToJson (sym : Symbol) (val : Value) : Lean.Json :=
  .mkObj [
    ("symbol", symbolToJson sym),
    ("type", valueToJson val)
  ]

/-- Serialize SymbolEnv to JSON -/
def symbolEnvToJson (env : SymbolEnv) : Lean.Json :=
  let entries := env.fold (init := #[]) fun acc sym val =>
    acc.push (symbolEntryToJson sym val)
  .arr entries

/-- Serialize an instance entry to JSON -/
def instanceEntryToJson (typeArgs : Array Value) (sym : Symbol) : Lean.Json :=
  .mkObj [
    ("typeArgs", .arr (typeArgs.map valueToJson)),
    ("symbol", symbolToJson sym)
  ]

/-- Serialize InstanceMetadata to JSON -/
def instanceMetadataToJson (env : InstanceMetadata) : Lean.Json :=
  let entries := env.fold (init := #[]) fun acc className instances =>
    let classInstances := instances.map fun (typeArgs, sym) => instanceEntryToJson typeArgs sym
    acc.push (.mkObj [("class", .str className), ("instances", .arr classInstances)])
  .arr entries

/-- Serialize constructor metadata to JSON -/
def constructorMetadataToJson (ctors : Std.HashMap String Nat) : Lean.Json :=
  let entries := ctors.fold (init := #[]) fun acc name tag =>
    acc.push (.mkObj [("name", .str name), ("tag", .num tag)])
  .arr entries

/-- Serialize a GlobalInfo to JSON -/
def globalInfoToJson (info : GlobalInfo) : Lean.Json :=
  .mkObj [
    ("name", coreNameToJson info.name),
    ("type", valueToJson info.type),
    ("value", match info.value with
      | some v => valueToJson v
      | none => .null),
    ("isConstructor", .bool info.isConstructor),
    ("ctorTag", .num info.ctorTag)
  ]

/-- Serialize Globals to JSON -/
def globalsToJson (g : Globals) : Lean.Json :=
  let defs := g.defs.fold (init := #[]) fun acc name info =>
    acc.push (.mkObj [("name", .str name), ("info", globalInfoToJson info)])
  let typeIds := g.typeIds.fold (init := #[]) fun acc name id =>
    acc.push (.mkObj [("name", .str name), ("id", typeIdToJson id)])
  .mkObj [
    ("defs", .arr defs),
    ("typeIds", .arr typeIds)
  ]

/-- Serialize a ClassInfo to JSON -/
def classInfoToJson (info : ClassInfo) : Lean.Json :=
  .mkObj [
    ("classId", .mkObj [
      ("id", .num info.classId.id),
      ("module", .str info.classId.module),
      ("original", .str info.classId.original)
    ]),
    ("numParams", .num info.numParams),
    ("paramQuantities", .arr (info.paramQuantities.map quantityToJson)),
    ("recordType", valueToJson info.recordType),
    ("superclasses", .arr (info.superclasses.map fun (uid, idxs) =>
      .mkObj [
        ("classId", .mkObj [("id", .num uid.id), ("module", .str uid.module), ("original", .str uid.original)]),
        ("paramIndices", .arr (idxs.map Lean.toJson))
      ])),
    ("span", spanToJson info.span)
  ]

/-- Serialize an InstanceInfo to JSON -/
def instanceInfoToJson (info : InstanceInfo) : Lean.Json :=
  .mkObj [
    ("instanceId", .mkObj [
      ("id", .num info.instanceId.id),
      ("module", .str info.instanceId.module),
      ("original", .str info.instanceId.original)
    ]),
    ("classId", .mkObj [
      ("id", .num info.classId.id),
      ("module", .str info.classId.module),
      ("original", .str info.classId.original)
    ]),
    ("args", .arr (info.args.map valueToJson)),
    ("argQuantities", .arr (info.argQuantities.map quantityToJson)),
    ("constraints", .arr (info.constraints.map fun (uid, args) =>
      .mkObj [
        ("classId", .mkObj [("id", .num uid.id), ("module", .str uid.module), ("original", .str uid.original)]),
        ("args", .arr (args.map valueToJson))
      ])),
    ("value", valueToJson info.value),
    ("span", spanToJson info.span)
  ]

/-- Serialize InstanceEnv to JSON -/
def instanceEnvToJson (env : InstanceEnv) : Lean.Json :=
  let classes := env.classes.fold (init := #[]) fun acc uid info =>
    acc.push (.mkObj [
      ("classId", .mkObj [("id", .num uid.id), ("module", .str uid.module), ("original", .str uid.original)]),
      ("info", classInfoToJson info)
    ])
  let instances := env.instances.fold (init := #[]) fun acc uid insts =>
    acc.push (.mkObj [
      ("classId", .mkObj [("id", .num uid.id), ("module", .str uid.module), ("original", .str uid.original)]),
      ("instances", .arr (insts.map instanceInfoToJson))
    ])
  .mkObj [
    ("classes", .arr classes),
    ("instances", .arr instances),
    ("nextInstanceId", .num env.nextInstanceId),
    ("moduleName", .str env.moduleName)
  ]

/-! ## Metadata Types -/

/-- Project metadata structure for JSON output -/
structure ProjectMetadata where
  version : String := "2"  -- Version 2 for dependent types
  module : String
  symbols : SymbolEnv
  instances : InstanceMetadata
  constructors : Std.HashMap String Nat
  globals : Globals
  instanceEnv : InstanceEnv

/-- Convert ProjectMetadata to JSON -/
def ProjectMetadata.toJson (pm : ProjectMetadata) : Lean.Json :=
  .mkObj [
    ("version", .str pm.version),
    ("module", .str pm.module),
    ("symbols", symbolEnvToJson pm.symbols),
    ("instances", instanceMetadataToJson pm.instances),
    ("constructors", constructorMetadataToJson pm.constructors),
    ("globals", globalsToJson pm.globals),
    ("instanceEnv", instanceEnvToJson pm.instanceEnv)
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
def metadata (opts : MetadataOptions) (loadDeps : Array (String × System.FilePath) → IO (Except CheckError (Array ExternalDependency))) : IO MetadataResult := do
  let config : ProjectConfig := {
    input := opts.input
    name := opts.name
    deps := opts.deps.map fun (n, p) => (n, ⟨p⟩)
  }

  let result ← checkProject config loadDeps

  if result.success then
    let pm : ProjectMetadata := {
      module := result.packageName
      symbols := result.symbols
      instances := result.instances
      constructors := result.constructors
      globals := result.globals
      instanceEnv := result.instanceEnv
    }
    pure (MetadataResult.succeeded pm)
  else
    pure (MetadataResult.failed result.diagnostics)

end Somac.Build.Metadata
