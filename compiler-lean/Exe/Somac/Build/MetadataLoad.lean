import Lean.Data.Json
import Soma.Project
import Soma.Project.Check
import Soma.Typing
import Soma.Unique

namespace Somac.Build.MetadataLoad

open Soma
open Soma.Project
open Soma.Syntax (Span)
open Soma.Typing
open Soma.Check (ExternalDependency CheckError)

/-! # Metadata JSON Loading

Parse metadata JSON back into compiler types for dependency loading.
This module is separate to avoid import cycles.
-/

/-- Parse a Kind from JSON -/
partial def kindFromJson (j : Lean.Json) : Except String Kind := do
  match j with
  | .str "*" => pure .star
  | .obj obj =>
    match obj.get? "arrow" with
    | some (.arr arr) =>
      if arr.size = 2 then
        let k1' ← kindFromJson arr[0]!
        let k2' ← kindFromJson arr[1]!
        pure (.arrow k1' k2')
      else .error "Invalid kind arrow: expected 2 elements"
    | _ => .error "Invalid kind JSON"
  | _ => .error "Invalid kind JSON"

/-- Parse a TypeId from JSON -/
def typeIdFromJson (j : Lean.Json) : Except String TypeId := do
  let name ← j.getObjValAs? String "name"
  let module ← j.getObjValAs? String "module"
  let unique ← j.getObjValAs? Nat "unique"
  let kind := match j.getObjVal? "kind" with
    | .ok k => (kindFromJson k).toOption.getD .star
    | .error _ => .star
  pure { name, module, unique, kind }

/-- Parse a TyVarId from JSON -/
def tyVarIdFromJson (j : Lean.Json) : Except String TyVarId := do
  let name ← j.getObjValAs? String "name"
  let id ← j.getObjValAs? Nat "id"
  let kind := match j.getObjVal? "kind" with
    | .ok k => (kindFromJson k).toOption.getD .star
    | .error _ => .star
  pure { name, id, kind }

/-- Parse a type of a given kind from JSON.
    This is the core parsing function that handles types of any kind,
    using the expected kind to guide parsing of type applications. -/
partial def tyFromJsonWithKind (k : Kind) (j : Lean.Json) : Except String (Ty k) := do
  match j with
  | .obj obj =>
    -- Variable case: create var with the expected kind
    if let some varObj := obj.get? "var" then
      let name ← varObj.getObjValAs? String "name"
      let id ← varObj.getObjValAs? Nat "id"
      pure (.var { name, id, kind := k })

    -- Star primitive (only valid for kind *)
    else if let some (.str primName) := obj.get? "prim" then
      match k with
      | .star =>
        match StarPrimitive.fromName? primName with
        | some p => pure (.starPrim p)
        | none => .error s!"Unknown primitive type: {primName}"
      | _ => .error s!"Primitive {primName} has kind *, but expected kind {k}"

    -- Higher primitive (only valid for kind * -> *)
    else if let some (.str hpName) := obj.get? "higherPrim" then
      match k with
      | .arrow .star .star =>
        match HigherPrimitive.fromName? hpName with
        | some p => pure (.higherPrim p)
        | none => .error s!"Unknown higher primitive: {hpName}"
      | .star =>
        -- Standalone higherPrim at kind * is a placeholder (will be wrapped in app)
        match HigherPrimitive.fromName? hpName with
        | some p => pure (.app (.higherPrim p) (.starPrim .unit))
        | none => .error s!"Unknown higher primitive: {hpName}"
      | _ => .error s!"Higher primitive {hpName} has kind * -> *, but expected kind {k}"

    -- User type constructor
    else if let some conObj := obj.get? "con" then
      let typeId ← typeIdFromJson conObj
      -- The typeId includes the kind from JSON serialization
      -- We trust it matches k (type system ensures this at serialization time)
      pure (.userCon k typeId)

    -- Arrow type (only valid for kind *)
    else if let some (.arr arr) := obj.get? "arrow" then
      match k with
      | .star =>
        if arr.size = 2 then
          let from' ← tyFromJsonWithKind .star arr[0]!
          let to' ← tyFromJsonWithKind .star arr[1]!
          pure (.arrow from' to')
        else .error "Invalid arrow type: expected 2 elements"
      | _ => .error s!"Arrow types have kind *, but expected kind {k}"

    -- Type application
    else if let some (.arr arr) := obj.get? "app" then
      if arr.size = 2 then
        -- If result kind is k, then f has kind (* -> k) and arg has kind *
        -- We only support * as argument kinds (no higher-kinded arguments like Functor f)
        let fnKind : Kind := .arrow .star k
        let f' ← tyFromJsonWithKind fnKind arr[0]!
        let a' ← tyFromJsonWithKind .star arr[1]!
        pure (.app f' a')
      else .error "Invalid app type: expected 2 elements"

    -- Tuple (only valid for kind *)
    else if let some (.arr elems) := obj.get? "tuple" then
      match k with
      | .star =>
        let elemTys ← elems.toList.mapM (tyFromJsonWithKind .star)
        pure (Ty.mkTuple elemTys.toArray)
      | _ => .error s!"Tuple types have kind *, but expected kind {k}"

    else .error s!"Unknown type JSON for kind {k}: {j}"
  | _ => .error s!"Invalid type JSON: {j}"

/-- Parse a MonoTy (kind *) from JSON -/
def tyFromJson (j : Lean.Json) : Except String MonoTy :=
  tyFromJsonWithKind .star j

/-- Parse a higher-kinded type (kind * -> *) from JSON -/
def tyFromJsonHK (j : Lean.Json) : Except String (Ty (.arrow Kind.star Kind.star)) :=
  tyFromJsonWithKind (.arrow .star .star) j

/-- Parse a TyCon from JSON -/
def tyConFromJson (j : Lean.Json) : Except String TyCon := do
  match j with
  | .obj obj =>
    if let some (.str primName) := obj.get? "prim" then
      match Primitive.fromName? primName with
      | some p => pure (.prim p)
      | none => .error s!"Unknown primitive: {primName}"
    else if let some userObj := obj.get? "user" then
      let typeId ← typeIdFromJson userObj
      pure (.user typeId)
    else
      .error s!"Invalid TyCon JSON: {j}"
  | _ => .error s!"Invalid TyCon JSON: {j}"

/-- Parse a Constraint from JSON -/
def constraintFromJson (j : Lean.Json) : Except String Constraint := do
  let classJ ← j.getObjVal? "class"
  let className ← tyConFromJson classJ
  let argsJ ← j.getObjValAs? (Array Lean.Json) "args"
  let args ← argsJ.toList.mapM tyFromJson
  pure { className, args := args.toArray }

/-- Parse a QualifiedType from JSON -/
def qualTypeFromJson (j : Lean.Json) : Except String QualifiedType := do
  let varsJ ← j.getObjValAs? (Array Lean.Json) "vars"
  let vars ← varsJ.toList.mapM tyVarIdFromJson
  let constraintsJ ← j.getObjValAs? (Array Lean.Json) "constraints"
  let constraints ← constraintsJ.toList.mapM constraintFromJson
  let bodyJ ← j.getObjVal? "body"
  let body ← tyFromJson bodyJ
  pure { vars := vars.toArray, constraints := constraints.toArray, body }

/-- Parse a SymbolKind from JSON -/
def symbolKindFromJson (j : Lean.Json) : Except String SymbolKind := do
  match j with
  | .str "binding" => pure .binding
  | .str "type" => pure .type
  | .str "typeClass" => pure .typeClass
  | .str "letBinding" => pure .letBinding
  | .str "lambdaParam" => pure .lambdaParam
  | .str "patternVar" => pure .patternVar
  | .str "patternAs" => pure .patternAs
  | .str "composeBinding" => pure .composeBinding
  | .str "intrinsicBinding" => pure .intrinsicBinding
  | .str "intrinsicType" => pure .intrinsicType
  | .obj obj =>
    if let some dataConObj := obj.get? "dataCon" then
      let parent ← dataConObj.getObjValAs? String "parent"
      let tag ← dataConObj.getObjValAs? Nat "tag"
      pure (.dataCon parent tag)
    else if let some (.str cls) := obj.get? "typeClassMethod" then
      pure (.typeClassMethod cls)
    else if let some instObj := obj.get? "instanceMethod" then
      let inst ← instObj.getObjValAs? String "instance"
      let cls ← instObj.getObjValAs? String "class"
      pure (.instanceMethod inst cls)
    else
      .error s!"Unknown symbol kind: {j}"
  | _ => .error s!"Invalid symbol kind JSON: {j}"

/-- Parse a Unique from JSON -/
def uniqueFromJson (j : Lean.Json) : Except String Unique := do
  let id ← j.getObjValAs? Nat "id"
  let module ← j.getObjValAs? String "module"
  let original ← j.getObjValAs? String "original"
  pure { id, module, original }

/-- Parse a Span from JSON -/
def spanFromJson (j : Lean.Json) : Except String Span := do
  let fileId ← j.getObjValAs? Nat "fileId"
  let startOffset ← j.getObjValAs? Nat "startOffset"
  let endOffset ← j.getObjValAs? Nat "endOffset"
  let startLine ← j.getObjValAs? Nat "startLine"
  let startColumn ← j.getObjValAs? Nat "startColumn"
  let endLine ← j.getObjValAs? Nat "endLine"
  let endColumn ← j.getObjValAs? Nat "endColumn"
  pure {
    start := { file := ⟨fileId⟩, byteOffset := startOffset, line := startLine, column := startColumn }
    stop := { file := ⟨fileId⟩, byteOffset := endOffset, line := endLine, column := endColumn }
  }

/-- Parse a Symbol from JSON -/
def symbolFromJson (j : Lean.Json) : Except String Symbol := do
  let name ← j.getObjValAs? String "name"
  let kindJ ← j.getObjVal? "kind"
  let kind ← symbolKindFromJson kindJ
  let module ← j.getObjValAs? String "module"
  let package ← j.getObjValAs? String "package"
  let spanJ ← j.getObjVal? "span"
  let span ← spanFromJson spanJ
  let uniqueJ ← j.getObjVal? "unique"
  let unique ← uniqueFromJson uniqueJ
  pure { unique, name, kind, module, package, span }

/-- Parse a symbol entry (symbol + type) from JSON -/
def symbolEntryFromJson (j : Lean.Json) : Except String (Symbol × QualifiedType) := do
  let symJ ← j.getObjVal? "symbol"
  let sym ← symbolFromJson symJ
  let typeJ ← j.getObjVal? "type"
  let qt ← qualTypeFromJson typeJ
  pure (sym, qt)

/-- Parse SymbolEnv from JSON array -/
def symbolEnvFromJson (j : Lean.Json) : Except String SymbolEnv := do
  match j with
  | .arr entries =>
    let pairs ← entries.toList.mapM symbolEntryFromJson
    pure (pairs.foldl (fun env (sym, qt) => env.insert sym qt) {})
  | _ => .error "Expected array for symbols"

/-- Parse an instance entry from JSON -/
def instanceEntryFromJson (j : Lean.Json) : Except String (Array MonoTy × Symbol) := do
  let typeArgsJ ← j.getObjValAs? (Array Lean.Json) "typeArgs"
  let typeArgs ← typeArgsJ.toList.mapM tyFromJson
  let symJ ← j.getObjVal? "symbol"
  let sym ← symbolFromJson symJ
  pure (typeArgs.toArray, sym)

/-- Parse InstanceMetadata from JSON array -/
def instanceMetadataFromJson (j : Lean.Json) : Except String Project.InstanceMetadata := do
  match j with
  | .arr entries =>
    let mut env : Project.InstanceMetadata := {}
    for entry in entries do
      let className ← entry.getObjValAs? String "class"
      let instancesJ ← entry.getObjValAs? (Array Lean.Json) "instances"
      let instances ← instancesJ.toList.mapM instanceEntryFromJson
      env := env.insert className instances.toArray
    pure env
  | _ => .error "Expected array for instances"

/-- Parse constructor metadata from JSON array -/
def constructorMetadataFromJson (j : Lean.Json) : Except String (Std.HashMap String Nat) := do
  match j with
  | .arr entries =>
    let mut ctors : Std.HashMap String Nat := {}
    for entry in entries do
      let name ← entry.getObjValAs? String "name"
      let tag ← entry.getObjValAs? Nat "tag"
      ctors := ctors.insert name tag
    pure ctors
  | _ => .error "Expected array for constructors"

/-- Load metadata from a JSON file -/
def loadMetadataFromFile (path : System.FilePath) : IO (Except String ExternalDependency) := do
  let content ← IO.FS.readFile path
  match Lean.Json.parse content with
  | .error e => pure (.error s!"Failed to parse JSON: {e}")
  | .ok json => do
    let result := do
      let version ← json.getObjValAs? String "version"
      if version != "1" then
        .error s!"Unsupported metadata version: {version}"
      else
        let moduleName ← json.getObjValAs? String "module"
        let symbolsJ ← json.getObjVal? "symbols"
        let symbols ← symbolEnvFromJson symbolsJ
        let instancesJ ← json.getObjVal? "instances"
        let instances ← instanceMetadataFromJson instancesJ
        let constructorsJ ← json.getObjVal? "constructors"
        let constructors ← constructorMetadataFromJson constructorsJ
        pure {
          name := moduleName
          version := some version
          symbols := ({} : Std.HashMap String SymbolEnv).insert moduleName symbols
          instances := ({} : Std.HashMap String Project.InstanceMetadata).insert moduleName instances
          constructors := constructors
        }
    pure result

/-- Load multiple metadata files as external dependencies -/
def loadMetadataFiles (deps : Array (String × System.FilePath)) : IO (Except CheckError (Array ExternalDependency)) := do
  let mut results : Array ExternalDependency := #[]
  for (name, path) in deps do
    match ← loadMetadataFromFile path with
    | .ok dep => results := results.push dep
    | .error e => return .error (.dependencyLoadError name e)
  pure (.ok results)

end Somac.Build.MetadataLoad
