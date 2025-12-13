import Soma.Metal.Lower.Expr
import Soma.Metal.Module
import Soma.Syntax.Ast

namespace Soma.Metal.Lower

open Soma.Typing
open Soma.Metal
open Soma.Syntax (Decl DataCon StructField DefClause)

/-- Helper to enumerate a list with indices -/
def enumWithIndex (xs : List α) : List (Nat × α) :=
  go 0 xs
where
  go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (i, x) :: go (i + 1) xs

/-- First pass: collect all global definitions into the environment.
    This allows forward references.
-/
partial def collectGlobals (decl : Decl) : LowerM Unit := do
  match decl with
  | .def_ _attrs name sig _clauses _span =>
    -- Check for duplicate definition
    let existing? ← LowerM.lookupVar LocalEnv.empty name.value
    match existing? with
    | some (.inr existingInfo) =>
      -- Report duplicate with both spans
      LowerM.reportError (.duplicateDefinition name.value name.span existingInfo.definedAt)
    | _ =>
      -- Register the function name (but don't resolve type yet)
      let globalName ← LowerM.freshUserName name.value
      -- Store raw syntax - will be resolved during lowerFunction
      LowerM.registerGlobal name.value { name := globalName, typeSyntax := sig, definedAt := name.span }

  | .data name params constructors _span =>
    -- Register the type
    let modName ← LowerM.getModuleName
    let uniqueId ← LowerM.freshUniqueId
    let typeUnique : Unique := { id := uniqueId, module := modName, original := name.value }
    let typeId : TypeId := { module := modName, name := name.value, unique := uniqueId, kind := Kind.nary params.size }
    let tyCon := TyCon.user typeId
    let tyVarIds := params.mapIdx fun idx p => TyVarId.mk p.value idx .star
    let kind := Kind.nary params.size
    LowerM.registerType name.value { tyCon := tyCon, params := tyVarIds, kind := kind, unique := typeUnique }

    -- Register constructors
    let ctorList := enumWithIndex constructors.toList
    for (i, ctor) in ctorList do
      let ctorName := LowerM.mkCtorName typeUnique ctor.name.value i
      -- Resolve field types (best effort - may fail if types not yet registered)
      let fields ← ctor.fields.mapM fun (_, tyExpr) => do
        let ty? ← resolveType tyExpr
        pure (ty?.getD Ty.unit)
      LowerM.registerConstructor ctor.name.value
        { name := ctorName, parentType := name.value, parentUnique := typeUnique, tag := i, fields := fields }

  | .struct name params ctorName fields _span =>
    -- Register the type
    let modName ← LowerM.getModuleName
    let uniqueId ← LowerM.freshUniqueId
    let typeUnique : Unique := { id := uniqueId, module := modName, original := name.value }
    let typeId : TypeId := { module := modName, name := name.value, unique := uniqueId, kind := Kind.nary params.size }
    let tyCon := TyCon.user typeId
    let tyVarIds := params.mapIdx fun idx p => TyVarId.mk p.value idx .star
    let kind := Kind.nary params.size
    LowerM.registerType name.value { tyCon := tyCon, params := tyVarIds, kind := kind, unique := typeUnique }

    -- Register the constructor
    let ctorMetalName := LowerM.mkCtorName typeUnique ctorName.value 0
    let fieldTys ← fields.mapM fun field => do
      let ty? ← resolveType field.type_
      pure (ty?.getD Ty.unit)
    LowerM.registerConstructor ctorName.value
      { name := ctorMetalName, parentType := name.value, parentUnique := typeUnique, tag := 0, fields := fieldTys }

  | .trait name _params _constraints methods _span =>
    -- Register the type class
    let modName ← LowerM.getModuleName
    let uniqueId ← LowerM.freshUniqueId
    let typeUnique : Unique := { id := uniqueId, module := modName, original := name.value }
    let typeId : TypeId := { module := modName, name := name.value, unique := uniqueId, kind := .star }
    let tyCon := TyCon.user typeId
    let globalName ← LowerM.freshUserName name.value

    let methodSigs ← methods.mapM fun m => do
      let ty? ← resolveQualifiedType m.type_
      pure (m.name.value, ty?.getD (QualifiedType.mono Ty.unit))

    LowerM.registerTypeClass name.value
      { name := globalName, tyCon := tyCon, methods := methodSigs, unique := typeUnique }

  | .instance_ _traitName _args _constraints _methods _ =>
    -- Instances are handled in a separate pass
    pure ()

  | .use _path _items _ =>
    -- Imports are handled by the driver
    pure ()

  | .export_ _items _ =>
    -- Exports are handled by the driver
    pure ()

  | .intrinsic inner _ =>
    -- Intrinsics - collect the inner declaration
    collectGlobals inner

/-- Collect globals from all declarations -/
def collectAllGlobals (decls : Array Decl) : LowerM Unit := do
  for decl in decls do
    collectGlobals decl

/-- Theorem: buildParamList preserves binding structure -/
theorem buildParamList_bindingIds_eq (bindings : List (BindingId × String)) :
    (buildParamList bindings).bindingIds = bindings.map Prod.fst := by
  induction bindings with
  | nil => rfl
  | cons hd tl ih => simp only [buildParamList, ParamList.bindingIds, List.map, ih]

/-- Theorem: bindingIds ++ [] = bindingIds -/
theorem bindingIds_append_nil (paramList : ParamList Unit) :
    paramList.bindingIds ++ [] = paramList.bindingIds := by
  simp

/-- Cast expression to equivalent scope -/
def castExprScope (h : s1 = s2) (e : Expr α s1) : Expr α s2 := h ▸ e

/-- Lower a function definition to an UntypedFunction -/
def lowerFunction (decl : Decl) : LowerM (Option UntypedFunction) := do
  match decl with
  | .def_ attrs name sig clauses _span =>
    -- TODO: Multi-clause functions
    if h : clauses.size > 0 then
      let clause := clauses[0]

      -- Get the function's registered name
      let globalInfo? ← LowerM.lookupVar LocalEnv.empty name.value
      let globalName ← match globalInfo? with
        | some (.inr info) => pure info.name
        | _ => LowerM.freshUserName name.value  -- Fallback: create a fresh name

      -- Build params from clause patterns (just binding + name, no types yet)
      let params ← clause.patterns.mapM fun pat => do
        let paramName := match pat with
          | .var n => n.value
          | _ => "_"
        let bindingId ← LowerM.freshParamId paramName
        pure (bindingId, paramName)

      -- Build ParamList for the lambda body (we need it for scope calculation)
      let paramList := buildParamList params.toList

      -- Extend environment with params
      let localEnv := extendEnvWithParams LocalEnv.empty paramList

      -- Lower the body in the paramList scope
      let bodyRaw ← lowerExpr localEnv clause.body
      -- bodyRaw : Expr Unit (paramList.bindingIds ++ [])
      -- We need: Expr Unit (params.toList.map Prod.fst)
      -- Use the theorem to cast
      let body : UntypedExpr (params.toList.map Prod.fst) :=
        castExprScope (by rw [List.append_nil, buildParamList_bindingIds_eq]) bodyRaw

      -- Build function attributes
      let funcAttrs : FunctionAttrs := {
        inline := attrs.any fun a => a.name.value == "inline"
        noInline := attrs.any fun a => a.name.value == "noinline"
        deprecated := none
        extern := none
      }

      -- Store raw type syntax - resolution happens during type inference
      pure (some {
        name := globalName
        params := params
        body := body
        declaredTypeSyntax := sig
        closureInfo := none
        attrs := funcAttrs
      })

    else
      -- No clauses - empty function?
      pure none

  | _ => pure none

/-- Lower a type definition to an UntypedTypeDef -/
def lowerTypeDef (decl : Decl) : LowerM (Option UntypedTypeDef) := do
  match decl with
  | .data name _params constructors _ =>
    let typeUnique ← LowerM.freshUnique name.value
    let typeName := Name.user typeUnique
    let typeVarNames := _params.map (·.value)

    -- Build untyped constructors with field type syntax preserved
    let ctorList := enumWithIndex constructors.toList
    let ctors ← ctorList.toArray.mapM fun (i, ctor) => do
      let ctorName := Name.ctor typeUnique ctor.name.value i
      -- Extract TypeExpr from each field (ignoring optional field names)
      let fieldTypes := ctor.fields.map (·.2)
      pure { name := ctorName, tag := i, fieldTypeSyntax := fieldTypes : UntypedConstructor }

    pure (some (.algebraic typeName typeVarNames ctors))

  | .struct name _params ctorName fields _ =>
    let typeUnique ← LowerM.freshUnique name.value
    let typeName := Name.user typeUnique
    let typeVarNames := _params.map (·.value)
    let ctorMetalName := Name.ctor typeUnique ctorName.value 0
    -- Extract TypeExpr from each field
    let fieldTypes := fields.map (·.type_)

    pure (some (.struct typeName typeVarNames ctorMetalName fieldTypes))

  | _ => pure none

/-- Lower an instance declaration to an UntypedInstance -/
def lowerInstance (decl : Decl) : LowerM (Option UntypedInstance) := do
  match decl with
  | .instance_ traitName args constraints methods span =>
    -- Lower each method as a function
    let methodFunctions ← methods.filterMapM lowerFunction

    pure (some {
      className := traitName.value
      typeArgsSyntax := args
      constraintsSyntax := constraints
      methods := methodFunctions
      span := span
    })
  | _ => pure none

/-- Lower all declarations to an UntypedModule -/
def lowerModule (moduleName : String) (decls : Array Decl) : LowerM UntypedModule := do
  -- First pass: collect all globals
  collectAllGlobals decls

  -- Second pass: lower functions
  let functions ← decls.filterMapM lowerFunction

  -- Third pass: lower type definitions
  let types ← decls.filterMapM lowerTypeDef

  -- Fourth pass: lower instances
  let instances ← decls.filterMapM lowerInstance

  pure {
    name := moduleName
    functions := functions
    types := types
    instances := instances
    typeClasses := #[]
  }

end Soma.Metal.Lower
