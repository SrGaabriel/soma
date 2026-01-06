import Soma.Metal.Lower.Expr
import Soma.Metal.Module
import Soma.Syntax.Ast

namespace Soma.Metal.Lower

open Soma.Core (TypeId Name)
open Soma.Metal
open Soma.Syntax (Decl DataCon StructField DefClause)

/-- Check if a character is uppercase ASCII letter -/
private def isUpperAscii (c : Char) : Bool :=
  c.toNat >= 65 && c.toNat <= 90  -- 'A' to 'Z'

/-- Check if a character is lowercase ASCII letter -/
private def isLowerAscii (c : Char) : Bool :=
  c.toNat >= 97 && c.toNat <= 122  -- 'a' to 'z'

/-- Check if a character is a digit -/
private def isDigit (c : Char) : Bool :=
  c.toNat >= 48 && c.toNat <= 57  -- '0' to '9'

/-- Check if a name follows snake_case conventions -/
private def isSnakeCase (name : String) : Bool :=
  if name.isEmpty then true
  else
    let chars := name.toList
    match chars with
    | [] => true
    | c :: rest =>
      (isLowerAscii c || c == '_') &&
      rest.all fun c => isLowerAscii c || isDigit c || c == '_'

/-- Check if a name follows PascalCase convention -/
private def isPascalCase (name : String) : Bool :=
  if name.isEmpty then true
  else
    let chars := name.toList
    match chars with
    | [] => true
    | c :: rest =>
      isUpperAscii c &&
      rest.all fun c => isUpperAscii c || isLowerAscii c || isDigit c

/-- Check if a character is an identifier character (letter, digit, or underscore) -/
private def isIdentChar (c : Char) : Bool :=
  isUpperAscii c || isLowerAscii c || isDigit c || c == '_'

/-- Check if a name is an operator (contains non-identifier characters). -/
private def isOperatorName (name : String) : Bool :=
  if name.isEmpty then false
  else name.toList.any fun c => !isIdentChar c

/-- Check naming convention for a declaration and report warning if violated -/
private def checkNamingConvention (name : Syntax.Name) (declKind : String) (expected : NamingConvention) : LowerM Unit := do
  let nameStr := name.value
  if nameStr.startsWith "_" then return
  if isOperatorName nameStr then return
  let valid := match expected with
    | .snakeCase => isSnakeCase nameStr
    | .pascalCase => isPascalCase nameStr
  if !valid then
    LowerM.reportWarning (.namingConvention declKind nameStr name.span expected)

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
    checkNamingConvention name "function" .snakeCase
    -- Check for duplicate definition
    let existing? ← LowerM.lookupVar LocalEnv.empty name.value
    match existing? with
    | some (.inr existingInfo) =>
      -- Report duplicate with both spans
      LowerM.reportError (.duplicateDefinition name.value name.span existingInfo.definedAt)
    | _ =>
      -- Register the function name (but don't resolve type yet)
      let globalName ← LowerM.freshUserName name.value
      -- Store raw syntax - will be resolved during dependent type checking
      LowerM.registerGlobal name.value { name := globalName, typeSyntax := sig, definedAt := name.span }

  | .data name params constructors _kind _span =>
    checkNamingConvention name "type" .pascalCase
    -- Register the type
    let modName ← LowerM.getModuleName
    let uniqueId ← LowerM.freshUniqueId
    let typeUnique : Unique := { id := uniqueId, module := modName, original := name.value }
    let typeId : TypeId := { module := modName, name := name.value, unique := uniqueId }
    LowerM.registerType name.value {
      typeId := typeId
      paramNames := params.map (·.name.value)
      unique := typeUnique
    }

    -- Register constructors
    let ctorList := enumWithIndex constructors.toList
    for (i, ctor) in ctorList do
      checkNamingConvention ctor.name "constructor" .pascalCase
      let ctorName := LowerM.mkCtorName typeUnique ctor.name.value i
      -- Check if this is an indexed constructor (has full signature) or simple (has fields)
      match ctor.sig with
      | some sig =>
        -- Indexed constructor: store the full signature
        LowerM.registerConstructor ctor.name.value
          { name := ctorName, parentType := name.value, parentUnique := typeUnique, tag := i,
            fieldTypeSyntax := #[], sigSyntax := some sig, span := ctor.span }
      | none =>
        -- Simple constructor: store field types
        let fieldTypeSyntax := ctor.fields.map (·.2)
        LowerM.registerConstructor ctor.name.value
          { name := ctorName, parentType := name.value, parentUnique := typeUnique, tag := i,
            fieldTypeSyntax := fieldTypeSyntax, sigSyntax := none, span := ctor.span }

  | .struct name params ctorName fields _span =>
    checkNamingConvention name "struct" .pascalCase
    checkNamingConvention ctorName "constructor" .pascalCase
    -- Register the type
    let modName ← LowerM.getModuleName
    let uniqueId ← LowerM.freshUniqueId
    let typeUnique : Unique := { id := uniqueId, module := modName, original := name.value }
    let typeId : TypeId := { module := modName, name := name.value, unique := uniqueId }
    let fieldNames := fields.filterMap fun field => field.name.map (·.value)
    LowerM.registerType name.value {
      typeId := typeId
      paramNames := params.map (·.name.value)
      unique := typeUnique
      fieldNames := fieldNames
    }

    -- Register the constructor
    let ctorMetalName := LowerM.mkCtorName typeUnique ctorName.value 0
    let fieldTypeSyntax := fields.map (·.type_)
    LowerM.registerConstructor ctorName.value
      { name := ctorMetalName, parentType := name.value, parentUnique := typeUnique, tag := 0, fieldTypeSyntax := fieldTypeSyntax, span := ctorName.span }

  | .trait name params constraints methods _span =>
    checkNamingConvention name "trait" .pascalCase
    -- Register the type class
    let modName ← LowerM.getModuleName
    let uniqueId ← LowerM.freshUniqueId
    let typeUnique : Unique := { id := uniqueId, module := modName, original := name.value }
    let typeId : TypeId := { module := modName, name := name.value, unique := uniqueId }
    let globalName ← LowerM.freshUserName name.value

    -- Store method signatures as syntax (unresolved)
    let methodSigs ← methods.mapM fun m => do
      checkNamingConvention m.name "function" .snakeCase
      let methodGlobalName ← LowerM.freshUserName m.name.value
      pure (methodGlobalName, m.type_)

    LowerM.registerTypeClass name.value
      { name := globalName
        typeId := typeId
        params := params
        superclasses := constraints
        methods := methodSigs
        unique := typeUnique }

    -- Register each trait method as a global so it can be looked up as a variable
    for (methodName, _) in methodSigs do
      LowerM.registerGlobal methodName.display { name := methodName, typeSyntax := none, definedAt := name.span }

  | .instance_ _instanceName _traitName _args _constraints methods _ =>
    -- Instance methods should NOT register as new globals - they implement existing trait methods
    for methodDecl in methods do
      match methodDecl with
      | .def_ _attrs name sig _clauses _span =>
        -- Only register if not already present (from the trait)
        let existing? ← LowerM.lookupVar LocalEnv.empty name.value
        if existing?.isNone then
          let globalName ← LowerM.freshUserName name.value
          LowerM.registerGlobal name.value { name := globalName, typeSyntax := sig, definedAt := name.span }
      | _ => pure ()
    pure ()

  | .use _path _items _ =>
    -- Imports are handled by the driver
    pure ()

  | .export_ _items _ =>
    -- Exports are handled by the driver
    pure ()

  | .abbrev name params _type _span =>
    checkNamingConvention name "type" .pascalCase
    -- Register the type abbreviation
    let modName ← LowerM.getModuleName
    let uniqueId ← LowerM.freshUniqueId
    let typeUnique : Unique := { id := uniqueId, module := modName, original := name.value }
    let typeId : TypeId := { module := modName, name := name.value, unique := uniqueId }
    LowerM.registerType name.value {
      typeId := typeId
      paramNames := params.map (·.value)
      unique := typeUnique
    }

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

/-- Check if a pattern is a simple variable or wildcard pattern -/
private def isSimpleVarPattern : Syntax.Pattern → Bool
  | .var _ => true
  | .wildcard _ => true
  | .parens inner _ => isSimpleVarPattern inner
  | .typed inner _ _ => isSimpleVarPattern inner
  | _ => false

/-- Check if all patterns in a clause are simple variable patterns -/
private def allSimplePatterns (patterns : Array Syntax.Pattern) : Bool :=
  patterns.all isSimpleVarPattern

/-- Extract variable name from a simple pattern -/
private def extractVarName : Syntax.Pattern → String
  | .var n => n.value
  | .parens inner _ => extractVarName inner
  | .typed inner _ _ => extractVarName inner
  | _ => "_"

/-- Lower a function definition to an UntypedFunction.

    For functions with complex patterns (e.g., `def head | (x:xs) => x`), we transform them
    into functions with synthetic parameters and a case expression:
    `def head = \_arg0 -> case _arg0 of (x:xs) => x`

    This ensures pattern variables are properly bound via the existing case arm lowering.
-/
def lowerFunction (decl : Decl) : LowerM (Option UntypedFunction) := do
  match decl with
  | .def_ attrs name sig clauses span =>
    if h : clauses.size > 0 then
      let clause := clauses[0]

      -- Get the function's registered name
      let globalInfo? ← LowerM.lookupVar LocalEnv.empty name.value
      let globalName ← match globalInfo? with
        | some (.inr info) => pure info.name
        | _ => LowerM.freshUserName name.value  -- Fallback: create a fresh name

      -- Build function attributes
      let funcAttrs : FunctionAttrs := {
        inline := attrs.any fun a => a.name.value == "inline"
        noInline := attrs.any fun a => a.name.value == "noinline"
        total := attrs.any fun a => a.name.value == "total"
        deprecated := none
        extern := none
      }

      -- Check if all patterns are simple variables
      if allSimplePatterns clause.patterns then
        -- Simple case: all patterns are variable patterns
        -- Build params directly from patterns
        let params ← clause.patterns.mapM fun pat => do
          let paramName := extractVarName pat
          let bindingId ← LowerM.freshParamId paramName
          pure (bindingId, paramName)

        -- Build ParamList for the lambda body
        let paramList := buildParamList params.toList

        -- Extend environment with params
        let localEnv := extendEnvWithParams LocalEnv.empty paramList

        -- Lower the body in the paramList scope
        let bodyRaw ← lowerExpr localEnv clause.body
        let body : UntypedExpr (params.toList.map Prod.fst) :=
          castExprScope (by rw [List.append_nil, buildParamList_bindingIds_eq]) bodyRaw

        pure (some {
          name := globalName
          params := params
          body := body
          declaredTypeSyntax := sig
          closureInfo := none
          attrs := funcAttrs
        })
      else
        -- Complex case: patterns contain structured patterns (tuples, constructors, cons, etc.)
        -- Strategy: Transform `def f | pat => body` into an equivalent syntax expression
        -- `case (_arg0, ...) of | (pat, ...) => body` and lower that.
        --
        -- This reuses the existing case/arm lowering which properly handles pattern bindings.

        let numParams := clause.patterns.size

        -- Create synthetic parameters
        let params ← (List.range numParams).toArray.mapM fun i => do
          let bindingId ← LowerM.freshParamId s!"_arg{i}"
          pure (bindingId, s!"_arg{i}")

        -- Build ParamList and extend environment
        let paramList := buildParamList params.toList
        let localEnv := extendEnvWithParams LocalEnv.empty paramList

        -- Build a syntax-level case expression and lower it
        -- Scrutinees: references to the synthetic params (as syntax vars)
        let scrutineeSyntax : Array Syntax.Expr := params.map fun (_, paramName) =>
          Syntax.Expr.var ⟨paramName, span⟩

        -- Arms: convert each DefClause to a MatchArm
        let armsSyntax : Array Syntax.MatchArm := clauses.map fun c =>
          Syntax.MatchArm.mk c.patterns c.guard c.body c.span

        -- Create the case expression in syntax form
        let caseSyntax := Syntax.Expr.case scrutineeSyntax armsSyntax span

        -- Lower this case expression - it will properly handle pattern bindings
        let bodyRaw ← lowerExpr localEnv caseSyntax

        let body : UntypedExpr (params.toList.map Prod.fst) :=
          castExprScope (by rw [List.append_nil, buildParamList_bindingIds_eq]) bodyRaw

        pure (some {
          name := globalName
          params := params
          body := body
          declaredTypeSyntax := sig
          closureInfo := none
          attrs := funcAttrs
        })
    else
      -- No clauses - check for @[intrinsic] or @[extern] attributes
      let isIntrinsic := attrs.any fun a => a.name.value == "intrinsic"
      let isExtern := attrs.any fun a => a.name.value == "extern"

      if isIntrinsic || isExtern then
        let globalInfo? ← LowerM.lookupVar LocalEnv.empty name.value
        let globalName ← match globalInfo? with
          | some (.inr info) => pure info.name
          | _ => LowerM.freshUserName name.value

        -- Intrinsics/externs have no real body - create a placeholder panic
        -- The actual implementation comes from the runtime/LLVM intrinsics or external linkage
        let body : UntypedExpr [] := .panic s!"{if isIntrinsic then "intrinsic" else "extern"}:{name.value}" () span

        let funcAttrs : FunctionAttrs := {
          inline := attrs.any fun a => a.name.value == "inline"
          noInline := attrs.any fun a => a.name.value == "noinline"
          total := attrs.any fun a => a.name.value == "total"
          deprecated := none
          extern := some name.value  -- Mark as extern with the function name
        }

        pure (some {
          name := globalName
          params := #[]
          body := body
          declaredTypeSyntax := sig
          closureInfo := none
          attrs := funcAttrs
        })
      else
        -- No clauses and no intrinsic/extern attribute - invalid
        pure none

  | _ => pure none

/-- Lower a type definition to an UntypedTypeDef -/
def lowerTypeDef (decl : Decl) : LowerM (Option UntypedTypeDef) := do
  match decl with
  | .data name _params constructors _kind _ =>
    let typeUnique ← LowerM.freshUnique name.value
    let typeName := Name.user typeUnique
    let typeVarNames := _params.map (·.name.value)

    -- Build untyped constructors with field type syntax preserved
    let ctorList := enumWithIndex constructors.toList
    let ctors ← ctorList.toArray.mapM fun (i, ctor) => do
      let ctorName := Name.ctor typeUnique ctor.name.value i
      -- Check if this is an indexed constructor or simple constructor
      match ctor.sig with
      | some sig =>
        -- Indexed constructor: store full signature
        pure { name := ctorName, tag := i, fieldTypeSyntax := #[], sigSyntax := some sig : UntypedConstructor }
      | none =>
        -- Simple constructor: extract field types
        let fieldTypes := ctor.fields.map (·.2)
        pure { name := ctorName, tag := i, fieldTypeSyntax := fieldTypes, sigSyntax := none : UntypedConstructor }

    pure (some (.algebraic typeName typeVarNames ctors))

  | .struct name _params ctorName fields _ =>
    let typeUnique ← LowerM.freshUnique name.value
    let typeName := Name.user typeUnique
    let typeVarNames := _params.map (·.name.value)
    let ctorMetalName := Name.ctor typeUnique ctorName.value 0
    -- Extract optional field names and types
    let fieldsWithOptNames := fields.map fun field =>
      (field.name.map (·.value), field.type_)

    pure (some (.struct typeName typeVarNames ctorMetalName fieldsWithOptNames))

  | _ => pure none

/-- Lower an instance declaration to an UntypedInstance -/
def lowerInstance (decl : Decl) : LowerM (Option UntypedInstance) := do
  match decl with
  | .instance_ _instanceName traitName args constraints methods span =>
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

/-- Lower a type abbreviation -/
def lowerAbbrev (decl : Decl) : LowerM (Option TypeAbbrev) := do
  match decl with
  | .abbrev name params expansion span =>
    pure (some {
      name := name.value
      params := params.map (·.value)
      expansion := expansion
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

  -- Fifth pass: lower abbreviations
  let abbreviations ← decls.filterMapM lowerAbbrev

  -- Sixth pass: extract type class metadata from GlobalEnv
  let genv ← LowerM.getGlobalEnv
  let typeClasses := genv.typeClasses.fold (init := #[]) fun acc _ info =>
    acc.push { name := info.name
               params := info.params
               superclasses := info.superclasses
               methodSignatures := info.methods : TypeClassMeta }

  pure {
    name := moduleName
    functions := functions
    types := types
    instances := instances
    typeClasses := typeClasses
    abbreviations := abbreviations
  }

/-- Get the name of a declaration (for tracking purposes) -/
def getDeclName (decl : Decl) : Option String :=
  match decl with
  | .def_ _ name _ _ _ => some name.value
  | .data name _ _ _ _ => some name.value
  | .struct name _ _ _ _ => some name.value
  | .trait name _ _ _ _ => some name.value
  | .instance_ instanceName traitName args _ _ _ =>
    -- Use the instance name if provided, otherwise generate from trait name
    match instanceName with
    | some name => some name.value
    | none =>
      let argStr := args.foldl (fun acc _ => acc ++ "_") ""
      some s!"instance_{traitName.value}{argStr}"
  | .use _ _ _ => none
  | .export_ _ _ => none
  | .abbrev name _ _ _ => some name.value

/-- Result of incremental lowering -/
structure IncrementalLowerResult where
  /-- The complete module -/
  module : UntypedModule
  /-- Lowering errors -/
  errors : Array LowerError
  /-- Lowering warnings -/
  warnings : Array LowerWarning
  /-- The final global environment -/
  globalEnv : GlobalEnv
  /-- Next binding ID counter -/
  nextBindingId : Nat
  /-- Next unique ID counter -/
  nextUniqueId : Nat
  /-- Cached functions by declaration name -/
  functionsByName : Std.HashMap String UntypedFunction
  /-- Cached type definitions by declaration name -/
  typesByName : Std.HashMap String UntypedTypeDef
  /-- Cached instances by declaration name -/
  instancesByName : Std.HashMap String UntypedInstance

/-- Lower a module from scratch and build the incremental cache -/
def lowerModuleFresh (syntaxModule : Syntax.Module) : IncrementalLowerResult :=
  let (metalModule, finalState) := LowerM.run (lowerModule syntaxModule.name syntaxModule.decls) syntaxModule.name

  -- Build name-to-output mappings
  let functionsByName := metalModule.functions.foldl (fun acc fn =>
    match fn.name with
    | .user u => acc.insert u.original fn
    | _ => acc) {}

  let typesByName := metalModule.types.foldl (fun acc td =>
    match td.name with
    | .user u => acc.insert u.original td
    | _ => acc) {}

  let instancesByName := metalModule.instances.foldl (fun acc inst =>
    let instName := s!"instance_{inst.className}"
    acc.insert instName inst) {}

  { module := metalModule
  , errors := finalState.errors
  , warnings := finalState.warnings
  , globalEnv := finalState.globalEnv
  , nextBindingId := finalState.nextBindingId
  , nextUniqueId := finalState.nextUniqueId
  , functionsByName := functionsByName
  , typesByName := typesByName
  , instancesByName := instancesByName
  }

/-- Lower a module with external symbols pre-populated in the GlobalEnv -/
def lowerModuleWithExternals (syntaxModule : Syntax.Module) (initialEnv : GlobalEnv) : IncrementalLowerResult :=
  let (metalModule, finalState) := LowerM.runWithEnv (lowerModule syntaxModule.name syntaxModule.decls) syntaxModule.name initialEnv

  -- Build name-to-output mappings
  let functionsByName := metalModule.functions.foldl (fun acc fn =>
    match fn.name with
    | .user u => acc.insert u.original fn
    | _ => acc) {}

  let typesByName := metalModule.types.foldl (fun acc td =>
    match td.name with
    | .user u => acc.insert u.original td
    | _ => acc) {}

  let instancesByName := metalModule.instances.foldl (fun acc inst =>
    let instName := s!"instance_{inst.className}"
    acc.insert instName inst) {}

  { module := metalModule
  , errors := finalState.errors
  , warnings := finalState.warnings
  , globalEnv := finalState.globalEnv
  , nextBindingId := finalState.nextBindingId
  , nextUniqueId := finalState.nextUniqueId
  , functionsByName := functionsByName
  , typesByName := typesByName
  , instancesByName := instancesByName
  }

/-- Remove entries for a declaration from GlobalEnv -/
def removeFromGlobalEnv (env : GlobalEnv) (declName : String) : GlobalEnv :=
  let globals := env.globals.erase declName
  let types := env.types.erase declName
  let constructors := env.constructors.fold (fun acc name info =>
    if info.parentType == declName then acc
    else acc.insert name info) {}
  let typeClasses := env.typeClasses.erase declName
  { env with globals, types, constructors, typeClasses }

/-- Helper to lower only changed declarations -/
def lowerChangedDecls (changedDecls : Array Decl)
    : LowerM (Array UntypedFunction × Array UntypedTypeDef × Array UntypedInstance) := do
  for decl in changedDecls do
    collectGlobals decl

  let newFunctions ← changedDecls.filterMapM lowerFunction
  let newTypes ← changedDecls.filterMapM lowerTypeDef
  let newInstances ← changedDecls.filterMapM lowerInstance

  pure (newFunctions, newTypes, newInstances)

/-- Lower a module incrementally, only re-processing changed declarations -/
def lowerModuleIncremental
    (syntaxModule : Syntax.Module)
    (changedDeclNames : Array String)
    (oldResult : IncrementalLowerResult)
    : IncrementalLowerResult :=
  if changedDeclNames.isEmpty then
    -- Nothing changed, return old result
    oldResult
  else
    let prunedEnv := changedDeclNames.foldl (fun acc name =>
      removeFromGlobalEnv acc name) oldResult.globalEnv

    let changedDecls := syntaxModule.decls.filter fun decl =>
      match getDeclName decl with
      | some name => changedDeclNames.contains name
      | none => false

    -- Initial state preserving counters but with pruned env
    let initialState : LowerState := {
      nextBindingId := oldResult.nextBindingId
      nextUniqueId := oldResult.nextUniqueId
      moduleName := syntaxModule.name
      errors := #[]
      warnings := #[]
      globalEnv := prunedEnv
    }

    -- Re-collect globals for changed declarations and re-lower them
    let (newOutputs, finalState) := StateT.run (lowerChangedDecls changedDecls) initialState

    let (newFunctions, newTypes, newInstances) := newOutputs

    -- Merge: start with old cached outputs, remove changed, add new
    let prunedFunctions : Std.HashMap String UntypedFunction :=
      changedDeclNames.foldl (fun acc name => acc.erase name) oldResult.functionsByName
    let prunedTypes : Std.HashMap String UntypedTypeDef :=
      changedDeclNames.foldl (fun acc name => acc.erase name) oldResult.typesByName
    let prunedInstances : Std.HashMap String UntypedInstance :=
      changedDeclNames.foldl (fun acc name => acc.erase s!"instance_{name}") oldResult.instancesByName

    -- Add new entries
    let functionsByName : Std.HashMap String UntypedFunction := newFunctions.foldl (fun acc fn =>
      match fn.name with
      | .user u => acc.insert u.original fn
      | _ => acc) prunedFunctions

    let typesByName : Std.HashMap String UntypedTypeDef := newTypes.foldl (fun acc td =>
      match td.name with
      | .user u => acc.insert u.original td
      | _ => acc) prunedTypes

    let instancesByName : Std.HashMap String UntypedInstance := newInstances.foldl (fun acc inst =>
      let instName := s!"instance_{inst.className}"
      acc.insert instName inst) prunedInstances

    -- Build the complete module from all cached outputs
    let allFunctions := functionsByName.fold (fun acc _ fn => acc.push fn) #[]
    let allTypes := typesByName.fold (fun acc _ td => acc.push td) #[]
    let allInstances := instancesByName.fold (fun acc _ inst => acc.push inst) #[]

    let metalModule : UntypedModule := {
      name := syntaxModule.name
      functions := allFunctions
      types := allTypes
      instances := allInstances
      typeClasses := #[]
    }

    { module := metalModule
    , errors := oldResult.errors ++ finalState.errors
    , warnings := oldResult.warnings ++ finalState.warnings
    , globalEnv := finalState.globalEnv
    , nextBindingId := finalState.nextBindingId
    , nextUniqueId := finalState.nextUniqueId
    , functionsByName := functionsByName
    , typesByName := typesByName
    , instancesByName := instancesByName
    }

end Soma.Metal.Lower
