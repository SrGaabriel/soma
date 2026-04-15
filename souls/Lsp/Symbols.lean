import Std.Data.HashSet
import Lsp.State
import Lsp.Cst
import Soma.Core.Quote
import Soma.Dependent.Monad

namespace Lsp

open Std

open Soma.Syntax
open Soma.Project (Symbol SymbolEnv SymbolKind)
open Soma.Core (Value valueToString QualifiedName)
open Soma.Dependent (Globals GlobalInfo Namespace AbbrevEnv AbbrevInfo)

/-- Build a DefinitionSite from a CstDefinition -/
def cstDefToDefinitionSite (moduleName filePath : String) (def_ : CstDefinition) : DefinitionSite :=
  { name := def_.name
  , kind := syntaxKindToSymbolKind def_.kind
  , nameSpan := def_.nameSpan
  , declSpan := def_.declSpan
  , typeSignature := def_.typeSignature
  , moduleName := moduleName
  , filePath := filePath
  }

/-- Extract import info from a use declaration node -/
def extractImportInfo (tree : RedTree) (node : RedNode) : Option ImportInfo := do
  guard (node.syntaxKind? == some .declUse)

  let pathNode ← findChild? tree node .importPath
  let pathTokens := getTokens tree pathNode
  let pathText := pathTokens
    |>.filter (·.tokenKind? != some .slash)
    |>.toList
    |>.filterMap (·.text?)
    |> String.intercalate "/"

  let items := match findChild? tree node .importItems with
    | some itemsNode =>
        let tokens := getTokens tree itemsNode
        tokens
          |>.filter (fun t => t.tokenKind? == some .lowerIdent || t.tokenKind? == some .upperIdent)
          |>.filterMap (·.text?)
    | none => #[]

  some { modulePath := pathText, items, span := tree.spanOf node }

/-- Build symbol table from RedTree (full rebuild) -/
def buildSymbolTable (moduleName filePath : String) (tree : RedTree) : SymbolTable := Id.run do
  let mut table := SymbolTable.empty

  -- Collect all definitions
  let definitions := collectDefinitions tree
  for def_ in definitions do
    let site := cstDefToDefinitionSite moduleName filePath def_
    table := table.addDefinition site

  -- Collect imports
  let importNodes := tree.nodes.filter fun node =>
    node.syntaxKind? == some .declUse
  for impNode in importNodes do
    if let some imp := extractImportInfo tree impNode then
      table := table.addImport imp

  -- Collect references
  let definedNames := table.allNames
  let refs := collectReferences tree definedNames
  for ref in refs do
    table := table.addReference {
      name := ref.name
      span := ref.span
      context := ref.context
    }

  return table

/-- Update symbol table incrementally for changed declarations -/
def updateSymbolTableIncremental
    (oldSymbols : SymbolTable)
    (tree : RedTree)
    (changedDeclIds : HashSet NodeId)
    (moduleName filePath : String) : SymbolTable := Id.run do
  -- Start with old symbols
  let mut definitions := oldSymbols.definitions
  let mut references := oldSymbols.references

  -- Collect all new definitions
  let allDefs := collectDefinitions tree

  -- Find names of changed declarations (to remove old entries)
  let changedNames : HashSet String := allDefs.foldl (fun acc def_ =>
    if changedDeclIds.contains def_.declId then acc.insert def_.name
    else acc) {}

  -- Remove old definitions for changed declarations
  for name in changedNames do
    definitions := definitions.erase name
    references := references.erase name

  -- Add new definitions for changed declarations
  for def_ in allDefs do
    if changedDeclIds.contains def_.declId then
      let site := cstDefToDefinitionSite moduleName filePath def_
      definitions := definitions.insert def_.name site

  -- Rebuild references for changed declarations
  let definedNames := definitions.toArray.map (·.1)
  let allRefs := collectReferences tree definedNames

  -- Clear and rebuild references that involve changed names
  for name in changedNames do
    references := references.erase name

  -- Add all references (simpler than trying to be incremental here)
  let mut newRefs : Std.HashMap String (Array SymbolReference) := references
  for ref in allRefs do
    let existing := newRefs.getD ref.name #[]
    -- Avoid duplicates by checking span
    let isDuplicate := existing.any (·.span == ref.span)
    if !isDuplicate then
      newRefs := newRefs.insert ref.name (existing.push {
        name := ref.name
        span := ref.span
        context := ref.context
      })

  -- Imports don't change incrementally (they're top-level)
  let imports := tree.nodes.filterMap fun node =>
    if node.syntaxKind? == some .declUse then
      extractImportInfo tree node
    else none

  return {
    definitions := definitions
    references := newRefs
    imports := imports
  }

/-- A completion item -/
structure CompletionEntry where
  label : String
  insertText : String
  kind : Lsp.SymbolKind
  detail : Option String
  deriving Inhabited

/-- Convert a GlobalInfo's DeclarationOrigin to LSP SymbolKind -/
def globalInfoToSymbolKind (info : GlobalInfo) : Lsp.SymbolKind :=
  if info.isConstructor then .constructor
  else match info.origin with
    | .typeDecl => .type
    | .constructor => .constructor
    | .projection => .field
    | .traitMethod => .method
    | .intrinsic | .extern => .function
    | _ => .function

/-- Resolve a name using Globals (namespace tree + imports), returning GlobalInfo -/
def resolveViaGlobals (globals : Globals) (currentNs : Array String)
    (path : Array String) (name : String) : Option GlobalInfo :=
  match (globals.resolve currentNs path name).bind globals.getDef with
  | some info => some info
  | none =>
    if !path.isEmpty then none
    else
      -- Search child namespaces (constructors live under their type's namespace)
      match globals.root.getAt? currentNs.toList with
      | some ns =>
        ns.children.fold (init := none) fun acc _ childNs =>
          match acc with
          | some _ => acc
          | none => (childNs.getDecl? name).bind globals.getDef
      | none => none

/-- Get the module name from a QualifiedName -/
def moduleOfQualifiedName (qn : QualifiedName) : String :=
  qn.id.module

/-- Format hover for a global declaration resolved through Globals -/
def formatGlobalHover (info : GlobalInfo) (abbrevEnv : Option AbbrevEnv := none) : String :=
  let name := info.name.display
  let typeStr := valueToString info.type
  let kindStr := toString (globalInfoToSymbolKind info)
  let moduleName := moduleOfQualifiedName info.name
  let abbrevNote := match abbrevEnv with
    | some env =>
      match env.get? info.name with
      | some abbrevInfo =>
        let expansionStr := valueToString abbrevInfo.expansion
        s!"\n\n*expands to* `{expansionStr}`"
      | none => ""
    | none => ""
  s!"```soma\n{name} :: {typeStr}\n```\n\n*{kindStr}* from `{moduleName}`{abbrevNote}"

/-- Format hover for an abbreviation resolved through AbbrevEnv -/
def formatAbbrevHover (name : String) (abbrevInfo : AbbrevInfo) : String :=
  let expansionStr := valueToString abbrevInfo.expansion
  let arityStr := if abbrevInfo.arity > 0 then s!" ({abbrevInfo.arity} parameters)" else ""
  s!"```soma\nalias {name}{arityStr} = {expansionStr}\n```\n\n*type alias* from `{abbrevInfo.abbrevId.module}`"

/-- Format hover content for a definition -/
def formatDefinitionHover (def_ : DefinitionSite) (globals : Option Globals := none)
    (abbrevEnv : Option AbbrevEnv := none) : String :=
  let kindStr := toString def_.kind
  let typeStr : Option String :=
    match def_.typeSignature with
    | some sig => some sig
    | none =>
        globals.bind fun g =>
          (g.resolve #[] #[] def_.name |>.bind g.getDef)
          |>.map fun info => valueToString info.type
  let abbrevNote := match abbrevEnv with
    | some env =>
      let resolved : Option AbbrevInfo :=
        globals.bind (fun g => g.resolve #[] #[] def_.name) |>.bind (fun qn => env.get? qn)
      match resolved with
      | some ai => s!"\n\n*expands to* `{valueToString ai.expansion}`"
      | none => ""
    | none => ""
  match typeStr with
  | some sig =>
      s!"```soma\n{def_.name} :: {sig}\n```\n\n*{kindStr}* from `{def_.moduleName}`{abbrevNote}"
  | none =>
      s!"**{def_.name}**\n\n*{kindStr}* from `{def_.moduleName}`{abbrevNote}"

/-- Convert compiler SymbolKind to LSP SymbolKind for display -/
def compilerSymbolKindToString : Soma.Project.SymbolKind → String
  | .binding => "function"
  | .dataCon _ _ => "constructor"
  | .type => "type"
  | .typeClass => "class"
  | .typeClassMethod _ => "method"
  | .instanceMethod _ _ => "instance method"
  | .letBinding => "local binding"
  | .lambdaParam => "parameter"
  | .patternVar => "variable"
  | .patternAs => "variable"
  | .composeBinding => "local binding"
  | .intrinsicBinding => "intrinsic"
  | .intrinsicType => "intrinsic type"

/-- Format hover content for an external symbol (from seedSymbols) -/
def formatExternalSymbolHover (sym : Symbol) (ty : Value) : String :=
  let kindStr := compilerSymbolKindToString sym.kind
  let typeStr := valueToString ty
  s!"```soma\n{sym.name} :: {typeStr}\n```\n\n*{kindStr}* from `{sym.module}`"

/-- Look up a name in seedSymbols -/
def lookupInSeedSymbols (name : String) (seedSymbols : SymbolEnv) : Option (Symbol × Value) :=
  seedSymbols.toArray.find? fun (sym, _) => sym.name == name

/-- Format hover for a keyword -/
def formatKeywordHover (kind : TokenKind) (text : String) : String :=
  let desc := match kind with
    | .kw_def => "Define a function or value"
    | .kw_let => "Local binding"
    | .kw_in => "Body of let expression"
    | .kw_case => "Pattern matching"
    | .kw_if => "Conditional expression"
    | .kw_then => "Then branch of if"
    | .kw_else => "Else branch of if"
    | .kw_inductive => "Define an inductive type"
    | .kw_struct => "Define a record type"
    | .kw_trait => "Define a type class"
    | .kw_instance => "Define a type class instance"
    | .kw_where => "Begin definition body or constraints"
    | .kw_with => "Add constraints"
    | .kw_use => "Import a module"
    | .kw_pub => "Public visibility modifier"
    | .kw_forall => "Universal quantification"
    | .kw_bind => "Monadic bind block"
    | .kw_compose => "Applicative compose block"
    | .kw_abbrev => "Define a type alias"
    | _ => kind.describe
  s!"**{text}** — {desc}"

/-- Format hover for a syntax construct -/
def formatSyntaxHover (kind : SyntaxKind) (text : String) : String :=
  let preview := if text.length > 50 then (text.take 50 |>.copy) ++ "..." else text
  s!"*{kind.describe}*\n```soma\n{preview}\n```"

/-- Extract qualified path segments from an exprVar parent node -/
def extractQualifiedPath (tree : RedTree) (node : RedNode) : Array String × String :=
  match tree.parent? node with
  | some parent =>
    match parent.syntaxKind? with
    | some .exprVar =>
      let tokens := getTokens tree parent
      let identTokens := tokens.filter fun t =>
        t.tokenKind? == some .lowerIdent || t.tokenKind? == some .upperIdent
      let names := identTokens.filterMap (·.text?)
      if names.isEmpty then (#[], "")
      else
        let path := names.extract 0 (names.size - 1)
        let name := names[names.size - 1]!
        (path, name)
    | _ => (#[], node.text?.getD "")
  | none => (#[], node.text?.getD "")

/-- Get hover information at a position -/
def getHoverAt (offset : Nat) (mod : CompiledModule) (allModules : Array CompiledModule)
    (seedSymbols : SymbolEnv := {}) : Option (String × Span) := do
  let nodeInfo ← findNodeAtPosition offset mod.tree

  guard (!nodeInfo.node.green.isTrivia)
  if nodeInfo.node.syntaxKind? == some .triviaToken then none else

  let span := mod.tree.spanOf nodeInfo.node

  -- Check if it's a token
  if nodeInfo.node.isToken then
    let text ← nodeInfo.node.text?
    let kind ← nodeInfo.node.tokenKind?

    if kind.isNameLike then
      if let some local_ := mod.scopeMap.resolveByNodeId nodeInfo.node.id then
        return (formatLocalBindingHover local_, span)
      if let some local_ := mod.scopeMap.resolve text offset then
        return (formatLocalBindingHover local_, span)
      if let some globals := mod.globals then
        let currentNs := mod.name.splitOn "/" |>.toArray
        let (qualPath, _qualName) := extractQualifiedPath mod.tree nodeInfo.node
        if let some info := resolveViaGlobals globals currentNs qualPath text then
          return (formatGlobalHover info mod.abbrevEnv, span)
      if let some def_ := mod.symbols.lookupDefinition text then
        return (formatDefinitionHover def_ mod.globals mod.abbrevEnv, span)
      for other in allModules do
        if other.filePath != mod.filePath then
          if let some globals := other.globals then
            let otherNs := other.name.splitOn "/" |>.toArray
            if let some info := resolveViaGlobals globals otherNs #[] text then
              return (formatGlobalHover info other.abbrevEnv, span)
          if let some def_ := other.symbols.lookupDefinition text then
            return (formatDefinitionHover def_ other.globals other.abbrevEnv, span)
      if let some (sym, ty) := lookupInSeedSymbols text seedSymbols then
        return (formatExternalSymbolHover sym ty, span)
      -- Unknown identifier/operator
      return (s!"**{text}** — *unknown*", span)
    else if kind.isKeyword then
      return (formatKeywordHover kind text, span)
    else
      -- Punctuation
      return (s!"`{text}` — {kind.describe}", span)
  else
    -- Interior node
    if let some kind := nodeInfo.node.syntaxKind? then
      match nodeInfo.node.green with
      | .error msg _ _ =>
          return (s!"**Error** at {span.start.line}:{span.start.column}\n\n{msg}", span)
      | .missing expected =>
          return (s!"**Missing** at {span.start.line}:{span.start.column}\n\nExpected: {expected.describe}", span)
      | _ =>
          let text := nodeText mod.tree nodeInfo.node
          return (formatSyntaxHover kind text, span)
    else
      none

/-- Find definition location for a name, using Globals as primary source -/
def findDefinitionLocation (name : String) (mod : CompiledModule) (allModules : Array CompiledModule)
    (seedSymbols : SymbolEnv := {}) (qualPath : Array String := #[]) : Option (String × Span) := do
  if let some globals := mod.globals then
    let currentNs := mod.name.splitOn "/" |>.toArray
    if let some _info := resolveViaGlobals globals currentNs qualPath name then
      -- Found via Globals, now locate the definition site
      if let some def_ := mod.symbols.lookupDefinition name then
        return (def_.filePath, def_.nameSpan)
      -- Check imported modules for the CST definition site
      for imp in mod.symbols.imports do
        for other in allModules do
          if other.name == imp.modulePath || other.filePath.endsWith imp.modulePath then
            if let some def_ := other.symbols.lookupDefinition name then
              if imp.items.isEmpty || imp.items.contains name then
                return (def_.filePath, def_.nameSpan)
      -- Fall back to searching all modules
      for other in allModules do
        if let some def_ := other.symbols.lookupDefinition name then
          return (other.filePath, def_.nameSpan)

  if let some def_ := mod.symbols.lookupDefinition name then
    return (def_.filePath, def_.nameSpan)

  for imp in mod.symbols.imports do
    for other in allModules do
      if other.name == imp.modulePath || other.filePath.endsWith imp.modulePath then
        if let some def_ := other.symbols.lookupDefinition name then
          if imp.items.isEmpty || imp.items.contains name then
            return (def_.filePath, def_.nameSpan)

  for other in allModules do
    if let some def_ := other.symbols.lookupDefinition name then
      return (def_.filePath, def_.nameSpan)

  -- External dependencies
  if let some (sym, _) := lookupInSeedSymbols name seedSymbols then
    return (sym.module ++ ".soma", sym.span)

  none

/-- Get definition at a position -/
def getDefinitionAt (offset : Nat) (mod : CompiledModule) (allModules : Array CompiledModule)
    (seedSymbols : SymbolEnv := {}) : Option (String × Span) := do
  let nodeInfo ← findNodeAtPosition offset mod.tree

  if nodeInfo.node.isToken then
    let kind ← nodeInfo.node.tokenKind?
    if kind.isNameLike then
      let text ← nodeInfo.node.text?
      if let some local_ := mod.scopeMap.resolveByNodeId nodeInfo.node.id then
        return (mod.filePath, local_.nameSpan)
      if let some local_ := mod.scopeMap.resolve text offset then
        return (mod.filePath, local_.nameSpan)
      let (qualPath, _) := extractQualifiedPath mod.tree nodeInfo.node
      findDefinitionLocation text mod allModules seedSymbols qualPath
    else
      none
  else
    none

/-- LSP completion item kind numbers -/
def completionKindNumber : Lsp.SymbolKind → Nat
  | .function => 3      -- Function
  | .type => 22         -- Struct
  | .typeAlias => 22    -- Struct
  | .constructor => 4   -- Constructor
  | .field => 5         -- Field
  | .trait => 8         -- Interface
  | .method => 2        -- Method
  | .variable => 6      -- Variable
  | .typeVariable => 25 -- TypeParameter
  | .module => 9        -- Module
  | .parameter => 6     -- Variable

/-- Parse a qualified prefix like "Foo::Bar::" from the text before cursor -/
def parseQualifiedPrefix (source : String) (offset : Nat) : Array String × String := Id.run do
  let before := (source.take offset).toString
  let chars := before.toList.reverse
  let mut segments : Array String := #[]
  let mut currentSeg : List Char := []
  let mut cs := chars
  let mut sawDoubleColon := false

  while !cs.isEmpty do
    match cs with
    | c :: rest =>
      if c == ':' then
        match rest with
        | ':' :: rest2 =>
          -- Push whatever we've accumulated (possibly empty for trailing ::)
          segments := #[String.ofList currentSeg.reverse] ++ segments
          currentSeg := []
          sawDoubleColon := true
          cs := rest2
        | _ => break
      else if c.isAlphanum || c == '_' then
        currentSeg := currentSeg ++ [c]
        cs := rest
      else
        break
    | [] => break

  if !currentSeg.isEmpty then
    segments := #[String.ofList currentSeg.reverse] ++ segments

  if !sawDoubleColon then
    return (#[], "")

  if segments.isEmpty then
    return (#[], "")

  let path := segments.extract 0 (segments.size - 1)
  let namePart := segments[segments.size - 1]!
  (path, namePart)

/-- Get completions from a namespace node -/
def completionsFromNamespace (ns : Namespace) (globals : Globals) (namePrefix : String)
    : Array CompletionEntry := Id.run do
  let mut results : Array CompletionEntry := #[]
  for (name, qn) in ns.decls.toArray do
    if namePrefix.isEmpty || name.startsWith namePrefix then
      let kind := match globals.getDef qn with
        | some info => globalInfoToSymbolKind info
        | none => Lsp.SymbolKind.variable
      let typeStr := (globals.getDef qn).map fun info => valueToString info.type
      results := results.push { label := name, insertText := name, kind, detail := typeStr }
  for (childName, _) in ns.children.toArray do
    if namePrefix.isEmpty || childName.startsWith namePrefix then
      results := results.push { label := childName, insertText := childName, kind := .module, detail := some "namespace" }
  return results

/-- Collect all visible completions from Globals -/
def globalsCompletions (globals : Globals) (currentNs : Array String)
    : Array CompletionEntry := Id.run do
  let mut results : Array CompletionEntry := #[]
  let mut seen : Std.HashSet String := {}

  -- Declarations in the current namespace
  if let some ns := globals.root.getAt? currentNs.toList then
    for (name, qn) in ns.decls.toArray do
      if !seen.contains name then
        seen := seen.insert name
        let kind := match globals.getDef qn with
          | some info => globalInfoToSymbolKind info
          | none => Lsp.SymbolKind.variable
        let typeStr := (globals.getDef qn).map fun info => valueToString info.type
        results := results.push { label := name, insertText := name, kind, detail := typeStr }

    -- Also collect constructors from child namespaces (types contain their constructors)
    for (childName, childNs) in ns.children.toArray do
      for (ctorName, ctorQn) in childNs.decls.toArray do
        let qualName := s!"{childName}::{ctorName}"
        if !seen.contains qualName then
          seen := seen.insert qualName
          let kind := match globals.getDef ctorQn with
            | some info => globalInfoToSymbolKind info
            | none => Lsp.SymbolKind.variable
          let typeStr := (globals.getDef ctorQn).map fun info => valueToString info.type
          results := results.push { label := qualName, insertText := qualName, kind, detail := typeStr }

  -- Imported symbols
  for (name, (_, qn)) in globals.imports.toArray do
    if !seen.contains name then
      seen := seen.insert name
      let kind := match globals.getDef qn with
        | some info => globalInfoToSymbolKind info
        | none => Lsp.SymbolKind.variable
      let typeStr := (globals.getDef qn).map fun info => valueToString info.type
      results := results.push { label := name, insertText := name, kind, detail := typeStr }

  return results

/-- Get completions from Globals filtered by context -/
def getGlobalsCompletionsForContext (context : SyntaxContext) (globals : Globals)
    (currentNs : Array String) (_abbrevEnv : Option AbbrevEnv)
    : Array CompletionEntry :=
  let all := globalsCompletions globals currentNs
  match context with
  | .inTypeExpr | .inTypeSignature | .afterColon =>
      all.filter fun e =>
        e.kind == .type || e.kind == .typeVariable || e.kind == .typeAlias || e.kind == .trait
  | .inPattern =>
      all.filter fun e =>
        e.kind == .constructor || e.kind == .variable
  | _ => all

/-- Get module path completions for import declarations -/
def getModulePathCompletions (state : LspState) (partialPath : String)
    : Array CompletionEntry := Id.run do
  let mut results : Array CompletionEntry := #[]
  for (modName, _) in state.moduleNameToPath.toArray do
    if partialPath.isEmpty || modName.startsWith partialPath then
      results := results.push { label := modName, insertText := modName, kind := .module, detail := some "module" }
  return results

/-- Get field completions for a type -/
def getFieldCompletions (globals : Globals) (_name : String)
    : Array CompletionEntry := Id.run do
  let mut results : Array CompletionEntry := #[]
  for (typeQn, fields) in globals.recordFields.toArray do
    for fieldName in fields do
      let isDuplicate := results.any fun e => e.label == fieldName
      if !isDuplicate then
        let typeStr := (globals.getDef typeQn).map fun info =>
          s!"{info.name.display}.{fieldName}"
        results := results.push { label := fieldName, insertText := fieldName, kind := .field, detail := typeStr }
  return results

/-- CST-based completions -/
def getCompletionsForContextCst (context : SyntaxContext) (mod : CompiledModule)
    (allModules : Array CompiledModule) : Array DefinitionSite :=
  let otherModules := allModules.filter (·.filePath != mod.filePath)
  match context with
  | .inTypeExpr | .inTypeSignature | .afterColon =>
      let localTypes := mod.symbols.definitionsOfKind .type
      let localAliases := mod.symbols.definitionsOfKind .typeAlias
      let localTyVars := mod.symbols.definitionsOfKind .typeVariable
      let importedTypes := otherModules.foldl (fun acc m =>
        acc ++ m.symbols.definitionsOfKind .type ++ m.symbols.definitionsOfKind .typeAlias) #[]
      localTypes ++ localAliases ++ localTyVars ++ importedTypes

  | .inPattern =>
      let constructors := mod.symbols.definitionsOfKind .constructor
      let variables := mod.symbols.definitionsOfKind .variable
      let importedCons := otherModules.foldl (fun acc m =>
        acc ++ m.symbols.definitionsOfKind .constructor) #[]
      constructors ++ variables ++ importedCons

  | .afterDot _ =>
      mod.symbols.definitionsOfKind .field

  | .inImport | .inImportItems =>
      #[]

  | _ =>
      let local_ := mod.symbols.allDefinitions
      let imported := otherModules.foldl (fun acc m =>
        acc ++ m.symbols.allDefinitions) #[]
      local_ ++ imported

/-- Get all completions at a position -/
def getCompletionsAt (offset : Nat) (mod : CompiledModule) (allModules : Array CompiledModule)
    (state : Option LspState := none) (liveContent : Option String := none)
    (cursorLine : Option Nat := none) (cursorCol : Option Nat := none)
    : Array CompletionEntry := Id.run do
  let context := match findNodeAtPosition offset mod.tree with
    | some nodeInfo => nodeInfo.context
    | none => .unknown

  -- Check for qualified name prefix
  if let some globals := mod.globals then
    let currentNs := mod.name.splitOn "/" |>.toArray

    -- Extract text before cursor using line+col (avoids byte/char offset mismatch)
    let textBeforeCursor : String := match liveContent, cursorLine, cursorCol with
      | some live, some line, some col =>
        let lines := (live.splitOn "\n").toArray
        if h : line < lines.size then
          ((lines[line]).take col).toString
        else ""
      | _, _, _ => ((mod.sourceContent.take offset).toString)

    let (path, partialName) := parseQualifiedPrefix textBeforeCursor textBeforeCursor.length
    if !path.isEmpty then
      let relativePath := currentNs.toList ++ path.toList
      pure ()
      if let some ns := globals.root.getAt? relativePath then
        let results := completionsFromNamespace ns globals partialName

        return results
      pure ()
      if let some ns := globals.root.getAt? path.toList then
        return completionsFromNamespace ns globals partialName
      -- Try via imports: first segment might be an imported module name
      match path.toList with
      | head :: rest =>
        if let some (treePath, _) := globals.imports.get? head then
          let fullPath := treePath ++ [head] ++ rest
          if let some ns := globals.root.getAt? fullPath then
            return completionsFromNamespace ns globals partialName
      | [] => pure ()

    -- Module path completions for import declarations
    match context with
    | .inImport | .inImportItems =>
      if let some st := state then
        return getModulePathCompletions st ""
      else return #[]
    | .afterDot _ =>
      -- Field completions
      return getFieldCompletions globals ""
    | _ =>
      -- Standard completions from Globals
      return getGlobalsCompletionsForContext context globals currentNs mod.abbrevEnv

  pure ()
  -- CST fallback when Globals unavailable
  let cstCompletions := getCompletionsForContextCst context mod allModules
  return cstCompletions.map fun def_ =>
    { label := def_.name, insertText := def_.name, kind := def_.kind, detail := def_.typeSignature }

/-- Try to find a local binding at the given offset (either in scope or at binding site) -/
private def resolveLocalBinding (name : String) (offset : Nat) (mod : CompiledModule)
    : Option LocalBinding :=
  -- Try in-scope resolution first
  if let some local_ := mod.scopeMap.resolve name offset then
    some local_
  else
    -- Try binding-site resolution (cursor is on the definition)
    mod.scopeMap.bindings.find? fun b =>
      b.name == name &&
      offset >= b.nameSpan.start.byteOffset &&
      offset < b.nameSpan.stop.byteOffset

/-- Find all references to a name in a module -/
def findReferencesInModule (name : String) (mod : CompiledModule)
    (targetOffset : Option Nat := none) : Array Span :=
  match targetOffset with
  | some offset =>
    if let some local_ := resolveLocalBinding name offset mod then
      mod.scopeMap.findLocalReferences local_ mod.tree
    else
      (mod.symbols.getReferences name).map (·.span)
  | none =>
    (mod.symbols.getReferences name).map (·.span)

/-- Find all references across modules -/
def findAllReferences (name : String) (allModules : Array CompiledModule)
    (targetOffset : Option Nat := none)
    : Array (String × Span) :=
  allModules.foldl (fun acc mod =>
    let refs := findReferencesInModule name mod targetOffset
    acc ++ refs.map (mod.filePath, ·)) #[]

/-- LSP symbol kind numbers -/
def documentSymbolKindNumber : Lsp.SymbolKind → Nat
  | .function => 12     -- Function
  | .type => 5          -- Class
  | .typeAlias => 5     -- Class (same visual as type)
  | .constructor => 9   -- Constructor
  | .field => 8         -- Field
  | .trait => 11        -- Interface
  | .method => 6        -- Method
  | .variable => 13     -- Variable
  | .typeVariable => 26 -- TypeParameter
  | .module => 2        -- Module
  | .parameter => 13    -- Variable

/-- Get document symbols for a module, returns top-level definitions -/
def getDocumentSymbols (mod : CompiledModule) : Array DefinitionSite :=
  mod.symbols.allDefinitions.filter fun def_ =>
    def_.kind == .function ||
    def_.kind == .type ||
    def_.kind == .typeAlias ||
    def_.kind == .trait ||
    def_.kind == .constructor

/-- Collect inlay hints for a range in a module -/
def collectInlayHints (mod : CompiledModule) (startOffset endOffset : Nat)
    : Array (Span × String × Bool) := Id.run do
  let mut hints : Array (Span × String × Bool) := #[]
  let globals := mod.globals

  for binding in mod.scopeMap.bindings do
    let bindingOffset := binding.nameSpan.start.byteOffset
    if bindingOffset < startOffset || bindingOffset > endOffset then
      continue

    -- Skip bindings that already have type annotations
    if binding.typeAnnotation.isSome then
      continue

    -- Only show hints for let bindings, pattern variables, and lambda params
    match binding.kind with
    | .letBinding | .patternVariable | .lambdaParam | .parameter =>
      -- Try to resolve the type from Globals
      if let some g := globals then
        if let some qn := g.resolve #[] #[] binding.name then
          if let some info := g.getDef qn then
            let typeStr := valueToString info.type
            hints := hints.push (binding.nameSpan, s!" :: {typeStr}", false)
    | _ => pure ()

  return hints

/-- Information about a function signature for signature help -/
structure SignatureInfo where
  name : String
  fullSignature : String
  parameters : Array (String × String)
  deriving Inhabited

/-- Extract parameter information from a Pi-type chain -/
partial def extractParams (ty : Value) (acc : Array (String × String) := #[]) : Array (String × String) :=
  match ty with
  | .vPi _qty _binder name domain codomain =>
    let paramType := valueToString domain
    let newAcc := acc.push (name, paramType)
    match codomain with
    | .const _ v => extractParams v newAcc
    | .term .. => newAcc
  | _ => acc

/-- Walk up from a node to find the enclosing function application, returning (fnName, argIndex) -/
partial def findEnclosingApp (tree : RedTree) (offset : Nat) (node : RedNode) : Option (String × Nat) :=
  match node.syntaxKind? with
  | some .exprApp =>
    let children := getChildren tree node
    if h : 0 < children.size then
      let fnNode := children[0]
      let argIdx := Id.run do
        let mut idx : Nat := 0
        for i in [1:children.size] do
          if i < children.size then
            let child := children[i]!
            let childSpan := tree.spanOf child
            if offset >= childSpan.start.byteOffset && offset <= childSpan.stop.byteOffset then
              idx := i - 1
        return idx
      let fnName? := fnNode.text? <|> do
        let tokens := getTokens tree fnNode
        tokens[0]?.bind (·.text?)
      fnName?.map (·, argIdx)
    else none
  | _ =>
    match tree.parent? node with
    | some parent => findEnclosingApp tree offset parent
    | none => none

/-- Get signature help at a position (inside function application) -/
def getSignatureHelpAt (offset : Nat) (mod : CompiledModule)
    (_allModules : Array CompiledModule) (seedSymbols : SymbolEnv := {})
    : Option (SignatureInfo × Nat) := do
  let nodeInfo ← findNodeAtPosition offset mod.tree
  let (fnName, argIndex) ← findEnclosingApp mod.tree offset nodeInfo.node

  -- Resolve the function type
  let fnType ← resolveType fnName mod seedSymbols
  let params := extractParams fnType
  guard (!params.isEmpty)

  let fullSig := s!"{fnName} :: {valueToString fnType}"
  some ({ name := fnName, fullSignature := fullSig, parameters := params }, argIndex)
where
  resolveType (name : String) (mod : CompiledModule) (seedSymbols : SymbolEnv) : Option Value :=
    match mod.globals with
    | some globals =>
      let currentNs := mod.name.splitOn "/" |>.toArray
      match resolveViaGlobals globals currentNs #[] name with
      | some info => some info.type
      | none => (lookupInSeedSymbols name seedSymbols).map (·.2)
    | none => (lookupInSeedSymbols name seedSymbols).map (·.2)

end Lsp
