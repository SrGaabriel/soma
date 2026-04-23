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
    |>.filter (·.tokenKind? != some .doubleColon)
    |>.toList
    |>.filterMap (·.text?)
    |> String.intercalate "::"

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
    | .class_ => .trait
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

/-- Assemble the metadata line shown beneath a hover's signature block -/
private def hoverMetadata (kindStr : String) (moduleName : Option String)
    (extra : Option String := none) : String :=
  let modPart := match moduleName with
    | some m => s!" · `{m}`"
    | none => ""
  let extraPart := match extra with
    | some e => s!" · {e}"
    | none => ""
  s!"{kindStr}{modPart}{extraPart}"

/-- Extra "expands to" note for type aliases, shown in the metadata line -/
private def abbrevNote (globals : Option Globals) (abbrevEnv : Option AbbrevEnv)
    (qn : Soma.Core.QualifiedName) : Option String :=
  let _ := globals
  match abbrevEnv with
  | some env =>
    match env.get? qn with
    | some info => some s!"expands to `{valueToString info.expansion}`"
    | none => none
  | none => none

/-- Format hover for a global declaration resolved through Globals -/
def formatGlobalHover (info : GlobalInfo) (abbrevEnv : Option AbbrevEnv := none) : String :=
  let name := info.name.display
  let typeStr := valueToString info.type
  let kindStr := toString (globalInfoToSymbolKind info)
  let moduleName := moduleOfQualifiedName info.name
  let extra := abbrevNote none abbrevEnv info.name
  mkHoverDoc s!"{name} : {typeStr}" (hoverMetadata kindStr (some moduleName) extra)

/-- Format hover for an abbreviation resolved through AbbrevEnv -/
def formatAbbrevHover (name : String) (abbrevInfo : AbbrevInfo) : String :=
  let expansionStr := valueToString abbrevInfo.expansion
  let arityStr := if abbrevInfo.arity > 0 then s!" ({abbrevInfo.arity} parameters)" else ""
  mkHoverDoc s!"alias {name}{arityStr} = {expansionStr}"
    (hoverMetadata "type alias" (some abbrevInfo.abbrevId.module))

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
  let extra : Option String :=
    globals.bind (fun g => g.resolve #[] #[] def_.name)
      |>.bind (abbrevNote globals abbrevEnv)
  let metadata := hoverMetadata kindStr (some def_.moduleName) extra
  match typeStr with
  | some sig => mkHoverDoc s!"{def_.name} : {sig}" metadata
  | none => mkHoverDoc def_.name metadata

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
  mkHoverDoc s!"{sym.name} : {typeStr}" (hoverMetadata kindStr (some sym.module))

/-- Look up a name in seedSymbols -/
def lookupInSeedSymbols (name : String) (seedSymbols : SymbolEnv) : Option (Symbol × Value) :=
  seedSymbols.toArray.find? fun (sym, _) => sym.name == name

/-- Format hover for a keyword -/
def formatKeywordHover (kind : TokenKind) (text : String) : String :=
  let desc := match kind with
    | .kw_def => "Define a function or value."
    | .kw_let => "Introduce a local binding."
    | .kw_in => "Body of a `let` expression."
    | .kw_case => "Pattern matching."
    | .kw_if => "Conditional expression."
    | .kw_then => "`then` branch of an `if` expression."
    | .kw_else => "`else` branch of an `if` expression."
    | .kw_inductive => "Define an inductive type."
    | .kw_struct => "Define a record type."
    | .kw_trait => "Define a type class."
    | .kw_instance => "Define a type class instance."
    | .kw_where => "Begin definition body or constraints."
    | .kw_with => "Add constraints."
    | .kw_use => "Import a module."
    | .kw_pub => "Public visibility modifier."
    | .kw_forall => "Universal quantification."
    | .kw_bind => "Monadic `bind` block."
    | .kw_compose => "Applicative `compose` block."
    | .kw_abbrev => "Define a type alias."
    | .true_ | .false_ => "Boolean literal."
    | _ => kind.describe
  mkHoverDoc text "keyword" (some desc)

/-- Human-readable name for a literal token's type -/
private def literalTypeName (kind : TokenKind) : Option String :=
  match kind with
  | .number => some "Int"
  | .string _ => some "String"
  | .true_ | .false_ => some "Bool"
  | _ => none

/-- Format hover for a literal token with type in the code block, raw value in the docs -/
def formatLiteralHover (kind : TokenKind) (text : String) : Option String := do
  let tyName ← literalTypeName kind
  some (mkHoverDoc tyName "" (some s!"value: `{text}`"))

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

/-- Walk up from a node looking for a `.importPath` ancestor -/
partial def importPathPrefixAt (tree : RedTree) (node : RedNode) : Option (Array String) :=
  go (tree.parent? node)
where
  go : Option RedNode → Option (Array String)
    | none => none
    | some parent =>
      if parent.syntaxKind? == some .importPath then
        Id.run do
          let mut segs : Array String := #[]
          for t in getTokens tree parent do
            match t.tokenKind? with
            | some .lowerIdent | some .upperIdent =>
              if let some txt := t.text? then segs := segs.push txt
              if t.id == node.id then return some segs
            | _ => pure ()
          some segs
      else go (tree.parent? parent)

/-- Walk up from a node to find an enclosing `.attribute` node -/
partial def findAttributeAncestor (tree : RedTree) (node : RedNode) : Option RedNode :=
  match tree.parent? node with
  | none => none
  | some p =>
    if p.syntaxKind? == some .attribute then some p
    else findAttributeAncestor tree p

/-- Short description for a known attribute name -/
def attributeDoc (name : String) : Option String :=
  match name with
  | "extern" => some "Declares an externally-defined function."
  | "intrinsic" => some "Marks a declaration as a compiler intrinsic."
  | "wired_in" => some "Binds this declaration to a well-known compiler role."
  | "total" => some "Asserts that this function terminates on all inputs."
  | "inline" => some "Hint to inline this function at call sites."
  | "noinline" => some "Hint to never inline this function."
  | _ => none

/-- Hover for built-in sorts and universe names that aren't declared anywhere -/
def builtinSortHover (name : String) : Option String :=
  match name with
  | "Type" | "Type0" => some (mkHoverDoc "Type" "sort"
      (some "The universe of ordinary types."))
  | "Type1" => some (mkHoverDoc "Type1" "sort"
      (some "The universe one level above `Type` that contains `Type` itself."))
  | "Row" => some (mkHoverDoc "Row" "sort"
      (some "The sort of row types used by records and variants."))
  | "Label" => some (mkHoverDoc "Label" "sort"
      (some "The sort of record/variant field labels."))
  | _ => none

/-- Get hover information at a position -/
def getHoverAt (offset : Nat) (mod : CompiledModule) (allModules : Array CompiledModule)
    (seedSymbols : SymbolEnv := {}) : Option (String × Span) := do
  let nodeInfo ← findNodeAtPosition offset mod.tree

  guard (!nodeInfo.node.green.isTrivia)
  if nodeInfo.node.syntaxKind? == some .triviaToken then none else

  let span := mod.tree.spanOf nodeInfo.node

  if let some attrNode := findAttributeAncestor mod.tree nodeInfo.node then
    let attrName := (getTokens mod.tree attrNode).findSome? fun t =>
      match t.tokenKind? with
      | some .lowerIdent => t.text?
      | _ => none
    match attrName with
    | some name =>
      return (mkHoverDoc s!"@[{name}]" "attribute" (attributeDoc name), span)
    | none => pure ()

  if nodeInfo.node.isToken then
    let text ← nodeInfo.node.text?
    let kind ← nodeInfo.node.tokenKind?

    if kind.isNameLike then
      if let some hov := builtinSortHover text then
        return (hov, span)
      if let some segs := importPathPrefixAt mod.tree nodeInfo.node then
        let qualified := String.intercalate "::" segs.toList
        return (mkHoverDoc qualified "module", span)
      if let some local_ := mod.scopeMap.resolveByNodeId nodeInfo.node.id then
        return (formatLocalBindingHover local_, span)
      if let some local_ := mod.scopeMap.resolve text offset then
        return (formatLocalBindingHover local_, span)
      if let some globals := mod.globals then
        let currentNs := mod.name.splitOn "::" |>.toArray
        let (qualPath, _qualName) := extractQualifiedPath mod.tree nodeInfo.node
        if let some info := resolveViaGlobals globals currentNs qualPath text then
          return (formatGlobalHover info mod.abbrevEnv, span)
      if let some def_ := mod.symbols.lookupDefinition text then
        return (formatDefinitionHover def_ mod.globals mod.abbrevEnv, span)
      for other in allModules do
        if other.filePath != mod.filePath then
          if let some globals := other.globals then
            let otherNs := other.name.splitOn "::" |>.toArray
            if let some info := resolveViaGlobals globals otherNs #[] text then
              return (formatGlobalHover info other.abbrevEnv, span)
          if let some def_ := other.symbols.lookupDefinition text then
            return (formatDefinitionHover def_ other.globals other.abbrevEnv, span)
      if let some (sym, ty) := lookupInSeedSymbols text seedSymbols then
        return (formatExternalSymbolHover sym ty, span)
      -- Unknown identifier/operator
      return (mkHoverDoc text "unknown identifier", span)
    else if let some lit := formatLiteralHover kind text then
      return (lit, span)
    else if kind.isKeyword then
      return (formatKeywordHover kind text, span)
    else
      none
  else
    match nodeInfo.node.green with
    | .error msg _ _ =>
        some (s!"**Error** at {span.start.line}:{span.start.column}\n\n{msg}", span)
    | .missing expected =>
        some (s!"**Missing** at {span.start.line}:{span.start.column}\n\nExpected: {expected.describe}", span)
    | _ => none

/-- Walk a Syntax.Module and find the span -/
private def findDeclNameSpanInAst (name : String) (mod : Soma.Syntax.Module) : Option Span := Id.run do
  for decl in mod.decls do
    if let some q := decl.name? then
      if q.name == name then return some q.span
    match decl with
    | .inductive _ _ _ ctors _ _ =>
      for ctor in ctors do
        if ctor.name.name == name then return some ctor.name.span
    | .record _ _ _ con fields _ =>
      if con.name == name then return some con.span
      for field in fields do
        match field.name with
        | some q => if q.name == name then return some q.span
        | none => pure ()
    | .trait _ _ _ _ methods _ =>
      for m in methods do
        if m.name.name == name then return some m.name.span
    | _ => pure ()
  none

/-- Find definition location for a name, using Globals as primary source -/
def findDefinitionLocation (name : String) (mod : CompiledModule) (allModules : Array CompiledModule)
    (state : Option LspState := none) (seedSymbols : SymbolEnv := {})
    (qualPath : Array String := #[]) : Option (String × Span) := do
  if let some globals := mod.globals then
    let currentNs := mod.name.splitOn "::" |>.toArray
    if let some info := resolveViaGlobals globals currentNs qualPath name then
      let originModule := info.name.id.module
      if originModule == mod.name then
        if let some def_ := mod.symbols.lookupDefinition name then
          return (def_.filePath, def_.nameSpan)
      for other in allModules do
        if other.name == originModule then
          if let some def_ := other.symbols.lookupDefinition name then
            return (other.filePath, def_.nameSpan)
      -- Fall back to the project-wide CheckedModule AST for unopened files.
      if let some st := state then
        if let some filePath := st.getModulePath originModule then
          if let some checked := st.checkedModules.get? originModule then
            if let some sp := findDeclNameSpanInAst name checked.resolvedAst then
              return (filePath, sp)
            return (filePath, Span.uninhabited)

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
      return (other.filePath, def_.nameSpan)

  -- External dependencies
  if let some (sym, _) := lookupInSeedSymbols name seedSymbols then
    let filePath :=
      state.bind (·.getModulePath sym.module) |>.getD (sym.module ++ ".soma")
    return (filePath, sym.span)

  none

/-- Get definition at a position -/
def getDefinitionAt (offset : Nat) (mod : CompiledModule) (allModules : Array CompiledModule)
    (state : Option LspState := none) (seedSymbols : SymbolEnv := {})
    : Option (String × Span) := do
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
      findDefinitionLocation text mod allModules state seedSymbols qualPath
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
    let displayName := modName.replace "/" "::"
    let keep := partialPath.isEmpty
      || displayName.startsWith partialPath
      || modName.startsWith partialPath
    if keep then
      results := results.push
        { label := displayName, insertText := displayName
        , kind := .module, detail := some "module" }
  return results

/-- Walk up from a node to find the nearest ancestor of a given SyntaxKind -/
partial def findAncestorOfKind (tree : RedTree) (node : RedNode) (kind : SyntaxKind) : Option RedNode :=
  if node.syntaxKind? == some kind then some node
  else match tree.parent? node with
    | some parent => findAncestorOfKind tree parent kind
    | none => none

/-- Extract path segments from an importPath node -/
def extractImportPathSegments (tree : RedTree) (importPathNode : RedNode) : Array String :=
  (getTokens tree importPathNode).filterMap fun t =>
    match t.tokenKind? with
    | some .lowerIdent | some .upperIdent => t.text?
    | _ => none

/-- Extract the partial word ending at `offset` in `source` -/
def extractPartialWord (source : String) (offset : Nat) : String :=
  let before := (source.take offset).toString
  let rev := before.toList.reverse
  let taken := rev.takeWhile fun c => c.isAlphanum || c == '_'
  String.ofList taken.reverse

def parseDotPrefix (source : String) (offset : Nat) : Option (String × String) :=
  let before := (source.take offset).toString
  let rev := before.toList.reverse
  let (partialChars, afterPartial) := rev.span fun c => c.isAlphanum || c == '_'
  match afterPartial with
  | '.' :: restAfterDot =>
    match restAfterDot with
    | '.' :: _ => none
    | _ =>
      let (lhsChars, _) := restAfterDot.span fun c => c.isAlphanum || c == '_'
      if lhsChars.isEmpty then none
      else some (String.ofList lhsChars.reverse, String.ofList partialChars.reverse)
  | _ => none

/-- Detect whether the cursor sits right after a `use` or `pub use` keyword with no path started yet -/
def isAtUseKeyword (source : String) (offset : Nat) : Bool :=
  let rev := ((source.take offset).toString).toList.reverse
  let afterTrailingWs := rev.dropWhile Char.isWhitespace
  match afterTrailingWs with
  | 'e' :: 's' :: 'u' :: rest =>
    -- `use` must be a standalone keyword, not the tail of another identifier.
    match rest with
    | [] => true
    | c :: _ => !(c.isAlphanum || c == '_')
  | _ => false

/-- Source of field information for projection completion -/
inductive FieldSource where
  | anonRecord (recordTy : Value)
  | namedType (qn : Soma.Core.QualifiedName)

/-- Convert an elaborated `Value` type to a `FieldSource` if it names a record -/
private def fieldSourceOfType (ty : Value) : Option FieldSource :=
  match ty with
  | .vRecord _ => some (.anonRecord ty)
  | .vDataType id _ => some (.namedType (Soma.Core.QualifiedName.ofUnique id))
  | _ => none

/-- Resolve a reference name to the source of its fields (for projection completion) -/
def resolveFieldSource (name : String) (offset : Nat) (mod : CompiledModule)
    : Option FieldSource := do
  let globals ← mod.globals
  let currentNs := mod.name.splitOn "::" |>.toArray
  match mod.scopeMap.resolve name offset with
  | some binding =>
    match mod.localTypes.get? binding.nameSpan.start.byteOffset with
    | some ty => fieldSourceOfType ty
    | none =>
      let annot ← binding.typeAnnotation
      let afterWs := annot.toList.dropWhile Char.isWhitespace
      let head := String.ofList (afterWs.takeWhile fun c => c.isAlphanum || c == '_')
      guard (!head.isEmpty)
      let qn ← globals.resolve currentNs #[] head
      some (.namedType qn)
  | none =>
    let info ← resolveViaGlobals globals currentNs #[] name
    fieldSourceOfType info.type

/-- Build completion entries for the fields of a record-like type -/
def getFieldCompletionsFromSource (globals : Globals) (source : FieldSource)
    (partialName : String) : Array CompletionEntry := Id.run do
  let mut results : Array CompletionEntry := #[]
  match source with
  | .anonRecord recordTy =>
    for (fname, fty) in recordTy.recordFields do
      if partialName.isEmpty || fname.startsWith partialName then
        results := results.push
          { label := fname, insertText := fname, kind := .field
          , detail := some (valueToString fty) }
  | .namedType qn =>
    if let some fieldNames := globals.recordFields.get? qn then
      for fname in fieldNames do
        if partialName.isEmpty || fname.startsWith partialName then
          let detail := (globals.getDef qn).map fun info =>
            s!"field of {info.name.display}"
          results := results.push
            { label := fname, insertText := fname, kind := .field, detail }
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
  let nodeAtPos := findNodeAtPosition offset mod.tree
  let context := match nodeAtPos with
    | some nodeInfo => nodeInfo.context
    | none => .unknown

  -- Check for qualified name prefix
  if let some globals := mod.globals then
    let currentNs := mod.name.splitOn "::" |>.toArray

    -- Extract text before cursor using line+col (avoids byte/char offset mismatch)
    let textBeforeCursor : String := match liveContent, cursorLine, cursorCol with
      | some live, some line, some col =>
        let lines := (live.splitOn "\n").toArray
        if h : line < lines.size then
          ((lines[line]).take col).toString
        else ""
      | _, _, _ => ((mod.sourceContent.take offset).toString)
    let cursorPos := textBeforeCursor.length

    let inImportItems := match context with
      | .inImportItems => true
      | _ => false
    if !inImportItems then
      if let some (lhsName, partialField) := parseDotPrefix textBeforeCursor cursorPos then
        if let some source := resolveFieldSource lhsName offset mod then
          return getFieldCompletionsFromSource globals source partialField

    if isAtUseKeyword textBeforeCursor cursorPos then
      if let some st := state then
        return getModulePathCompletions st ""

    let (path, partialName) := parseQualifiedPrefix textBeforeCursor cursorPos
    if !path.isEmpty then
      let relativePath := currentNs.toList ++ path.toList
      if let some ns := globals.root.getAt? relativePath then
        return completionsFromNamespace ns globals partialName
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

    match context with
    | .inImport =>
      if let some st := state then
        return getModulePathCompletions st (extractPartialWord textBeforeCursor cursorPos)
      else return #[]
    | .inImportItems =>
      let partialWord := extractPartialWord textBeforeCursor cursorPos
      match nodeAtPos with
      | some nodeInfo =>
        match findAncestorOfKind mod.tree nodeInfo.node .declUse with
        | some useNode =>
          match findChild? mod.tree useNode .importPath with
          | some pathNode =>
            let segments := extractImportPathSegments mod.tree pathNode
            match globals.root.getAt? segments.toList with
            | some ns => return completionsFromNamespace ns globals partialWord
            | none => return #[]
          | none => return #[]
        | none => return #[]
      | none => return #[]
    | .afterDot _ =>
      return #[]
    | _ =>
      -- Standard completions from Globals
      return getGlobalsCompletionsForContext context globals currentNs mod.abbrevEnv

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

/-- Find references in a module whose name tokens resolve to `targetQN` through the module's `Globals` -/
def findGlobalReferencesInModule (mod : CompiledModule) (targetQN : Soma.Core.QualifiedName)
    (name : String) : Array Span := Id.run do
  let some globals := mod.globals | return #[]
  let currentNs := mod.name.splitOn "::" |>.toArray
  mod.tree.nodes.filterMap fun node => do
    guard node.isToken
    let kind ← node.tokenKind?
    guard kind.isNameLike
    let text ← node.text?
    guard (text == name)
    let span := mod.tree.spanOf node
    let offset := span.start.byteOffset
    if (mod.scopeMap.resolve text offset).isSome then none
    else
      let (qualPath, _) := extractQualifiedPath mod.tree node
      match resolveViaGlobals globals currentNs qualPath text with
      | some info => if info.name == targetQN then some span else none
      | none => none

/-- Entry point for `textDocument/references` -/
def findReferencesForCursor (originMod : CompiledModule) (offset : Nat) (name : String)
    (allModules : Array CompiledModule) : Array (String × Span) := Id.run do
  if let some local_ := resolveLocalBinding name offset originMod then
    let refs := originMod.scopeMap.findLocalReferences local_ originMod.tree
    return refs.map (originMod.filePath, ·)

  if let some globals := originMod.globals then
    let currentNs := originMod.name.splitOn "::" |>.toArray
    let qualPath : Array String := match findNodeAtPosition offset originMod.tree with
      | some nodeInfo => (extractQualifiedPath originMod.tree nodeInfo.node).1
      | none => #[]
    if let some info := resolveViaGlobals globals currentNs qualPath name then
      let targetQN := info.name
      return allModules.foldl (init := #[]) fun acc mod =>
        let refs := findGlobalReferencesInModule mod targetQN name
        acc ++ refs.map (mod.filePath, ·)

  (originMod.symbols.getReferences name).map (fun r => (originMod.filePath, r.span))

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
      let currentNs := mod.name.splitOn "::" |>.toArray
      match resolveViaGlobals globals currentNs #[] name with
      | some info => some info.type
      | none => (lookupInSeedSymbols name seedSymbols).map (·.2)
    | none => (lookupInSeedSymbols name seedSymbols).map (·.2)

end Lsp
