import Std.Data.HashMap
import Soma.Syntax
import Lsp.Cst

namespace Lsp

open Std
open Soma.Syntax

/-- The kind of a local binding -/
inductive LocalBindingKind where
  | parameter
  | lambdaParam
  | letBinding
  | patternVariable
  | typeVariable
  | piBinder
  | sigmaBinder
  | composeLetVar
  | composeBindVar
  | inductiveTypeParam
  | constructorField
  deriving BEq, Repr, Inhabited


/-- Human-readable description for hover -/
def LocalBindingKind.describe : LocalBindingKind → String
  | .parameter         => "parameter"
  | .lambdaParam       => "lambda parameter"
  | .letBinding        => "local binding"
  | .patternVariable   => "pattern variable"
  | .typeVariable      => "type variable"
  | .piBinder          => "dependent type binder"
  | .sigmaBinder       => "dependent pair binder"
  | .composeLetVar     => "local binding"
  | .composeBindVar    => "bound variable"
  | .inductiveTypeParam => "type parameter"
  | .constructorField   => "constructor field"

/-- A local binding with its visibility interval -/
structure LocalBinding where
  name : String
  kind : LocalBindingKind
  bindingNodeId : NodeId
  nameSpan : Span
  typeAnnotation : Option String := none
  scopeStart : Nat
  scopeEnd : Nat
  deriving Repr, Inhabited

/-- The scope map for a module: flat array of bindings with indexed lookups -/
structure ScopeMap where
  bindings : Array LocalBinding := #[]
  nameIndex : HashMap String (Array Nat) := {}
  nodeIdIndex : HashMap NodeId Nat := {}
  deriving Inhabited

namespace ScopeMap

def empty : ScopeMap := {}

/-- Resolve a name at a byte offset to the innermost binding -/
def resolve (sm : ScopeMap) (name : String) (offset : Nat) : Option LocalBinding := Id.run do
  let indices := sm.nameIndex.getD name #[]
  let mut best : Option LocalBinding := none
  let mut bestSize : Nat := 0
  for idx in indices do
    if h : idx < sm.bindings.size then
      let b := sm.bindings[idx]
      if offset >= b.scopeStart && offset < b.scopeEnd then
        let size := b.scopeEnd - b.scopeStart
        match best with
        | none =>
          best := some b
          bestSize := size
        | some _ =>
          if size < bestSize then
            best := some b
            bestSize := size
  return best

/-- Look up a binding by its binding-site node ID (for definition-site classification) -/
def resolveByNodeId (sm : ScopeMap) (nodeId : NodeId) : Option LocalBinding := do
  let idx ← sm.nodeIdIndex.get? nodeId
  if h : idx < sm.bindings.size then some sm.bindings[idx] else none

/-- All bindings visible at a given offset -/
def visibleAt (sm : ScopeMap) (offset : Nat) : Array LocalBinding :=
  sm.bindings.filter fun b =>
    offset >= b.scopeStart && offset < b.scopeEnd

/-- Find all references to a specific local binding in the tree -/
def findLocalReferences (sm : ScopeMap) (binding : LocalBinding)
    (tree : RedTree) : Array Span :=
  tree.nodes.filterMap fun node => do
    guard node.isToken
    let kind ← node.tokenKind?
    guard kind.isNameLike
    let text ← node.text?
    guard (text == binding.name)
    let span := tree.spanOf node
    let offset := span.start.byteOffset
    -- Check if this is the binding site itself
    if node.id == binding.bindingNodeId then
      return span
    let resolved? := sm.resolve text offset
    match resolved? with
    | some resolved =>
      guard (resolved.bindingNodeId == binding.bindingNodeId)
      some span
    | none => none

end ScopeMap

/-- Extract type annotation text from a .field node's type child -/
private def extractFieldTypeText (tree : RedTree) (fieldNode : RedNode) : Option String :=
  let tokens := getTokens tree fieldNode
  -- Find the colon, everything after it (before rparen) is the type
  let tokenList := tokens.toList
  let afterColon := tokenList.dropWhile fun t =>
    t.tokenKind? != some .colon
  match afterColon with
  | _ :: rest =>
    -- Drop the trailing rparen/rbrace if present
    let typeTokens := rest.filter fun t =>
      t.tokenKind? != some .rightParen && t.tokenKind? != some .rightBrace
    if typeTokens.isEmpty then none
    else some (String.intercalate " " (typeTokens.filterMap (·.text?)))
  | [] => none

/-- Walk up through triviaToken wrappers to find the semantic parent -/
private partial def semanticParent? (tree : RedTree) (node : RedNode) : Option RedNode :=
  match tree.parent? node with
  | none => none
  | some p =>
    if p.syntaxKind? == some .triviaToken then semanticParent? tree p
    else some p

/-- Recursively collect all patVar names from a pattern subtree -/
private def collectPatternVarNames (tree : RedTree) (node : RedNode)
    : Array (String × RedNode) := Id.run do
  let mut result : Array (String × RedNode) := #[]
  -- Walk all descendant tokens
  let startIdx := node.selfIdx
  let endIdx := startIdx + RedTree.countGreenNodes node.green
  for h : i in [startIdx:endIdx] do
    if hi : i < tree.nodes.size then
      let n := tree.nodes[i]
      if n.tokenKind? == some .lowerIdent then
        -- Check if parent is a pattern (patVar, patAs, patTyped)
        if let some parent := semanticParent? tree n then
          match parent.syntaxKind? with
          | some .patVar | some .patAs | some .patTyped =>
            if let some text := n.text? then
              result := result.push (text, n)
          | _ => pure ()
  return result

/-- Find the arrow/fatArrow token in a node's children -/
private def findArrowToken (tree : RedTree) (node : RedNode) : Option RedNode :=
  let tokens := getTokens tree node
  tokens.find? fun t =>
    t.tokenKind? == some .fatArrow || t.tokenKind? == some .arrow

/-- Find the dot token in a node's children -/
private def findDotToken (tree : RedTree) (node : RedNode) : Option RedNode :=
  let tokens := getTokens tree node
  tokens.find? fun t => t.tokenKind? == some .dot

/-- Extract bindings from a declDef's paramList -/
private def extractDefParamBindings (tree : RedTree) (defNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  let children := getChildren tree defNode
  let defEnd := (tree.spanOf defNode).stop.byteOffset

  if let some paramListNode := children.find? (fun c => c.syntaxKind? == some .paramList) then
    let scopeStart := (tree.spanOf paramListNode).start.byteOffset
    let paramChildren := getChildren tree paramListNode
    for field in paramChildren do
      if field.syntaxKind? == some .field then
        if let some nameTok := findToken? tree field .lowerIdent then
          if let some name := nameTok.text? then
            let typeAnnot := extractFieldTypeText tree field
            result := result.push {
              name
              kind := .parameter
              bindingNodeId := nameTok.id
              nameSpan := tree.spanOf nameTok
              typeAnnotation := typeAnnot
              scopeStart
              scopeEnd := defEnd
            }
      else if field.syntaxKind? == some .patVar then
        -- Untyped parameter: (bare name without parens)
        if let some nameTok := findToken? tree field .lowerIdent then
          if let some name := nameTok.text? then
            result := result.push {
              name
              kind := .parameter
              bindingNodeId := nameTok.id
              nameSpan := tree.spanOf nameTok
              scopeStart
              scopeEnd := defEnd
            }
  return result

/-- Extract bindings from a defClause's patterns -/
private def extractDefClauseBindings (tree : RedTree) (clauseNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  -- Scope: from the arrow to clause end
  if let some arrowTok := findArrowToken tree clauseNode then
    let scopeStart := (tree.spanOf arrowTok).stop.byteOffset
    let scopeEnd := (tree.spanOf clauseNode).stop.byteOffset
    -- Collect pattern variables before the arrow
    let children := getChildren tree clauseNode
    for child in children do
      -- Stop at the arrow
      if child.tokenKind? == some .fatArrow || child.tokenKind? == some .arrow then
        break
      -- Collect patVars from pattern children
      let vars := collectPatternVarNames tree child
      for (name, nameTok) in vars do
        result := result.push {
          name
          kind := .patternVariable
          bindingNodeId := nameTok.id
          nameSpan := tree.spanOf nameTok
          scopeStart
          scopeEnd
        }
  return result

/-- Extract bindings from a lambda expression -/
private def extractLambdaBindings (tree : RedTree) (lambdaNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  let lambdaEnd := (tree.spanOf lambdaNode).stop.byteOffset

  -- Scope: from the arrow to lambda end
  if let some arrowTok := findArrowToken tree lambdaNode then
    let scopeStart := (tree.spanOf arrowTok).stop.byteOffset
    let children := getChildren tree lambdaNode
    for child in children do
      -- Stop at the arrow
      if child.tokenKind? == some .fatArrow || child.tokenKind? == some .arrow then
        break
      match child.syntaxKind? with
      | some .paramList =>
        -- Typed or grouped params
        let paramChildren := getChildren tree child
        for param in paramChildren do
          if param.syntaxKind? == some .field then
            if let some nameTok := findToken? tree param .lowerIdent then
              if let some name := nameTok.text? then
                let typeAnnot := extractFieldTypeText tree param
                result := result.push {
                  name
                  kind := .lambdaParam
                  bindingNodeId := nameTok.id
                  nameSpan := tree.spanOf nameTok
                  typeAnnotation := typeAnnot
                  scopeStart
                  scopeEnd := lambdaEnd
                }
          else if param.syntaxKind? == some .patVar then
            if let some nameTok := findToken? tree param .lowerIdent then
              if let some name := nameTok.text? then
                result := result.push {
                  name
                  kind := .lambdaParam
                  bindingNodeId := nameTok.id
                  nameSpan := tree.spanOf nameTok
                  scopeStart
                  scopeEnd := lambdaEnd
                }
      | some .patVar =>
        -- Bare untyped param
        if let some nameTok := findToken? tree child .lowerIdent then
          if let some name := nameTok.text? then
            result := result.push {
              name
              kind := .lambdaParam
              bindingNodeId := nameTok.id
              nameSpan := tree.spanOf nameTok
              scopeStart
              scopeEnd := lambdaEnd
            }
      | _ => pure ()
  return result

/-- Extract bindings from a let expression -/
private def extractLetBindings (tree : RedTree) (letNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  let letEnd := (tree.spanOf letNode).stop.byteOffset
  let children := getChildren tree letNode

  let tokens := getTokens tree letNode
  let inTok := tokens.find? fun t => t.tokenKind? == some .kw_in

  -- Scope start: after `in` if present, otherwise after the value expression
  let scopeStart := match inTok with
    | some tok => (tree.spanOf tok).stop.byteOffset
    | none =>
      -- Find the = token and the value after it
      match tokens.find? (fun t => t.tokenKind? == some .equals) with
      | some eqTok => (tree.spanOf eqTok).stop.byteOffset
      | none => (tree.spanOf letNode).start.byteOffset

  -- The binding is the second child (after `let` keyword)
  if h : 1 < children.size then
    let bindingChild := children[1]
    if bindingChild.isToken && bindingChild.tokenKind? == some .lowerIdent then
      -- Simple name binding
      if let some name := bindingChild.text? then
        -- Look for type annotation
        let sigNode := findChild? tree letNode .signature
        let typeAnnot := sigNode.map (extractSignatureText tree ·)
        result := result.push {
          name
          kind := .letBinding
          bindingNodeId := bindingChild.id
          nameSpan := tree.spanOf bindingChild
          typeAnnotation := typeAnnot
          scopeStart
          scopeEnd := letEnd
        }
    else
      -- Pattern binding so we collect all patVars
      let vars := collectPatternVarNames tree bindingChild
      for (name, nameTok) in vars do
        result := result.push {
          name
          kind := .letBinding
          bindingNodeId := nameTok.id
          nameSpan := tree.spanOf nameTok
          scopeStart
          scopeEnd := letEnd
        }
  return result

/-- Extract bindings from a match arm's patterns -/
private def extractMatchArmBindings (tree : RedTree) (armNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  if let some arrowTok := findArrowToken tree armNode then
    let scopeStart := (tree.spanOf arrowTok).stop.byteOffset
    let scopeEnd := (tree.spanOf armNode).stop.byteOffset
    let children := getChildren tree armNode
    for child in children do
      if child.tokenKind? == some .fatArrow || child.tokenKind? == some .arrow then
        break
      -- Skip the leading pipe token
      if child.tokenKind? == some .pipe then
        continue
      let vars := collectPatternVarNames tree child
      for (name, nameTok) in vars do
        result := result.push {
          name
          kind := .patternVariable
          bindingNodeId := nameTok.id
          nameSpan := tree.spanOf nameTok
          scopeStart
          scopeEnd
        }
  return result

/-- Extract type variable names from a tyParamList -/
private def extractTyParamNames (tree : RedTree) (tyParamListNode : RedNode)
    : Array (String × RedNode × Option String) := Id.run do
  let mut result : Array (String × RedNode × Option String) := #[]
  let children := getChildren tree tyParamListNode
  for child in children do
    match child.syntaxKind? with
    | some .typeVar =>
      -- Simple type variable
      if let some nameTok := findToken? tree child .lowerIdent then
        if let some name := nameTok.text? then
          result := result.push (name, nameTok, none)
    | some .tyParamKinded =>
      -- Kinded type parameter (a : Kind)
      if let some nameTok := findToken? tree child .lowerIdent then
        if let some name := nameTok.text? then
          -- Extract kind annotation
          let typeAnnot := extractFieldTypeText tree child
          result := result.push (name, nameTok, typeAnnot)
    | some .triviaToken =>
      if let some nameTok := findToken? tree child .lowerIdent then
        if let some name := nameTok.text? then
          result := result.push (name, nameTok, none)
    | _ =>
      -- Could be a bare lowerIdent token
      if child.isToken && child.tokenKind? == some .lowerIdent then
        if let some name := child.text? then
          result := result.push (name, child, none)
  return result

/-- Extract bindings from a forall type -/
private def extractForallBindings (tree : RedTree) (forallNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  let forallEnd := (tree.spanOf forallNode).stop.byteOffset
  let children := getChildren tree forallNode

  -- Find the dot token — scope starts after it
  let dotTok := (getTokens tree forallNode).find? fun t =>
    t.tokenKind? == some .dot
  -- If no dot, scope starts after tyParamList
  let scopeStart := match dotTok with
    | some tok => (tree.spanOf tok).stop.byteOffset
    | none =>
      -- Find tyParamList end
      match children.find? (fun c => c.syntaxKind? == some .tyParamList) with
      | some tpl => (tree.spanOf tpl).stop.byteOffset
      | none => (tree.spanOf forallNode).start.byteOffset

  if let some tyParamList := children.find? (fun c => c.syntaxKind? == some .tyParamList) then
    let params := extractTyParamNames tree tyParamList
    for (name, nameTok, typeAnnot) in params do
      result := result.push {
        name
        kind := .typeVariable
        bindingNodeId := nameTok.id
        nameSpan := tree.spanOf nameTok
        typeAnnotation := typeAnnot
        scopeStart
        scopeEnd := forallEnd
      }
  return result

/-- Extract the binder name from a typePiBinder node -/
private def extractPiBinderName (tree : RedTree) (binderNode : RedNode)
    : Option (String × RedNode × Option String) := do
  -- typePiBinder structure: [quantity?, typeVar/name, colon, domain]
  let nameTok ← findToken? tree binderNode .lowerIdent
  let name ← nameTok.text?
  let typeAnnot := extractFieldTypeText tree binderNode
  some (name, nameTok, typeAnnot)

/-- Extract bindings from a Pi type -/
private def extractPiBindings (tree : RedTree) (piNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  let piEnd := (tree.spanOf piNode).stop.byteOffset

  if let some arrowTok := findArrowToken tree piNode then
    let scopeStart := (tree.spanOf arrowTok).stop.byteOffset
    let children := getChildren tree piNode
    for child in children do
      if child.syntaxKind? == some .typePiBinder then
        if let some (name, nameTok, typeAnnot) := extractPiBinderName tree child then
          result := result.push {
            name
            kind := .piBinder
            bindingNodeId := nameTok.id
            nameSpan := tree.spanOf nameTok
            typeAnnotation := typeAnnot
            scopeStart
            scopeEnd := piEnd
          }
  return result

/-- Extract bindings from a Sigma type -/
private def extractSigmaBindings (tree : RedTree) (sigmaNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  let sigmaEnd := (tree.spanOf sigmaNode).stop.byteOffset

  -- Find the × token, scope starts after it
  let timesTok := (getTokens tree sigmaNode).find? fun t =>
    t.tokenKind? == some .times
  if let some tok := timesTok then
    let scopeStart := (tree.spanOf tok).stop.byteOffset
    let children := getChildren tree sigmaNode
    for child in children do
      if child.syntaxKind? == some .typePiBinder then
        if let some (name, nameTok, typeAnnot) := extractPiBinderName tree child then
          result := result.push {
            name
            kind := .sigmaBinder
            bindingNodeId := nameTok.id
            nameSpan := tree.spanOf nameTok
            typeAnnotation := typeAnnot
            scopeStart
            scopeEnd := sigmaEnd
          }
  return result

/-- Extract bindings from a compose block's let/bind statements -/
private def extractComposeBindings (tree : RedTree) (composeNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  let composeEnd := (tree.spanOf composeNode).stop.byteOffset
  let children := getChildren tree composeNode

  for child in children do
    match child.syntaxKind? with
    | some .composeLetStmt =>
      let stmtEnd := (tree.spanOf child).stop.byteOffset
      let stmtChildren := getChildren tree child
      -- Structure: [let, name/pattern, =, value]
      if h : 1 < stmtChildren.size then
        let bindingChild := stmtChildren[1]
        if bindingChild.isToken && bindingChild.tokenKind? == some .lowerIdent then
          if let some name := bindingChild.text? then
            result := result.push {
              name
              kind := .composeLetVar
              bindingNodeId := bindingChild.id
              nameSpan := tree.spanOf bindingChild
              scopeStart := stmtEnd
              scopeEnd := composeEnd
            }
        else
          let vars := collectPatternVarNames tree bindingChild
          for (name, nameTok) in vars do
            result := result.push {
              name
              kind := .composeLetVar
              bindingNodeId := nameTok.id
              nameSpan := tree.spanOf nameTok
              scopeStart := stmtEnd
              scopeEnd := composeEnd
            }
    | some .composeBindStmt =>
      let stmtEnd := (tree.spanOf child).stop.byteOffset
      let stmtChildren := getChildren tree child
      -- Structure: [bind, name/pattern, <-, value]
      if h : 1 < stmtChildren.size then
        let bindingChild := stmtChildren[1]
        if bindingChild.isToken && bindingChild.tokenKind? == some .lowerIdent then
          if let some name := bindingChild.text? then
            result := result.push {
              name
              kind := .composeBindVar
              bindingNodeId := bindingChild.id
              nameSpan := tree.spanOf bindingChild
              scopeStart := stmtEnd
              scopeEnd := composeEnd
            }
        else
          let vars := collectPatternVarNames tree bindingChild
          for (name, nameTok) in vars do
            result := result.push {
              name
              kind := .composeBindVar
              bindingNodeId := nameTok.id
              nameSpan := tree.spanOf nameTok
              scopeStart := stmtEnd
              scopeEnd := composeEnd
            }
    | _ => pure ()
  return result

/-- Extract type parameter bindings from an inductive/struct/trait declaration -/
private def extractDeclTypeParamBindings (tree : RedTree) (declNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  let declEnd := (tree.spanOf declNode).stop.byteOffset
  let children := getChildren tree declNode

  if let some tyParamList := children.find? (fun c => c.syntaxKind? == some .tyParamList) then
    let scopeStart := (tree.spanOf tyParamList).start.byteOffset
    let params := extractTyParamNames tree tyParamList
    for (name, nameTok, typeAnnot) in params do
      result := result.push {
        name
        kind := .inductiveTypeParam
        bindingNodeId := nameTok.id
        nameSpan := tree.spanOf nameTok
        typeAnnotation := typeAnnot
        scopeStart
        scopeEnd := declEnd
      }
  return result

/-- Extract bindings from an implicit type parameter -/
private def extractImplicitBindings (tree : RedTree) (implNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  let implEnd := (tree.spanOf implNode).stop.byteOffset

  if let some arrowTok := findArrowToken tree implNode then
    let scopeStart := (tree.spanOf arrowTok).stop.byteOffset
    let children := getChildren tree implNode
    for child in children do
      if child.syntaxKind? == some .typePiBinder then
        if let some (name, nameTok, typeAnnot) := extractPiBinderName tree child then
          result := result.push {
            name
            kind := .piBinder
            bindingNodeId := nameTok.id
            nameSpan := tree.spanOf nameTok
            typeAnnotation := typeAnnot
            scopeStart
            scopeEnd := implEnd
          }
  return result

/-- Extract field bindings from a constructor or constructorSig node -/
private def extractConstructorFieldBindings (tree : RedTree) (consNode : RedNode)
    : Array LocalBinding := Id.run do
  let mut result : Array LocalBinding := #[]
  let consEnd := (tree.spanOf consNode).stop.byteOffset
  let children := getChildren tree consNode

  for child in children do
    if child.syntaxKind? == some .field then
      let scopeStart := (tree.spanOf child).start.byteOffset
      if let some nameTok := findToken? tree child .lowerIdent then
        if let some name := nameTok.text? then
          let typeAnnot := extractFieldTypeText tree child
          result := result.push {
            name
            kind := .constructorField
            bindingNodeId := nameTok.id
            nameSpan := tree.spanOf nameTok
            typeAnnotation := typeAnnot
            scopeStart
            scopeEnd := consEnd
          }
  return result

/-- Build a ScopeMap from a RedTree by walking the CST -/
def buildScopeMap (tree : RedTree) : ScopeMap := Id.run do
  let mut bindings : Array LocalBinding := #[]

  for node in tree.nodes do
    match node.syntaxKind? with
    | some .declDef      => bindings := bindings ++ extractDefParamBindings tree node
    | some .defClause    => bindings := bindings ++ extractDefClauseBindings tree node
    | some .exprLambda   => bindings := bindings ++ extractLambdaBindings tree node
    | some .exprLet      => bindings := bindings ++ extractLetBindings tree node
    | some .matchArm     => bindings := bindings ++ extractMatchArmBindings tree node
    | some .typeForall    => bindings := bindings ++ extractForallBindings tree node
    | some .typePi        => bindings := bindings ++ extractPiBindings tree node
    | some .typeSigma     => bindings := bindings ++ extractSigmaBindings tree node
    | some .exprCompose   => bindings := bindings ++ extractComposeBindings tree node
    | some .declInductive => bindings := bindings ++ extractDeclTypeParamBindings tree node
    | some .declStruct    => bindings := bindings ++ extractDeclTypeParamBindings tree node
    | some .declTrait     => bindings := bindings ++ extractDeclTypeParamBindings tree node
    | some .typeImplicit  => bindings := bindings ++ extractImplicitBindings tree node
    | some .constructor    => bindings := bindings ++ extractConstructorFieldBindings tree node
    | some .constructorSig => bindings := bindings ++ extractConstructorFieldBindings tree node
    | _ => pure ()

  -- Sort by scopeStart for deterministic ordering
  let sorted := bindings.qsort (fun a b => a.scopeStart < b.scopeStart)

  -- Build indices
  let mut nameIdx : HashMap String (Array Nat) := {}
  let mut nodeIdIdx : HashMap NodeId Nat := {}
  for h : i in [:sorted.size] do
    let b := sorted[i]
    let existing := nameIdx.getD b.name #[]
    nameIdx := nameIdx.insert b.name (existing.push i)
    nodeIdIdx := nodeIdIdx.insert b.bindingNodeId i

  return { bindings := sorted, nameIndex := nameIdx, nodeIdIndex := nodeIdIdx }

/-- Format hover content for a local binding -/
def formatLocalBindingHover (b : LocalBinding) : String :=
  let kindStr := b.kind.describe
  match b.typeAnnotation with
  | some ty => s!"```soma\n{b.name} :: {ty}\n```\n\n*{kindStr}*"
  | none    => s!"**{b.name}**\n\n*{kindStr}*"

end Lsp
