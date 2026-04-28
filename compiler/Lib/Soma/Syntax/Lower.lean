import Soma.Syntax.Source
import Soma.Syntax.Diagnostic
import Soma.Syntax.SyntaxKind
import Soma.Syntax.GreenTree
import Soma.Syntax.RedTree
import Soma.Syntax.Ast
import Soma.Core.Quantity

namespace Soma.Syntax

open Soma.Core (Quantity)

/-- Context for lowering -/
structure LowerContext where
  source : SourceFile
  redTree : RedTree

/-- Lowering state - accumulates diagnostics -/
structure LowerState where
  diagnostics : Diagnostics := #[]

/-- Lowering monad - infallible, accumulates diagnostics -/
abbrev LowerM := ReaderT LowerContext (StateT LowerState Id)

/-- Run the lowering monad -/
def LowerM.run' (m : LowerM α) (ctx : LowerContext) : α × Diagnostics :=
  let (result, state) := (m.run ctx).run {}
  (result, state.diagnostics)

/-- Record a diagnostic -/
def recordDiag (d : Diagnostic) : LowerM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics.push d }

/-- Record an error and continue -/
def lowerError (msg : String) (span : Span) : LowerM Unit :=
  recordDiag (Diagnostic.error msg span)

/-- Get a default span from context -/
def defaultSpan : LowerM Span := do
  let ctx ← read
  pure (Span.point (SourceLoc.fromOffset ctx.source 0))

/-- Unwrap a triviaToken node to get the actual token (last child) or it as-is. -/
def unwrapTrivia (green : GreenNode) : GreenNode :=
  if green.syntaxKind? == some .triviaToken then
    -- The actual token is the last child (after trivia)
    if h : 0 < green.children.size then
      green.children[green.children.size - 1]'(by omega)
    else green
  else green

/-- Get the offset adjustment for a triviaToken (sum of trivia widths before the actual token) -/
def triviaOffset (green : GreenNode) : Nat :=
  if green.syntaxKind? == some .triviaToken then
    -- Sum widths of all children except the last (which is the actual token)
    if green.children.size > 1 then
      let triviaChildren := green.children.toList.dropLast
      triviaChildren.foldl (fun acc c => acc + c.width) 0
    else 0
  else 0

/-- Get the leading trivia offset for any node by recursively checking first children -/
partial def leadingTriviaOffset (green : GreenNode) : Nat :=
  if green.syntaxKind? == some .triviaToken then
    triviaOffset green
  else if green.children.size > 0 then
    leadingTriviaOffset green.children[0]!
  else 0

/-- Compute span for a green node given its offset, adjusting for leading trivia -/
def spanFor (green : GreenNode) (offset : Nat) : LowerM Span := do
  let ctx ← read
  let triviaAdj := leadingTriviaOffset green
  let adjustedOffset := offset + triviaAdj
  let adjustedWidth := green.width - triviaAdj
  pure (Span.fromOffsets ctx.source adjustedOffset (adjustedOffset + adjustedWidth))

/-- Get the token kind, unwrapping triviaToken if necessary -/
def getTokenKind (green : GreenNode) : Option TokenKind :=
  (unwrapTrivia green).tokenKind?

/-- Check if a node is a token of a specific kind (unwrapping trivia) -/
def isTokenKind (green : GreenNode) (kind : TokenKind) : Bool :=
  getTokenKind green == some kind

/-- Check if a node is a string token -/
def isStringToken (green : GreenNode) : Bool :=
  match getTokenKind green with
  | some (.string _) => true
  | _ => false

/-- Get the token text, unwrapping triviaToken if necessary -/
def getTokenText (green : GreenNode) : Option String :=
  (unwrapTrivia green).text?

/-- Get the token text from a green node (with error handling) -/
def getGreenTokenText (green : GreenNode) (offset : Nat) : LowerM String := do
  let unwrapped := unwrapTrivia green
  match unwrapped with
  | .token _ text => pure text
  | _ =>
    let span ← spanFor green offset
    lowerError s!"expected token, got interior node" span
    pure "_error"

/-- Get the first child of a green node -/
def firstGreenChild (green : GreenNode) : Option GreenNode :=
  if h : 0 < green.children.size then some green.children[0] else none

/-- Check if a node is a "semantic" node that should be processed during lowering -/
def isSemanticNode (green : GreenNode) : Bool :=
  if green.isTrivia then false
  else if green.isToken || green.syntaxKind? == some .triviaToken then
    -- Operators (.varSymbol) are NOT semantic since they are handled specially in exprInfix
    match getTokenKind green with
    | some .lowerIdent | some .upperIdent | some .number | some .true_ | some .false_ => true
    | some (.string _) => true
    | _ => false  -- punctuation, keywords, and operators are not semantic nodes
  else true  -- regular syntax nodes are semantic

/-- Filter children to get only semantic nodes (syntax nodes, not tokens/punctuation) -/
def syntaxGreenChildren (green : GreenNode) : Array GreenNode :=
  green.children.filter isSemanticNode

/-- Get children of a specific kind -/
def childrenOfGreenKind (green : GreenNode) (kind : SyntaxKind) : Array GreenNode :=
  green.children.filter fun c => c.syntaxKind? == some kind

/-- Iterate children with their offsets (includes all children for correct offset calculation) -/
def childrenWithOffsets (green : GreenNode) (baseOffset : Nat) : Array (GreenNode × Nat) := Id.run do
  let mut result := #[]
  let mut offset := baseOffset
  for child in green.children do
    if child.syntaxKind? == some .triviaToken then
      let adjustedOffset := offset + triviaOffset child
      let unwrapped := unwrapTrivia child
      result := result.push (unwrapped, adjustedOffset)
    else
      result := result.push (child, offset)
    offset := offset + child.width
  return result

/-- Filter children to find tokens of a specific kind (unwrapping trivia) -/
def tokensOfKind (green : GreenNode) (kind : TokenKind) : Array GreenNode :=
  green.children.filter fun c => isTokenKind c kind

/-- Lower a CST qualified name to a split (path, name) pair -/
def lowerQualifiedName (green : GreenNode) (offset : Nat) : LowerM (Array String × String) := do
  if green.isToken then
    let text ← getGreenTokenText green offset
    return (#[], text)
  let kidsWithOffsets := childrenWithOffsets green offset
  let mut parts : Array String := #[]
  for (c, o) in kidsWithOffsets do
    if isTokenKind c .lowerIdent || isTokenKind c .upperIdent then
      parts := parts.push (← getGreenTokenText c o)
  if parts.isEmpty then
    let text ← getGreenTokenText green offset
    return (#[], text)
  else if parts.size == 1 then
    return (#[], parts[0]!)
  else
    return (parts[0:parts.size-1].toArray, parts[parts.size-1]!)

mutual

/-- Lower a CST pattern to AST Pattern -/
partial def lowerPattern (green : GreenNode) (offset : Nat) : LowerM Pattern := do
  -- For triviaToken, recurse immediately with adjusted offset (don't compute span yet)
  if green.syntaxKind? == some .triviaToken then
    let unwrapped := unwrapTrivia green
    let adjustedOffset := offset + triviaOffset green
    return ← lowerPattern unwrapped adjustedOffset

  let span ← spanFor green offset

  match green with
  | .token kind text =>
      match kind with
      | .lowerIdent => pure (.var ⟨#[], text, span⟩)
      | .underscore => pure (.wildcard span)
      | .number => pure (.lit (.int text.toInt! span))
      | .string s => pure (.lit (.string s span))
      | .true_ => pure (.lit (.bool true span))
      | .false_ => pure (.lit (.bool false span))
      | _ =>
          lowerError s!"unexpected token in pattern: {kind}" span
          pure (.wildcard span)

  | .node .triviaToken _ _ =>
      -- Already handled above, but need this case for exhaustiveness
      pure (.wildcard span)

  | .node kind _ _ =>
      match kind with
      | .patVar =>
          match firstGreenChild green with
          | some child =>
              let text ← getGreenTokenText child offset
              pure (.var ⟨#[], text, span⟩)
          | none =>
              lowerError "pattern variable missing name" span
              pure (.wildcard span)

      | .patWildcard =>
          pure (.wildcard span)

      | .patLit =>
          match firstGreenChild green with
          | some child => lowerPattern child offset
          | none =>
              lowerError "pattern literal missing value" span
              pure (.wildcard span)

      | .patCon =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "constructor pattern missing name" span
            pure (.wildcard span)
          else
            let (nameNode, nameOffset) := kidsWithOffsets[0]!
            let (path, name) ← lowerQualifiedName nameNode nameOffset
            let nameSpan ← spanFor nameNode nameOffset
            let args ← kidsWithOffsets[1:].toArray.mapM fun (c, o) => lowerPattern c o
            pure (.con ⟨path, name, nameSpan⟩ args span)

      | .patTuple =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          let elems ← kidsWithOffsets.mapM fun (c, o) => lowerPattern c o
          pure (.tuple elems span)

      | .patList =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          let elems ← kidsWithOffsets.mapM fun (c, o) => lowerPattern c o
          pure (.list elems span)

      | .patCons =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size >= 2 then
            let head ← lowerPattern kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let tail ← lowerPattern kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            pure (.cons head tail span)
          else
            lowerError "cons pattern requires head and tail" span
            pure (.wildcard span)

      | .patParens =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            pure (.tuple #[] span)
          else
            let inner ← lowerPattern kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            pure (.parens inner span)

      | .patTyped =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size >= 2 then
            let pat ← lowerPattern kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let ty ← lowerTypeExpr kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            pure (.typed pat ty span)
          else if kidsWithOffsets.size == 1 then
            lowerPattern kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
          else
            lowerError "typed pattern missing pattern and type" span
            pure (.wildcard span)

      | .patVariant =>
          -- Structure: [dot, labelToken, optionalArgPattern]
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "variant pattern missing label" span
            pure (.wildcard span)
          else
            let labelText ← getGreenTokenText kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let labelSpan ← spanFor kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let arg ← if kidsWithOffsets.size >= 2 then
              some <$> lowerPattern kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            else pure none
            pure (.variant ⟨#[], labelText, labelSpan⟩ arg span)

      | .name =>
          let (path, name) ← lowerQualifiedName green offset
          if name.length > 0 && (String.Pos.Raw.get name ⟨0⟩).isUpper then
            pure (.con ⟨path, name, span⟩ #[] span)
          else
            pure (.var ⟨path, name, span⟩)

      | _ =>
          lowerError s!"unexpected pattern kind: {kind}" span
          pure (.wildcard span)

  | .error message _ _ =>
      lowerError message span
      pure (.wildcard span)

  | .missing expected =>
      lowerError s!"missing {expected}" span
      pure (.wildcard span)

/-- Lower a single binder node to `TypeVarBinder` -/
partial def lowerTypeVarBinder (v : GreenNode) (o : Nat) : LowerM TypeVarBinder := do
  match v.syntaxKind? with
  | some .instDictBinder =>
      let semanticKids := childrenWithOffsets v o
        |>.filter fun (c, _) => isSemanticNode c || isTokenKind c .lowerIdent
      let nameTokIdx? := semanticKids.findIdx? fun (c, _) => isTokenKind c .lowerIdent
      let constraintIdx? := semanticKids.findIdx? fun (c, _) => c.syntaxKind? == some .constraint
      match constraintIdx? with
      | some cIdx =>
          let (cNode, cOff) := semanticKids[cIdx]!
          let cstr ← lowerConstraint cNode cOff
          match nameTokIdx? with
          | some nIdx =>
              let (nTok, nOff) := semanticKids[nIdx]!
              let text ← getGreenTokenText nTok nOff
              let nspan ← spanFor nTok nOff
              pure (TypeVarBinder.constraint (some ⟨#[], text, nspan⟩) cstr)
          | none =>
              pure (TypeVarBinder.constraint none cstr)
      | none =>
          let vspan ← spanFor v o
          lowerError "constraint binder missing class application" vspan
          pure (TypeVarBinder.constraint none ⟨⟨#[], "_error", vspan⟩, #[], vspan⟩)
  | some .tyParamKinded =>
      let kids := childrenWithOffsets v o |>.filter (isSemanticNode ·.1)
      -- Look for the type variable name: either a .typeVar wrapper node
      -- or a raw .lowerIdent token (produced by parseInductiveBinders)
      let varChild := kids.find? fun (c, _) =>
        c.syntaxKind? == some .typeVar || isTokenKind c .lowerIdent
      let kindChildren := kids.filter fun (c, _) =>
        c.syntaxKind? != some .typeVar && !(isTokenKind c .lowerIdent)
      match varChild with
      | some (varNode, varOff) =>
          -- If varNode is a .typeVar wrapper, extract text from its child token;
          -- if it's already a leaf token (.lowerIdent), extract text directly.
          let text ← match firstGreenChild varNode with
            | some child => getGreenTokenText child varOff
            | none => getGreenTokenText varNode varOff
          let vspan ← spanFor varNode varOff
          let kindExpr ← if kindChildren.isEmpty then pure none
            else some <$> lowerTypeExpr kindChildren[0]!.1 kindChildren[0]!.2
          pure (TypeVarBinder.mk ⟨#[], text, vspan⟩ kindExpr)
      | none =>
          let vspan ← spanFor v o
          pure (TypeVarBinder.mk ⟨#[], "_", vspan⟩ none)
  | _ =>
      match firstGreenChild v with
      | some child =>
          let text ← getGreenTokenText child o
          let vspan ← spanFor v o
          pure (TypeVarBinder.mk ⟨#[], text, vspan⟩ none)
      | none =>
          let vspan ← spanFor v o
          pure (TypeVarBinder.mk ⟨#[], "_", vspan⟩ none)

/-- Lower type parameters from a tyParamList node -/
partial def lowerTypeParams (plist : GreenNode) (plistOffset : Nat) : LowerM (Array TypeVarBinder) := do
  let varNodes := childrenWithOffsets plist plistOffset |>.filter fun (c, _) =>
    let k := c.syntaxKind?
    k == some .typeVar || k == some .tyParamKinded || k == some .instDictBinder
  varNodes.mapM fun (v, vo) => lowerTypeVarBinder v vo

/-- Lower a CST type to an AST `Expr` -/
partial def lowerTypeExpr (green : GreenNode) (offset : Nat) : LowerM Expr := do
  -- For triviaToken, recurse immediately with adjusted offset (don't compute span yet)
  if green.syntaxKind? == some .triviaToken then
    let unwrapped := unwrapTrivia green
    let adjustedOffset := offset + triviaOffset green
    return ← lowerTypeExpr unwrapped adjustedOffset

  let span ← spanFor green offset

  match green with
  | .token kind text =>
      match kind with
      | .lowerIdent => pure (.var ⟨#[], text, span⟩)
      | .upperIdent => pure (.con ⟨#[], text, span⟩)
      | _ =>
          lowerError s!"unexpected token in type: {kind}" span
          pure (.var ⟨#[], "_error", span⟩)

  | .node .triviaToken _ _ => pure (.var ⟨#[], "_error", span⟩)

  | .node kind children _ =>
      match kind with
      | .typeVar =>
          match firstGreenChild green with
          | some child =>
              let text ← getGreenTokenText child offset
              pure (.var ⟨#[], text, span⟩)
          | none =>
              lowerError "type variable missing name" span
              pure (.var ⟨#[], "_error", span⟩)

      | .typeCon =>
          let (path, name) ← lowerQualifiedName green offset
          pure (.con ⟨path, name, span⟩)

      | .typeApp =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "empty type application" span
            pure (.var ⟨#[], "_error", span⟩)
          else
            let mut result ← lowerTypeExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            for (arg, argOffset) in kidsWithOffsets[1:] do
              let argTy ← lowerTypeExpr arg argOffset
              result := .app result argTy (Span.merge result.span argTy.span)
            pure result

      | .typeArrow =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size >= 2 then
            let from_ ← lowerTypeExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let to ← lowerTypeExpr kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            pure (.arrow from_ to span)
          else
            lowerError "arrow type requires two arguments" span
            pure (.var ⟨#[], "_error", span⟩)

      | .typeTuple =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          let elems ← kidsWithOffsets.mapM fun (c, o) => lowerTypeExpr c o
          pure (.tuple elems span)

      | .typeList =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "list type requires element type" span
            pure (.var ⟨#[], "_error", span⟩)
          else
            let elem ← lowerTypeExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            pure (.listTy elem span)

      | .typeForall =>
          let allKids := childrenWithOffsets green offset
          let isBinderKind : GreenNode → Bool := fun c =>
            let k := c.syntaxKind?
            k == some .typeVar || k == some .tyParamKinded || k == some .instDictBinder
          let tyParamListNode := allKids.find? fun (c, _) => c.syntaxKind? == some .tyParamList
          let binderNodes : Array (GreenNode × Nat) := match tyParamListNode with
            | some (paramList, paramOffset) =>
                let paramKids := childrenWithOffsets paramList paramOffset
                paramKids.filter fun (c, _) => isBinderKind c
            | none =>
                allKids.filter fun (c, _) => isBinderKind c
          let bodyNodes := allKids.filter fun (c, _) =>
            !isBinderKind c &&
            c.syntaxKind? != some .tyParamList && isSemanticNode c
          let vars ← binderNodes.mapM fun (v, o) => lowerTypeVarBinder v o
          if bodyNodes.isEmpty then
            lowerError "forall type requires body" span
            pure (.var ⟨#[], "_error", span⟩)
          else
            let body ← lowerTypeExpr bodyNodes[0]!.1 bodyNodes[0]!.2
            pure (.forall_ vars body span)

      | .typeParens =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            pure (.tuple #[] span)
          else
            let inner ← lowerTypeExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            pure (.parens inner span)

      | .exprInfix =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          let opNode := children.find? fun c => isTokenKind c .varSymbol || isTokenKind c .equals
          match opNode, opNode.bind getTokenText with
          | some _, some opText =>
              if kidsWithOffsets.size >= 2 then
                let left ← lowerTypeExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
                let right ← lowerTypeExpr kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
                pure (.infix ⟨opText, span⟩ left right span)
              else
                lowerError "infix type requires two operands" span
                pure (.var ⟨#[], "_error", span⟩)
          | _, _ =>
              lowerError "infix type missing operator" span
              pure (.var ⟨#[], "_error", span⟩)

      | .signature =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "signature missing type" span
            pure (.var ⟨#[], "_error", span⟩)
          else
            lowerTypeExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2

      | .typeRecord =>
          -- Parse record type
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          -- Separate field nodes from potential row tail variable
          let fieldNodes := kidsWithOffsets.filter fun (c, _) => c.syntaxKind? == some .typeRecordField
          let tailNodes := kidsWithOffsets.filter fun (c, _) => c.syntaxKind? == some .typeVar
          -- Lower fields
          let mut fields : Array (QualName × Expr) := #[]
          for (fieldNode, fieldOffset) in fieldNodes do
            let fieldKids := childrenWithOffsets fieldNode fieldOffset |>.filter fun (c, _) => isSemanticNode c
            if fieldKids.size >= 2 then
              let nameText ← getGreenTokenText fieldKids[0]!.1 fieldKids[0]!.2
              let nameSpan ← spanFor fieldKids[0]!.1 fieldKids[0]!.2
              let fieldTy ← lowerTypeExpr fieldKids[1]!.1 fieldKids[1]!.2
              fields := fields.push (⟨#[], nameText, nameSpan⟩, fieldTy)
          -- Check for tail variable
          let tail ← if tailNodes.isEmpty then pure none else do
            let (tailNode, tailOffset) := tailNodes[0]!
            let tailKids := childrenWithOffsets tailNode tailOffset |>.filter fun (c, _) => isSemanticNode c
            if tailKids.isEmpty then
              let tailText ← getGreenTokenText tailNode tailOffset
              let tailSpan ← spanFor tailNode tailOffset
              pure (some (⟨#[], tailText, tailSpan⟩ : QualName))
            else
              let tailText ← getGreenTokenText tailKids[0]!.1 tailKids[0]!.2
              let tailSpan ← spanFor tailKids[0]!.1 tailKids[0]!.2
              pure (some (⟨#[], tailText, tailSpan⟩ : QualName))
          pure (.recordTy fields tail span)

      | .typeVariant =>
          -- Parse variant type: < Ok :: Int | Err :: String > or < Ok :: Int | r >
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          -- Separate case nodes from potential row tail variable
          let caseNodes := kidsWithOffsets.filter fun (c, _) => c.syntaxKind? == some .typeVariantCase
          let tailNodes := kidsWithOffsets.filter fun (c, _) => c.syntaxKind? == some .typeVar
          -- Lower cases
          let mut cases : Array (QualName × Expr) := #[]
          for (caseNode, caseOffset) in caseNodes do
            let caseKids := childrenWithOffsets caseNode caseOffset |>.filter fun (c, _) => isSemanticNode c
            if caseKids.size >= 2 then
              let nameText ← getGreenTokenText caseKids[0]!.1 caseKids[0]!.2
              let nameSpan ← spanFor caseKids[0]!.1 caseKids[0]!.2
              let caseTy ← lowerTypeExpr caseKids[1]!.1 caseKids[1]!.2
              cases := cases.push (⟨#[], nameText, nameSpan⟩, caseTy)
          -- Check for tail variable
          let tail ← if tailNodes.isEmpty then pure none else do
            let (tailNode, tailOffset) := tailNodes[0]!
            let tailKids := childrenWithOffsets tailNode tailOffset |>.filter fun (c, _) => isSemanticNode c
            if tailKids.isEmpty then
              let tailText ← getGreenTokenText tailNode tailOffset
              let tailSpan ← spanFor tailNode tailOffset
              pure (some (⟨#[], tailText, tailSpan⟩ : QualName))
            else
              let tailText ← getGreenTokenText tailKids[0]!.1 tailKids[0]!.2
              let tailSpan ← spanFor tailKids[0]!.1 tailKids[0]!.2
              pure (some (⟨#[], tailText, tailSpan⟩ : QualName))
          pure (.variantTy cases tail span)

      | .typePi =>
          -- Dependent Pi type: (q? x : A) -> B
          -- Structure: lparen, binder, rparen, arrow, codomain
          let allKids := childrenWithOffsets green offset
          let binderNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .typePiBinder
          let codomainNodes := allKids.filter fun (c, _) =>
            c.syntaxKind? != some .typePiBinder && isSemanticNode c
          if binderNodes.isEmpty || codomainNodes.isEmpty then
            lowerError "Pi type missing binder or codomain" span
            pure (.var ⟨#[], "_error", span⟩)
          else
            let (binderNode, binderOffset) := binderNodes[0]!
            let binderKids := childrenWithOffsets binderNode binderOffset |>.filter fun (c, _) => isSemanticNode c
            -- Parse binder: optional quantity, name, domain type
            let (qty, nameIdx) ← if binderKids.size > 0 then
              let firstKid := binderKids[0]!.1
              if firstKid.syntaxKind? == some .typeQuantity then
                let qtyText ← getGreenTokenText (firstGreenChild firstKid |>.getD firstKid) binderKids[0]!.2
                let q := match qtyText with
                  | "0" => Quantity.zero
                  | "1" => Quantity.one
                  | _ => Quantity.omega
                pure (q, 1)
              else
                pure (Quantity.omega, 0)
            else
              pure (Quantity.omega, 0)
            if h : nameIdx < binderKids.size then
              let (nameNode, nameOffset) := binderKids[nameIdx]
              let nameText ← match firstGreenChild nameNode with
                | some child => getGreenTokenText child nameOffset
                | none => getGreenTokenText nameNode nameOffset
              let nameSpan ← spanFor nameNode nameOffset
              let domainIdx := nameIdx + 1
              if h2 : domainIdx < binderKids.size then
                let domain ← lowerTypeExpr binderKids[domainIdx].1 binderKids[domainIdx].2
                let codomain ← lowerTypeExpr codomainNodes[0]!.1 codomainNodes[0]!.2
                pure (.pi qty .explicit ⟨#[], nameText, nameSpan⟩ domain codomain span)
              else
                lowerError "Pi type binder missing domain type" span
                pure (.var ⟨#[], "_error", span⟩)
            else
              lowerError "Pi type binder missing name" span
              pure (.var ⟨#[], "_error", span⟩)

      | .typeSigma =>
          -- Dependent Sigma type: (q? x : A) × B
          -- Structure: lparen, binder, rparen, times, snd
          let allKids := childrenWithOffsets green offset
          let binderNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .typePiBinder
          let sndNodes := allKids.filter fun (c, _) =>
            c.syntaxKind? != some .typePiBinder && isSemanticNode c
          if binderNodes.isEmpty || sndNodes.isEmpty then
            lowerError "Sigma type missing binder or second type" span
            pure (.var ⟨#[], "_error", span⟩)
          else
            let (binderNode, binderOffset) := binderNodes[0]!
            let binderKids := childrenWithOffsets binderNode binderOffset |>.filter fun (c, _) => isSemanticNode c
            -- Parse binder: optional quantity, name, fst type
            let (qty, nameIdx) ← if binderKids.size > 0 then
              let firstKid := binderKids[0]!.1
              if firstKid.syntaxKind? == some .typeQuantity then
                let qtyText ← getGreenTokenText (firstGreenChild firstKid |>.getD firstKid) binderKids[0]!.2
                let q := match qtyText with
                  | "0" => Quantity.zero
                  | "1" => Quantity.one
                  | _ => Quantity.omega
                pure (q, 1)
              else
                pure (Quantity.omega, 0)
            else
              pure (Quantity.omega, 0)
            if h : nameIdx < binderKids.size then
              let (nameNode, nameOffset) := binderKids[nameIdx]
              let nameText ← match firstGreenChild nameNode with
                | some child => getGreenTokenText child nameOffset
                | none => getGreenTokenText nameNode nameOffset
              let nameSpan ← spanFor nameNode nameOffset
              let fstIdx := nameIdx + 1
              if h2 : fstIdx < binderKids.size then
                let fst ← lowerTypeExpr binderKids[fstIdx].1 binderKids[fstIdx].2
                let snd ← lowerTypeExpr sndNodes[0]!.1 sndNodes[0]!.2
                pure (.sigma qty ⟨#[], nameText, nameSpan⟩ fst snd span)
              else
                lowerError "Sigma type binder missing first type" span
                pure (.var ⟨#[], "_error", span⟩)
            else
              lowerError "Sigma type binder missing name" span
              pure (.var ⟨#[], "_error", span⟩)

      | .typeImplicit =>
          -- Implicit type: {x : A} -> B, {{x : A}} -> B, or {{A}} -> B
          -- Structure varies: single-brace or double-brace, named or unnamed
          let allKids := childrenWithOffsets green offset
          let binderNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .typePiBinder
          let semanticKids := allKids.filter fun (c, _) => isSemanticNode c
          if semanticKids.size < 2 then
            lowerError "Implicit type missing domain or codomain" span
            pure (.var ⟨#[], "_error", span⟩)
          else if !binderNodes.isEmpty then
            -- Named implicit: {{x : A}} -> B
            let (binderNode, binderOffset) := binderNodes[0]!
            let binderKids := childrenWithOffsets binderNode binderOffset |>.filter fun (c, _) => isSemanticNode c
            if binderKids.size >= 2 then
              let (nameNode, nameOffset) := binderKids[0]!
              let nameText ← match firstGreenChild nameNode with
                | some child => getGreenTokenText child nameOffset
                | none => getGreenTokenText nameNode nameOffset
              let nameSpan ← spanFor nameNode nameOffset
              let domain ← lowerTypeExpr binderKids[1]!.1 binderKids[1]!.2
              -- Find the codomain (last semantic kid that's not the binder)
              let codomainKids := semanticKids.filter fun (c, _) => c.syntaxKind? != some .typePiBinder
              if codomainKids.isEmpty then
                lowerError "Implicit type missing codomain" span
                pure (.var ⟨#[], "_error", span⟩)
              else
                let codomain ← lowerTypeExpr codomainKids[codomainKids.size - 1]!.1 codomainKids[codomainKids.size - 1]!.2
                pure (.pi .omega .instance_ ⟨#[], nameText, nameSpan⟩ domain codomain span)
            else
              lowerError "Implicit type binder incomplete" span
              pure (.var ⟨#[], "_error", span⟩)
          else
            -- Unnamed implicit: {{A}} -> B
            let domain ← lowerTypeExpr semanticKids[0]!.1 semanticKids[0]!.2
            let codomain ← lowerTypeExpr semanticKids[semanticKids.size - 1]!.1 semanticKids[semanticKids.size - 1]!.2
            pure (.pi .omega .instance_ ⟨#[], "_", span⟩ domain codomain span)

      | .typePiBinder | .typeQuantity =>
          -- These are helper nodes, not standalone types
          lowerError s!"unexpected standalone {kind}" span
          pure (.var ⟨#[], "_error", span⟩)

      | _ =>
          lowerError s!"unexpected type kind: {kind}" span
          pure (.var ⟨#[], "_error", span⟩)

  | .error message _ _ =>
      lowerError message span
      pure (.var ⟨#[], "_error", span⟩)

  | .missing expected =>
      lowerError s!"missing {expected}" span
      pure (.var ⟨#[], "_error", span⟩)

/-- Lower a constraint node -/
partial def lowerConstraint (green : GreenNode) (offset : Nat) : LowerM Constraint := do
  let span ← spanFor green offset

  match green with
  | .node .constraint _ _ =>
      let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
      if kidsWithOffsets.isEmpty then
        let tokenKids := green.children.filter fun c =>
          isTokenKind c .upperIdent
        if tokenKids.isEmpty then
          lowerError "empty constraint" span
          pure ⟨⟨#[], "_error", span⟩, #[], span⟩
        else
          match getTokenText tokenKids[0]! with
          | some text => pure ⟨⟨#[], text, span⟩, #[], span⟩
          | none => pure ⟨⟨#[], "_error", span⟩, #[], span⟩
      else
        let (classNode, classOffset) := kidsWithOffsets[0]!
        let className ← match classNode.syntaxKind? with
        | some .typeCon =>
            match firstGreenChild classNode with
            | some child =>
                let text ← getGreenTokenText child classOffset
                let cspan ← spanFor classNode classOffset
                pure ⟨#[], text, cspan⟩
            | none => pure ⟨#[], "_error", span⟩
        | _ =>
            match getTokenText classNode with
            | some text =>
                let cspan ← spanFor classNode classOffset
                pure ⟨#[], text, cspan⟩
            | none =>
                lowerError "expected class name in constraint" span
                pure ⟨#[], "_error", span⟩
        let args ← kidsWithOffsets[1:].toArray.mapM fun (c, o) => lowerTypeExpr c o
        pure ⟨className, args, span⟩

  | .node .constraintList _ _ =>
      let constraintNodes := childrenOfGreenKind green .constraint
      if !constraintNodes.isEmpty then
        -- Find offset of first constraint
        let allKids := childrenWithOffsets green offset
        match allKids.find? fun (c, _) => c.syntaxKind? == some .constraint with
        | some (c, o) => lowerConstraint c o
        | none => pure ⟨⟨#[], "_error", span⟩, #[], span⟩
      else
        let nestedLists := childrenOfGreenKind green .constraintList
        if !nestedLists.isEmpty then
          let allKids := childrenWithOffsets green offset
          match allKids.find? fun (c, _) => c.syntaxKind? == some .constraintList with
          | some (c, o) => lowerConstraint c o
          | none => pure ⟨⟨#[], "_error", span⟩, #[], span⟩
        else
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "empty constraint list" span
            pure ⟨⟨#[], "_error", span⟩, #[], span⟩
          else
            lowerConstraint kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2

  | .node kind _ _ =>
      if kind == .typeApp || kind == .typeCon || kind == .typeVar then
        let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
        if kidsWithOffsets.isEmpty then
          match kind with
          | .typeCon =>
              let (path, name) ← lowerQualifiedName green offset
              pure ⟨⟨path, name, span⟩, #[], span⟩
          | _ =>
              lowerError "expected constraint" span
              pure ⟨⟨#[], "_error", span⟩, #[], span⟩
        else
          let (classNode, classOffset) := kidsWithOffsets[0]!
          let className ← match classNode.syntaxKind? with
          | some .typeCon =>
              let (path, name) ← lowerQualifiedName classNode classOffset
              let cspan ← spanFor classNode classOffset
              pure ⟨path, name, cspan⟩
          | _ =>
              match getTokenText classNode with
              | some text =>
                  let cspan ← spanFor classNode classOffset
                  pure ⟨#[], text, cspan⟩
              | none =>
                  match firstGreenChild classNode with
                  | some child =>
                      let text ← getGreenTokenText child classOffset
                      let cspan ← spanFor classNode classOffset
                      pure ⟨#[], text, cspan⟩
                  | none => pure ⟨#[], "_error", span⟩
          let args ← kidsWithOffsets[1:].toArray.mapM fun (c, o) => lowerTypeExpr c o
          pure ⟨className, args, span⟩
      else
        lowerError s!"unexpected constraint node kind: {kind}" span
        pure ⟨⟨#[], "_error", span⟩, #[], span⟩

  | .token kind text =>
      if kind == .upperIdent then
        pure ⟨⟨#[], text, span⟩, #[], span⟩
      else
        lowerError s!"unexpected token in constraint: {kind}" span
        pure ⟨⟨#[], "_error", span⟩, #[], span⟩

  | _ =>
      lowerError "unexpected constraint node" span
      pure ⟨⟨#[], "_error", span⟩, #[], span⟩

end

/-- Lower attribute nodes to Syntax.Attribute values -/
partial def lowerAttributes (attrNodes : Array (GreenNode × Nat)) : LowerM (Array Attribute) :=
  attrNodes.mapM fun (a, ao) => do
    let aspan ← spanFor a ao
    let nameTokens := a.children.filter fun c => isTokenKind c .lowerIdent
    let stringTokens := a.children.filter isStringToken
    let args ← if stringTokens.isEmpty then
      pure #[]
    else
      let strTok := stringTokens[0]!
      match getTokenText strTok with
      | some text =>
        let unquoted := if text.utf8ByteSize >= 2 then
          let pos1 : String.Pos.Raw := ⟨1⟩
          let posEnd : String.Pos.Raw := ⟨text.utf8ByteSize - 1⟩
          if hv1 : String.Pos.Raw.IsValid text pos1 then
            if hv2 : String.Pos.Raw.IsValid text posEnd then
              text.extract ⟨pos1, hv1⟩ ⟨posEnd, hv2⟩
            else text
          else text
        else text
        pure #[Expr.lit (.string unquoted aspan)]
      | none => pure #[]
    if nameTokens.isEmpty then
      pure ⟨⟨#[], "unknown", aspan⟩, args, aspan⟩
    else
      match getTokenText nameTokens[0]! with
      | some text => pure ⟨⟨#[], text, aspan⟩, args, aspan⟩
      | none => pure ⟨⟨#[], "unknown", aspan⟩, args, aspan⟩

/-- Lower a data constructor -/
partial def lowerDataCon (green : GreenNode) (offset : Nat) : LowerM DataCon := do
  let span ← spanFor green offset

  match green with
  | .node .constructor _ _ =>
      let allKids := childrenWithOffsets green offset

      -- Extract constructor-level attributes
      let attrNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .attribute
      let attrs ← lowerAttributes attrNodes

      let nameNodes := green.children.filter fun c => isTokenKind c .upperIdent
      let name := if nameNodes.isEmpty then ⟨#[], "_Con", span⟩
        else match getTokenText nameNodes[0]! with
        | some text => ⟨#[], text, span⟩
        | none => ⟨#[], "_Con", span⟩

      let fieldNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .field
      let fields ← fieldNodes.mapM fun (f, fo) => do
        let fKids := childrenWithOffsets f fo |>.filter fun (c, _) => isSemanticNode c
        let nameNode? := fKids.find? fun (c, _) => isTokenKind c .lowerIdent
        let typeNode? := fKids.find? fun (c, _) =>
          match c.syntaxKind? with
          | some sk => sk.isType
          | none => false

        match typeNode? with
        | some (tyNode, tyOff) =>
            let ftype ← lowerTypeExpr tyNode tyOff
            match nameNode? with
            | some (nNode, nOff) =>
                match firstGreenChild nNode with
                | some nameChild =>
                    let fname ← getGreenTokenText nameChild nOff
                    let fnameSpan ← spanFor nNode nOff
                    pure (some ⟨#[], fname, fnameSpan⟩, ftype)
                | none =>
                    pure (none, ftype)
            | none =>
                pure (none, ftype)
        | none =>
            let fspan ← spanFor f fo
            pure (none, .var ⟨#[], "_", fspan⟩)

      pure { attrs, name, fields, span }

  | .node .constructorSig _ _ =>
      let allKids := childrenWithOffsets green offset

      -- Extract constructor-level attributes
      let attrNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .attribute
      let attrs ← lowerAttributes attrNodes

      -- Indexed constructor with signature: | Cons : a -> Vec n a -> Vec (n+1) a
      let nameNodes := green.children.filter fun c => isTokenKind c .upperIdent
      let name := if nameNodes.isEmpty then ⟨#[], "_Con", span⟩
        else match getTokenText nameNodes[0]! with
        | some text => ⟨#[], text, span⟩
        | none => ⟨#[], "_Con", span⟩

      -- Extract binder fields (present when constructor has both binders and a return type)
      let fieldNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .field

      let typeNodes := allKids.filter fun (c, _) =>
        isSemanticNode c && !c.isToken
          && c.syntaxKind? != some .field
          && c.syntaxKind? != some .attribute
      if typeNodes.size >= 1 then
        let mut sig ← lowerTypeExpr typeNodes[0]!.1 typeNodes[0]!.2
        -- If there are binder fields, wrap them into the signature type.
        for (f, fo) in fieldNodes.reverse do
          let fKids := childrenWithOffsets f fo |>.filter fun (c, _) => isSemanticNode c
          let nameNode? := fKids.find? fun (c, _) => isTokenKind c .lowerIdent
          let typeNode? := fKids.find? fun (c, _) =>
            match c.syntaxKind? with
            | some sk => sk.isType
            | none => false
          let isImplicit := f.children.any fun c => isTokenKind c .leftBrace
          match typeNode? with
          | some (tyNode, tyOff) =>
            let ftype ← lowerTypeExpr tyNode tyOff
            let fname ← match nameNode? with
              | some (nNode, nOff) =>
                match firstGreenChild nNode with
                | some nameChild => getGreenTokenText nameChild nOff
                | none => pure "_"
              | none => pure "_"
            let fnameSpan ← spanFor f fo
            if isImplicit then
              let binder := TypeVarBinder.mk ⟨#[], fname, fnameSpan⟩ (some ftype)
              sig := .forall_ #[binder] sig span
            else
              sig := .pi .omega .explicit ⟨#[], fname, fnameSpan⟩ ftype sig span
          | none => pure ()
        pure { attrs, name, fields := #[], sig := some sig, span }
      else
        lowerError "expected type signature for indexed constructor" span
        pure { name := ⟨#[], "_Con", span⟩, fields := #[], span }

  | _ =>
      lowerError "expected constructor" span
      pure { name := ⟨#[], "_Con", span⟩, fields := #[], span }

/-- Lower a record field -/
partial def lowerRecordField (green : GreenNode) (offset : Nat) : LowerM RecordField := do
  let span ← spanFor green offset
  let allKids := childrenWithOffsets green offset

  -- Look for name token
  let nameTokens := green.children.filter fun c => isTokenKind c .lowerIdent
  let fname ← if nameTokens.isEmpty then pure none
    else match getTokenText nameTokens[0]! with
    | some text => pure (some ⟨#[], text, span⟩)
    | none => pure none

  let syntaxKids := allKids.filter fun (c, _) => !c.isToken && isSemanticNode c

  if syntaxKids.size >= 1 then
    let ftype ← lowerTypeExpr syntaxKids[0]!.1 syntaxKids[0]!.2
    pure ⟨fname, ftype, span⟩
  else
    lowerError "record field missing type" span
    pure ⟨none, .var ⟨#[], "_", span⟩, span⟩

/-- Lower a token to an expression -/
def lowerExprToken (kind : TokenKind) (text : String) (span : Span) : LowerM Expr := do
  match kind with
  | .lowerIdent => pure (.var ⟨#[], text, span⟩)
  | .upperIdent => pure (.var ⟨#[], text, span⟩)
  | .number => pure (.lit (.int text.toInt! span))
  | .string s => pure (.lit (.string s span))
  | .true_ => pure (.lit (.bool true span))
  | .false_ => pure (.lit (.bool false span))
  | _ =>
      lowerError s!"unexpected token in expression: {kind}" span
      pure (.var ⟨#[], "_error", span⟩)

/-- Lower a single parameter -/
def lowerSingleParam (green : GreenNode) (offset : Nat) : LowerM (QualName × Option Expr) := do
  let span ← spanFor green offset
  match green.syntaxKind? with
  | some .patVar =>
      match firstGreenChild green with
      | some child =>
          let name ← getGreenTokenText child offset
          pure (⟨#[], name, span⟩, none)
      | none => pure (⟨#[], "_", span⟩, none)
  | some .field =>
      let tokenKids := green.children.filter fun c => isTokenKind c .lowerIdent
      if tokenKids.isEmpty then
        pure (⟨#[], "_", span⟩, none)
      else
        match getTokenText tokenKids[0]! with
        | some text =>
            let typeNodes := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
            if typeNodes.size >= 1 then
              let ty ← lowerTypeExpr typeNodes[0]!.1 typeNodes[0]!.2
              pure (⟨#[], text, span⟩, some ty)
            else
              pure (⟨#[], text, span⟩, none)
        | none => pure (⟨#[], "_", span⟩, none)
  | _ => pure (⟨#[], "_", span⟩, none)

/-- Lower lambda parameters -/
def lowerLambdaParams (paramNodes : Array (GreenNode × Nat)) : LowerM (Array (QualName × Option Expr)) := do
  let mut result : Array (QualName × Option Expr) := #[]
  for (p, pOffset) in paramNodes do
    match p.syntaxKind? with
    | some .paramList =>
        let vars := childrenWithOffsets p pOffset |>.filter fun (c, _) =>
          c.syntaxKind? == some .patVar || c.syntaxKind? == some .field
        for (v, vo) in vars do
          let param ← lowerSingleParam v vo
          result := result.push param
    | some .patVar =>
        let param ← lowerSingleParam p pOffset
        result := result.push param
    | some .field =>
        let param ← lowerSingleParam p pOffset
        result := result.push param
    | _ =>
        let span ← spanFor p pOffset
        result := result.push (⟨#[], "_", span⟩, none)
  pure result

partial def lowerExpr (green : GreenNode) (offset : Nat) : LowerM Expr := do
  -- For triviaToken, recurse immediately with adjusted offset (don't compute span yet)
  if green.syntaxKind? == some .triviaToken then
    let unwrapped := unwrapTrivia green
    let adjustedOffset := offset + triviaOffset green
    return ← lowerExpr unwrapped adjustedOffset

  let span ← spanFor green offset

  match green with
  | .token kind text => lowerExprToken kind text span

  | .node .triviaToken _ _ =>
      -- Already handled above, but need this case for exhaustiveness
      pure (.var ⟨#[], "_error", span⟩)

  | .node kind children _ =>
      match kind with
      | .exprVar =>
          let (path, name) ← lowerQualifiedName green offset
          pure (.var ⟨path, name, span⟩)

      | .exprLit =>
          match firstGreenChild green with
          | some child => lowerExpr child offset
          | none =>
              lowerError "literal missing value" span
              pure (.var ⟨#[], "_error", span⟩)

      | .exprApp =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size < 2 then
            lowerError "application requires function and argument" span
            pure (.var ⟨#[], "_error", span⟩)
          else
            let fn ← lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let arg ← lowerExpr kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            pure (.app fn arg span)

      | .exprInfix =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          let opNode := children.find? fun c => isTokenKind c .varSymbol || isTokenKind c .equals
          match opNode, opNode.bind getTokenText with
          | some _, some opText =>
              if kidsWithOffsets.size >= 2 then
                let left ← lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
                let right ← lowerExpr kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
                pure (.infix ⟨opText, span⟩ left right span)
              else
                lowerError "infix expression requires two operands" span
                pure (.var ⟨#[], "_error", span⟩)
          | _, _ =>
              lowerError "infix expression missing operator" span
              pure (.var ⟨#[], "_error", span⟩)

      | .exprLambda =>
          let allKids := childrenWithOffsets green offset
          let paramNodes := allKids.filter fun (c, _) =>
            c.syntaxKind? == some .paramList || c.syntaxKind? == some .patVar
          let bodyNodes := allKids.filter fun (c, _) =>
            c.syntaxKind? != some .paramList && c.syntaxKind? != some .patVar && isSemanticNode c
          let params ← lowerLambdaParams paramNodes
          if bodyNodes.isEmpty then
            lowerError "lambda missing body" span
            pure (.var ⟨#[], "_error", span⟩)
          else
            let body ← lowerExpr bodyNodes[0]!.1 bodyNodes[0]!.2
            pure (.lambda params body span)

      | .exprLet =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size >= 2 then
            let (patNode, patOffset) := kidsWithOffsets[0]!

            let sigNodes := kidsWithOffsets.filter fun (c, _) => c.syntaxKind? == some .signature
            let sig ← if sigNodes.isEmpty then pure none
              else some <$> lowerTypeExpr sigNodes[0]!.1 sigNodes[0]!.2

            let valueIdx := if sigNodes.isEmpty then 1 else 2
            if h : valueIdx < kidsWithOffsets.size then
              let value ← lowerExpr kidsWithOffsets[valueIdx].1 kidsWithOffsets[valueIdx].2
              let bodyIdx := valueIdx + 1
              if h2 : bodyIdx < kidsWithOffsets.size then
                let body ← lowerExpr kidsWithOffsets[bodyIdx].1 kidsWithOffsets[bodyIdx].2
                -- Let bindings are desugared to case expressions
                let pat ← lowerPattern patNode patOffset
                let typedPat := match sig with
                  | some tyExpr => Pattern.typed pat tyExpr span
                  | none => pat
                let arm := MatchArm.mk #[typedPat] none body span
                pure (.case #[value] #[arm] span)
              else
                lowerError "let missing body" span
                let errorBody := Expr.var ⟨#[], "_error", span⟩
                let wildcardPat := Pattern.wildcard span
                let arm := MatchArm.mk #[wildcardPat] none errorBody span
                pure (.case #[value] #[arm] span)
            else
              lowerError "let missing value" span
              pure (.var ⟨#[], "_error", span⟩)
          else
            lowerError "let expression incomplete" span
            pure (.var ⟨#[], "_error", span⟩)

      | .exprIf =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size >= 3 then
            let cond ← lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let then_ ← lowerExpr kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            let else_ ← lowerExpr kidsWithOffsets[2]!.1 kidsWithOffsets[2]!.2
            pure (.if_ cond then_ else_ span)
          else
            lowerError "if expression incomplete" span
            pure (.var ⟨#[], "_error", span⟩)

      | .exprCase =>
          let allKids := childrenWithOffsets green offset
          let armNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .matchArm
          let scrutNodes := allKids.filter fun (c, _) => c.syntaxKind? != some .matchArm && isSemanticNode c
          let scrutinees ← scrutNodes.mapM fun (c, o) => lowerExpr c o
          let arms ← armNodes.mapM fun (c, o) => lowerMatchArm c o
          pure (.case scrutinees arms span)

      | .exprTuple =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          let elems ← kidsWithOffsets.mapM fun (c, o) => lowerExpr c o
          pure (.tuple elems span)

      | .exprList =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          let elems ← kidsWithOffsets.mapM fun (c, o) => lowerExpr c o
          pure (.list elems span)

      | .exprRecord =>
          let allKids := childrenWithOffsets green offset
          let fieldNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .recordField
          let fields ← fieldNodes.mapM fun (fieldNode, fieldOffset) => do
            let fieldSpan ← spanFor fieldNode fieldOffset
            let fieldKids := childrenWithOffsets fieldNode fieldOffset
            let nameTokens := fieldNode.children.filter fun c => isTokenKind c .lowerIdent
            let fieldName ← if nameTokens.isEmpty then pure "_error"
              else match getTokenText nameTokens[0]! with
                | some text => pure text
                | none => pure "_error"
            let exprNodes := fieldKids.filter fun (c, _) => isSemanticNode c && !c.isToken
            if exprNodes.isEmpty then
              pure (⟨#[], fieldName, fieldSpan⟩, Expr.var ⟨#[], fieldName, fieldSpan⟩)
            else
              let valExpr ← lowerExpr exprNodes[0]!.1 exprNodes[0]!.2
              pure (⟨#[], fieldName, fieldSpan⟩, valExpr)
          pure (.record fields span)

      | .exprRecordUpdate =>
          let allKids := childrenWithOffsets green offset
          let exprNodes := allKids.filter fun (c, _) => isSemanticNode c && !c.isToken && c.syntaxKind? != some .recordField
          let fieldNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .recordField
          if exprNodes.isEmpty then
            lowerError "record update missing base expression" span
            pure (.var ⟨#[], "_error", span⟩)
          else
            let baseExpr ← lowerExpr exprNodes[0]!.1 exprNodes[0]!.2
            let updates ← fieldNodes.mapM fun (fieldNode, fieldOffset) => do
              let fieldSpan ← spanFor fieldNode fieldOffset
              let fieldKids := childrenWithOffsets fieldNode fieldOffset
              let nameTokens := fieldNode.children.filter fun c => isTokenKind c .lowerIdent
              let fieldName ← if nameTokens.isEmpty then pure "_error"
                else match getTokenText nameTokens[0]! with
                  | some text => pure text
                  | none => pure "_error"
              let valExprNodes := fieldKids.filter fun (c, _) => isSemanticNode c && !c.isToken
              if valExprNodes.isEmpty then
                pure (⟨#[], fieldName, fieldSpan⟩, Expr.var ⟨#[], fieldName, fieldSpan⟩)
              else
                let valExpr ← lowerExpr valExprNodes[0]!.1 valExprNodes[0]!.2
                pure (⟨#[], fieldName, fieldSpan⟩, valExpr)
            pure (.recordUpdate baseExpr updates span)

      | .exprFieldAccess =>
          -- Structure: [expr, dot, fieldName]
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size >= 2 then
            let expr ← lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let fieldNode := kidsWithOffsets[1]!.1
            let fieldText ← getGreenTokenText fieldNode kidsWithOffsets[1]!.2
            let fieldSpan ← spanFor fieldNode kidsWithOffsets[1]!.2
            pure (.fieldAccess expr ⟨#[], fieldText, fieldSpan⟩ span)
          else
            lowerError "incomplete field access" span
            pure (.var ⟨#[], "_error", span⟩)

      | .exprProjection =>
          -- Structure: [TypeName, dot, fieldName] -> becomes Expr.projection
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size >= 2 then
            let typeText ← getGreenTokenText kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let typeSpan ← spanFor kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let fieldText ← getGreenTokenText kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            let fieldSpan ← spanFor kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            pure (.projection ⟨#[], typeText, typeSpan⟩ ⟨#[], fieldText, fieldSpan⟩ span)
          else
            lowerError "incomplete projection" span
            pure (.var ⟨#[], "_error", span⟩)

      | .exprParens =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            pure (.tuple #[] span)
          else
            let inner ← lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            pure (.parens inner span)

      | .exprTypeAnnot =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size >= 2 then
            let expr ← lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let ty ← lowerTypeExpr kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            pure (.typeAnnot expr ty span)
          else
            lowerError "type annotation incomplete" span
            pure (.var ⟨#[], "_error", span⟩)

      | .exprTypeApp =>
          -- Structure: [@, type] or [@, label]
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size >= 1 then
            let argNode := kidsWithOffsets[0]!.1
            let argOffset := kidsWithOffsets[0]!.2
            -- Check if it's a label (lowerIdent token) or a type
            match argNode.tokenKind? with
            | some .lowerIdent =>
              -- It's a label: @fieldName
              let labelText ← getGreenTokenText argNode argOffset
              let labelSpan ← spanFor argNode argOffset
              pure (.typeApp (.label ⟨#[], labelText, labelSpan⟩) span)
            | _ =>
              -- It's a type: @Type or @(Type)
              let ty ← lowerTypeExpr argNode argOffset
              pure (.typeApp (.type ty) span)
          else
            lowerError "type application incomplete" span
            pure (.var ⟨#[], "_error", span⟩)

      | .exprCompose =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "compose block empty" span
            pure (.var ⟨#[], "_error", span⟩)
          else if kidsWithOffsets.size == 1 then
            -- Single expression, no desugaring needed
            lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
          else
            let lastIdx := kidsWithOffsets.size - 1
            let (lastNode, lastOffset) := kidsWithOffsets[lastIdx]!
            let finalExpr ← lowerExpr lastNode lastOffset

            let mut stmts : Array ComposeStmt := #[]

            for i in List.range lastIdx do
              let (stmtNode, stmtOffset) := kidsWithOffsets[i]!
              let stmtSpan ← spanFor stmtNode stmtOffset

              match stmtNode.syntaxKind? with
              | some .composeLetStmt =>
                  -- Pure let binding: let x = value
                  let nameTokens := stmtNode.children.filter fun c => isTokenKind c .lowerIdent
                  let valueNodes := childrenWithOffsets stmtNode stmtOffset |>.filter fun (c, _) => isSemanticNode c
                  if valueNodes.isEmpty then
                    lowerError "compose let missing value" stmtSpan
                  else
                    let (valueNode, valueOffset) := valueNodes[valueNodes.size - 1]!
                    let value ← lowerExpr valueNode valueOffset
                    let varName := match nameTokens[0]? with
                      | some tok => match getTokenText tok with
                        | some text => text
                        | none => "_"
                      | none => "_"
                    stmts := stmts.push (.let_ ⟨#[], varName, stmtSpan⟩ value stmtSpan)

              | some .composeBindStmt =>
                  -- Monadic bind: bind x <- action
                  let nameTokens := stmtNode.children.filter fun c => isTokenKind c .lowerIdent
                  let valueNodes := childrenWithOffsets stmtNode stmtOffset |>.filter fun (c, _) => isSemanticNode c
                  if valueNodes.isEmpty then
                    lowerError "compose bind missing value" stmtSpan
                  else
                    let (valueNode, valueOffset) := valueNodes[valueNodes.size - 1]!
                    let value ← lowerExpr valueNode valueOffset
                    let varName := match nameTokens[0]? with
                      | some tok => match getTokenText tok with
                        | some text => text
                        | none => "_"
                      | none => "_"
                    stmts := stmts.push (.bind_ ⟨#[], varName, stmtSpan⟩ value stmtSpan)

              | _ =>
                  -- Expression statement
                  let expr ← lowerExpr stmtNode stmtOffset
                  stmts := stmts.push (.expr expr stmtSpan)

            pure (.composeBlock stmts finalExpr span)

      | .exprVariant =>
          -- Structure: [dot, labelToken, optionalArgExpr]
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "variant expression missing label" span
            pure (.var ⟨#[], "_error", span⟩)
          else
            let labelText ← getGreenTokenText kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let labelSpan ← spanFor kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let arg ← if kidsWithOffsets.size >= 2 then
              some <$> lowerExpr kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            else pure none
            pure (.variant ⟨#[], labelText, labelSpan⟩ arg span)

      | .composeLetStmt | .composeBindStmt =>
          -- These are handled directly in .exprCompose
          -- If we reach here, it means they appeared outside a compose block
          lowerError "let/bind statement outside compose block" span
          pure (.var ⟨#[], "_error", span⟩)

      | .name =>
          match firstGreenChild green with
          | some child =>
              let text ← getGreenTokenText child offset
              pure (.var ⟨#[], text, span⟩)
          | none =>
              lowerError "name missing text" span
              pure (.var ⟨#[], "_error", span⟩)

      | _ =>
          lowerError s!"unexpected expression kind: {kind}" span
          pure (.var ⟨#[], "_error", span⟩)

  | .error message _ _ =>
      lowerError message span
      pure (.var ⟨#[], "_error", span⟩)

  | .missing expected =>
      lowerError s!"missing {expected}" span
      pure (.var ⟨#[], "_error", span⟩)

where
  lowerMatchArm (green : GreenNode) (offset : Nat) : LowerM MatchArm := do
    let span ← spanFor green offset
    match green with
    | .node .matchArm _ _ =>
        let allKids := childrenWithOffsets green offset
        let patternKinds : Array SyntaxKind := #[.patVar, .patCon, .patLit, .patWildcard, .patTuple, .patList, .patCons, .name]
        let patNodes := allKids.filter fun (c, _) =>
          match c.syntaxKind? with
          | some k => patternKinds.contains k
          | none => false
        let guardNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .matchGuard
        let bodyNodes := allKids.filter fun (c, _) =>
          match c.syntaxKind? with
          | some k => !patternKinds.contains k && k != .matchGuard && isSemanticNode c
          | none => isSemanticNode c

        let patterns ← patNodes.mapM fun (c, o) => lowerPattern c o
        let guard ← if guardNodes.isEmpty then pure none
          else
            let (g, go) := guardNodes[0]!
            let gKids := childrenWithOffsets g go |>.filter fun (c, _) => isSemanticNode c
            if gKids.isEmpty then pure none
            else some <$> lowerExpr gKids[0]!.1 gKids[0]!.2

        if bodyNodes.isEmpty then
          lowerError "match arm missing body" span
          pure (.mk patterns guard (.var ⟨#[], "_error", span⟩) span)
        else
          let body ← lowerExpr bodyNodes[0]!.1 bodyNodes[0]!.2
          pure (.mk patterns guard body span)

    | _ =>
        lowerError "expected match arm" span
        pure (.mk #[] none (.var ⟨#[], "_error", span⟩) span)

/-- Lower a definition clause -/
partial def lowerDefClause (green : GreenNode) (offset : Nat) : LowerM DefClause := do
  let span ← spanFor green offset
  let allKids := childrenWithOffsets green offset

  let patNodes := allKids.filter fun (c, _) =>
    match c.syntaxKind? with
    | some k => k.isPattern || k == .name
    | none => false
  let guardNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .matchGuard
  let bodyNodes := allKids.filter fun (c, _) =>
    match c.syntaxKind? with
    | some k => !k.isPattern && k != .matchGuard && k != .name && isSemanticNode c
    | none => isSemanticNode c

  let patterns ← patNodes.mapM fun (c, o) => lowerPattern c o
  let guard ← if guardNodes.isEmpty then pure none
    else
      let (g, go) := guardNodes[0]!
      let gKids := childrenWithOffsets g go |>.filter fun (c, _) => isSemanticNode c
      if gKids.isEmpty then pure none
      else some <$> lowerExpr gKids[0]!.1 gKids[0]!.2

  if bodyNodes.isEmpty then
    lowerError "definition clause missing body" span
    pure ⟨patterns, guard, .var ⟨#[], "_error", span⟩, span⟩
  else
    let body ← lowerExpr bodyNodes[0]!.1 bodyNodes[0]!.2
    pure ⟨patterns, guard, body, span⟩

/-- Lower a declaration -/
partial def lowerDecl (green : GreenNode) (offset : Nat) : LowerM Decl := do
  let span ← spanFor green offset

  match green with
  | .node kind _children _ =>
      match kind with
      | .declDef | .declTheorem =>
          -- `def` and `theorem` share their entire syntactic shape
          let mkDecl : Array Attribute → QualName → Array DefParam →
              Option Expr → Array DefClause → Span → Decl :=
            match kind with
            | .declTheorem => Decl.theorem_
            | _            => Decl.def_
          let allKids := childrenWithOffsets green offset
          let attrNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .attribute
          let attrs ← lowerAttributes attrNodes

          let nameNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .name
          let opNameNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .operatorName
          let name ← if !nameNodes.isEmpty then
            let (n, no) := nameNodes[0]!
            match firstGreenChild n with
            | some child =>
                let text ← getGreenTokenText child no
                let nspan ← spanFor n no
                pure ⟨#[], text, nspan⟩
            | none =>
                lowerError "definition missing name" span
                pure ⟨#[], "_error", span⟩
          else if !opNameNodes.isEmpty then
            let (opNode, oo) := opNameNodes[0]!
            let opTokens := opNode.children.filter fun c => isTokenKind c .varSymbol
            if opTokens.isEmpty then
              lowerError "operator name missing operator" span
              pure ⟨#[], "_error", span⟩
            else
              match getTokenText opTokens[0]! with
              | some text =>
                  let ospan ← spanFor opNode oo
                  pure ⟨#[], text, ospan⟩
              | none => pure ⟨#[], "_error", span⟩
          else
            lowerError "definition missing name" span
            pure ⟨#[], "_error", span⟩

          -- Extract parameter list and preserve header parameters
          let paramListNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .paramList

          let headerParams ← if paramListNodes.isEmpty then pure #[]
            else
              let (plist, plistOffset) := paramListNodes[0]!
              let varNodes := childrenWithOffsets plist plistOffset |>.filter fun (c, _) =>
                c.syntaxKind? == some .patVar || c.syntaxKind? == some .field
              let paramGroups ← varNodes.mapM fun (v, vo) => do
                let vspan ← spanFor v vo
                match v.syntaxKind? with
                | some .patVar =>
                    match firstGreenChild v with
                    | some child =>
                        let text ← getGreenTokenText child vo
                        pure #[({ name := ⟨#[], text, vspan⟩, type? := none, span := vspan } : DefParam)]
                    | none =>
                        lowerError "patVar missing name" vspan
                        pure #[({ name := ⟨#[], "_error", vspan⟩, type? := none, span := vspan } : DefParam)]
                | some .field =>
                    let kids := childrenWithOffsets v vo |>.filter fun (c, _) => isSemanticNode c
                    let nameNodes := kids.filter fun (c, _) => isTokenKind c .lowerIdent
                    let typeNode? := kids.find? fun (c, _) =>
                      match c.syntaxKind? with
                      | some .typeQuantity => false
                      | some sk => sk.isType
                      | none => false
                    let lbraceCount := v.children.foldl (init := 0) fun n c =>
                      if isTokenKind c .leftBrace then n + 1 else n
                    let isInstance := lbraceCount == 2
                    let isImplicit := lbraceCount >= 1
                    let quantityOpt? := kids.find? fun (c, _) => c.syntaxKind? == some .typeQuantity
                    let quantity? ← match quantityOpt? with
                      | some (qNode, qOffset) =>
                        let qText ← getGreenTokenText (firstGreenChild qNode |>.getD qNode) qOffset
                        pure (some (match qText with
                          | "0" => Soma.Core.Quantity.zero
                          | "1" => Soma.Core.Quantity.one
                          | _ => Soma.Core.Quantity.omega))
                      | none => pure none
                    let tyOpt ← match typeNode? with
                      | some (tyNode, tyOffset) => some <$> lowerTypeExpr tyNode tyOffset
                      | none => pure none
                    if nameNodes.isEmpty then
                      if isInstance then
                        pure #[({ name := ⟨#[], s!"_inst_{vspan.start}", vspan⟩
                                 , type? := tyOpt, isImplicit := true
                                 , isInstance := true
                                 , quantity? := quantity?, span := vspan } : DefParam)]
                      else
                        lowerError "field missing name" vspan
                        pure #[({ name := ⟨#[], "_error", vspan⟩, type? := none, span := vspan } : DefParam)]
                    else
                      nameNodes.mapM fun (nameNode, nameOffset) => do
                        let nameText ← getGreenTokenText nameNode nameOffset
                        pure ({ name := ⟨#[], nameText, vspan⟩
                              , type? := tyOpt, isImplicit, isInstance
                              , quantity? := quantity?, span := vspan } : DefParam)
                | _ =>
                    lowerError "unexpected node in param list" vspan
                    pure #[({ name := ⟨#[], "_error", vspan⟩, type? := none, span := vspan } : DefParam)]
              pure (paramGroups.flatten)

          -- Extract signature base from either `::` or `->` notation
          let sigNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .signature
          let mut returnTypeSig : Option Expr := none
          let mut explicitSig : Option Expr := none
          for (sigNode, sigOffset) in sigNodes do
            let sigTy ← lowerTypeExpr sigNode sigOffset
            let sigKind := match sigNode.children[0]? with
              | some (.token k _) => some k
              | _ => none
            match sigKind with
            | some .arrow => if returnTypeSig.isNone then returnTypeSig := some sigTy
            | some .doubleColon => if explicitSig.isNone then explicitSig := some sigTy
            | _ => if explicitSig.isNone then explicitSig := some sigTy

          let typedParams := headerParams.filter (·.type?.isSome)
          let sigBase := explicitSig.orElse (fun _ => returnTypeSig)
          let sig ← match sigBase with
            | none => pure none
            | some retTy =>
              if typedParams.isEmpty then
                pure (some retTy)
              else
                let fullSig := typedParams.foldr (init := retTy) fun param accTy =>
                  let binder : Soma.Core.BinderInfo :=
                    if param.isInstance then .instance_
                    else if param.isImplicit then .implicit
                    else .explicit
                  let qty := param.quantity?.getD .omega
                  Expr.pi qty binder param.name (param.type?.getD accTy) accTy span
                pure (some fullSig)

          let clauseNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .defClause
          let clauses ← clauseNodes.mapM fun (c, o) => lowerDefClause c o

          if clauses.isEmpty then
            let bodyNodes := allKids.filter fun (c, _) =>
              c.syntaxKind? != some .name && c.syntaxKind? != some .operatorName &&
              c.syntaxKind? != some .signature && c.syntaxKind? != some .attribute &&
              c.syntaxKind? != some .paramList && isSemanticNode c
            if bodyNodes.isEmpty then
              pure (mkDecl attrs name headerParams sig #[] span)
            else
              let body ← lowerExpr bodyNodes[0]!.1 bodyNodes[0]!.2
              let clause : DefClause := ⟨#[], none, body, body.span⟩
              pure (mkDecl attrs name headerParams sig #[clause] span)
          else
            pure (mkDecl attrs name headerParams sig clauses span)

      | .declInductive =>
          let nameNodes := green.children.filter fun c =>
            isTokenKind c .upperIdent || c.syntaxKind? == some .typeCon
          let name ← if nameNodes.isEmpty then
            lowerError "inductive type missing name" span
            pure ⟨#[], "_Error", span⟩
          else
            -- Use getTokenText to handle both raw tokens and triviaToken wrappers
            match getTokenText nameNodes[0]! with
            | some text => pure ⟨#[], text, span⟩
            | none =>
                match firstGreenChild nameNodes[0]! with
                | some child =>
                    let text ← getGreenTokenText child offset
                    pure ⟨#[], text, span⟩
                | none =>
                    lowerError "inductive type missing name" span
                    pure ⟨#[], "_Error", span⟩

          let allKids := childrenWithOffsets green offset
          let paramNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .tyParamList
          let params ← if paramNodes.isEmpty then pure #[]
            else
              let (plist, plistOffset) := paramNodes[0]!
              lowerTypeParams plist plistOffset

          let conNodes := allKids.filter fun (c, _) =>
            c.syntaxKind? == some .constructor || c.syntaxKind? == some .constructorSig
          let cons ← conNodes.mapM fun (c, o) => lowerDataCon c o

          -- Extract kind annotation if present (e.g., :: * -> *)
          let sigNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .signature
          let kindAnnot ← if sigNodes.isEmpty then pure none
            else
              let (sig, sigOffset) := sigNodes[0]!
              let tyNodes := childrenWithOffsets sig sigOffset |>.filter fun (c, _) =>
                match c.syntaxKind? with
                | some sk => sk.isType
                | none => false
              if tyNodes.isEmpty then pure none
              else
                let kind ← lowerTypeExpr tyNodes[0]!.1 tyNodes[0]!.2
                pure (some kind)

          -- Extract attributes
          let attrNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .attribute
          let attrs ← lowerAttributes attrNodes
          pure (.inductive attrs name params cons kindAnnot span)

      | .declStruct =>
          let nameNodes := green.children.filter fun c => isTokenKind c .upperIdent
          if nameNodes.isEmpty then
            lowerError "record missing name" span
            pure (.record #[] ⟨#[], "_Error", span⟩ #[] ⟨#[], "_Error", span⟩ #[] span)
          else
            let name ← match getTokenText nameNodes[0]! with
            | some text => pure text
            | none => pure "_Error"

            let allKids := childrenWithOffsets green offset
            let paramNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .tyParamList
            let params ← if paramNodes.isEmpty then pure #[]
              else
                let (plist, plistOffset) := paramNodes[0]!
                lowerTypeParams plist plistOffset
            let fieldNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .field
            let fields ← fieldNodes.mapM fun (c, o) => lowerRecordField c o

            -- Extract attributes
            let attrNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .attribute
            let attrs ← lowerAttributes attrNodes
            -- Constructor is canonically "New"; the name field is unused downstream
            pure (.record attrs ⟨#[], name, span⟩ params ⟨#[], name, span⟩ fields span)

      | .declTrait =>
          let nameNodes := green.children.filter fun c => isTokenKind c .upperIdent
          let name ← if nameNodes.isEmpty then
            pure ⟨#[], "_Error", span⟩
          else
            match getTokenText nameNodes[0]! with
            | some text => pure ⟨#[], text, span⟩
            | none => pure ⟨#[], "_Error", span⟩

          let allKids := childrenWithOffsets green offset
          let paramNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .tyParamList
          let params ← if paramNodes.isEmpty then pure #[]
            else
              let (plist, plistOffset) := paramNodes[0]!
              lowerTypeParams plist plistOffset

          let methodNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .traitMethod
          let methods ← methodNodes.mapM fun (m, mo) => do
            let mspan ← spanFor m mo
            let mAllKids := childrenWithOffsets m mo
            let nameN := mAllKids.filter fun (c, _) => c.syntaxKind? == some .name
            let opNameN := mAllKids.filter fun (c, _) => c.syntaxKind? == some .operatorName
            let sigN := mAllKids.filter fun (c, _) => c.syntaxKind? == some .signature
            let mname ← if !nameN.isEmpty then
                let (n, no) := nameN[0]!
                match firstGreenChild n with
                | some child =>
                    let text ← getGreenTokenText child no
                    let nspan ← spanFor n no
                    pure ⟨#[], text, nspan⟩
                | none => pure ⟨#[], "_", mspan⟩
              else if !opNameN.isEmpty then
                let (opNode, oo) := opNameN[0]!
                let opTokens := opNode.children.filter fun c => isTokenKind c .varSymbol
                if opTokens.isEmpty then pure ⟨#[], "_", mspan⟩
                else
                  match getTokenText opTokens[0]! with
                  | some text =>
                      let ospan ← spanFor opNode oo
                      pure ⟨#[], text, ospan⟩
                  | none => pure ⟨#[], "_", mspan⟩
              else pure ⟨#[], "_", mspan⟩
            let mtype ← if sigN.isEmpty then pure (.var ⟨#[], "_", mspan⟩)
              else lowerTypeExpr sigN[0]!.1 sigN[0]!.2
            pure ⟨mname, mtype, mspan⟩

          -- Extract attributes
          let attrNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .attribute
          let attrs ← lowerAttributes attrNodes
          pure (.trait attrs name params methods span)

      | .declInstance =>
          let allKids := childrenWithOffsets green offset

          -- Check for optional instance name (a lowerIdent token directly under declInstance)
          -- Named instances have a bare lowerIdent token as a child (not wrapped in a node)
          let instanceName ← do
            let nameTokens := allKids.filter fun (c, _) =>
              isTokenKind c .lowerIdent
            if nameTokens.isEmpty then pure none
            else
              let (tok, tokOffset) := nameTokens[0]!
              match getTokenText tok with
              | some text =>
                let nspan ← spanFor tok tokOffset
                pure (some ⟨#[], text, nspan⟩)
              | none => pure none

          -- Lower instance binders: {a : Type} and {{d : Display a}}
          let mut binders : Array InstanceBinder := #[]
          -- Process all binder nodes in source order
          for (child, childOffset) in allKids do
            match child.syntaxKind? with
            | some .instTypeVarBinder =>
              -- {name : kind} — children: lbrace, nameTok, colon, kindTy, rbrace
              let semanticKids := childrenWithOffsets child childOffset
                |>.filter fun (c, _) => isSemanticNode c || isTokenKind c .lowerIdent
              let bspan ← spanFor child childOffset
              if semanticKids.size >= 2 then
                -- First semantic child should be the lowerIdent name
                let nameText ← do
                  let (nc, noff) := semanticKids[0]!
                  match getTokenText nc with
                  | some t => pure t
                  | none =>
                    -- try nested
                    match firstGreenChild nc with
                    | some inner => getGreenTokenText inner noff
                    | none => pure "_error"
                let nspan ← spanFor semanticKids[0]!.1 semanticKids[0]!.2
                -- Second semantic child is the kind type
                let (kindNode, kindOffset) := semanticKids[1]!
                let kindTy ← lowerTypeExpr kindNode kindOffset
                binders := binders.push (.typeVar ⟨#[], nameText, nspan⟩ kindTy bspan)
              else
                lowerError "malformed type variable binder" bspan

            | some .instDictBinder =>
              -- {{name : Constraint}} or {{Constraint}}
              -- Children vary: lbrace1, lbrace2, [nameTok, colonTok,] constraintNode, rbrace1, rbrace2
              let bspan ← spanFor child childOffset
              let constraintKids := childrenWithOffsets child childOffset
                |>.filter fun (c, _) => c.syntaxKind? == some .constraint
              let nameKids := child.children.filter fun c =>
                isTokenKind c .lowerIdent
              let dictName ← if nameKids.isEmpty then pure none
                else match getTokenText nameKids[0]! with
                  | some text =>
                    let nspan ← spanFor nameKids[0]! childOffset
                    pure (some ⟨#[], text, nspan⟩)
                  | none => pure none
              if constraintKids.isEmpty then
                lowerError "missing constraint in dict binder" bspan
              else
                let (cnode, coffset) := constraintKids[0]!
                let constraint ← lowerConstraint cnode coffset
                binders := binders.push (.dictParam dictName constraint bspan)
            | _ => pure ()

          -- Lower the trait head (the constraint node after the colon)
          let constraintNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .constraint
          let (traitName, args) ← if constraintNodes.isEmpty then
            pure (⟨#[], "_Error", span⟩, #[])
          else
            let c ← lowerConstraint constraintNodes[0]!.1 constraintNodes[0]!.2
            pure (c.className, c.args)

          let methodNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .declDef
          let methods ← methodNodes.mapM fun (c, o) => lowerDecl c o

          pure (.instance_ instanceName binders traitName args methods span)

      | .declUse =>
          let allKids := childrenWithOffsets green offset
          let isPublic := allKids.any fun (c, _) =>
            match c with
            | .token k _ => k == .kw_pub
            | _ => false
          let pathNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .importPath
          let itemNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .importItems

          let path ← if pathNodes.isEmpty then
            pure ⟨#[], "_error", span⟩
          else
            let (pnode, _) := pathNodes[0]!
            -- Extract all identifier tokens from the path, including nested nodes
            -- Filter to only name-like tokens (lowerIdent, upperIdent, varSymbol)
            let segments := pnode.children.foldl (init := #[]) fun acc c =>
              match c with
              | .token k text => if k.isNameLike then acc.push text else acc
              | .node _ children _ => children.foldl (fun a c2 =>
                  match c2 with
                  | .token k2 text2 => if k2.isNameLike then a.push text2 else a
                  | _ => a) acc
              | _ => acc
            if segments.isEmpty then
              pure ⟨#[], "_error", span⟩
            else
              let pathArr := segments[0:segments.size-1].toArray
              let name := segments[segments.size-1]!
              let pspan ← spanFor pnode offset
              pure ⟨pathArr, name, pspan⟩

          let items ← if itemNodes.isEmpty then pure #[]
            else
              let (ilist, ilistOffset) := itemNodes[0]!
              let iAllKids := childrenWithOffsets ilist ilistOffset
              let names := iAllKids.filter fun (c, _) =>
                c.syntaxKind? == some .name || c.syntaxKind? == some .operatorName
              names.mapM fun (n, no) => do
                match firstGreenChild n with
                | some child =>
                    let text ← getGreenTokenText child no
                    let nspan ← spanFor n no
                    pure ⟨#[], text, nspan⟩
                | none =>
                    let nspan ← spanFor n no
                    pure ⟨#[], "_", nspan⟩

          pure (.use isPublic path items span)

      | .declAbbrev =>
          -- Structure: [abbrevTok, nameTok, optional tyParamList, eqTok, type]
          let nameNodes := green.children.filter fun c => isTokenKind c .upperIdent
          let name ← if nameNodes.isEmpty then
            lowerError "abbreviation missing name" span
            pure ⟨#[], "_Error", span⟩
          else
            match getTokenText nameNodes[0]! with
            | some text => pure ⟨#[], text, span⟩
            | none =>
                lowerError "abbreviation missing name" span
                pure ⟨#[], "_Error", span⟩

          let allKids := childrenWithOffsets green offset
          let paramNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .tyParamList
          let params ← if paramNodes.isEmpty then pure #[]
            else
              let (plist, plistOffset) := paramNodes[0]!
              let varNodes := childrenWithOffsets plist plistOffset |>.filter fun (c, _) =>
                c.syntaxKind? == some .typeVar
              varNodes.mapM fun (v, vo) => do
                match firstGreenChild v with
                | some child =>
                    let text ← getGreenTokenText child vo
                    let vspan ← spanFor v vo
                    pure ⟨#[], text, vspan⟩
                | none =>
                    let vspan ← spanFor v vo
                    pure ⟨#[], "_", vspan⟩

          -- Find the type (last semantic node that is a type)
          let typeNodes := allKids.filter fun (c, _) =>
            match c.syntaxKind? with
            | some sk => sk.isType
            | none => false
          if typeNodes.isEmpty then
            lowerError "abbreviation missing type" span
            pure (.abbrev name params (.var ⟨#[], "_error", span⟩) span)
          else
            let ty ← lowerTypeExpr typeNodes[0]!.1 typeNodes[0]!.2
            pure (.abbrev name params ty span)

      | _ =>
          lowerError s!"unexpected declaration kind: {kind}" span
          pure (.use false ⟨#[], "_error", span⟩ #[] span)

  | .error message _ _ =>
      lowerError message span
      pure (.use false ⟨#[], "_error", span⟩ #[] span)

  | .missing expected =>
      lowerError s!"missing {expected}" span
      pure (.use false ⟨#[], "_error", span⟩ #[] span)

  | .token kind _ =>
      lowerError s!"unexpected token at declaration level: {kind}" span
      pure (.use false ⟨#[], "_error", span⟩ #[] span)

/-- Lower a module from a green tree -/
def lowerModule (green : GreenNode) (offset : Nat) (moduleName : String) : LowerM Module := do
  let span ← spanFor green offset

  match green with
  | .node .sourceFile _ _ =>
      let childrenOff := childrenWithOffsets green offset
      let decls ← childrenOff.filterMapM fun (c, co) => do
        match c with
        | .error message _ _ =>
            let cspan ← spanFor c co
            lowerError message cspan
            pure none
        | .missing expected =>
            let cspan ← spanFor c co
            lowerError s!"missing {expected}" cspan
            pure none
        | .token .eof _ =>
            -- Skip EOF token (it's only there to carry trailing trivia for width)
            pure none
        | .node .triviaToken _ _ =>
            -- Skip triviaToken wrappers around EOF (trailing trivia)
            let inner := unwrapTrivia c
            if inner.tokenKind? == some .eof then pure none
            else some <$> lowerDecl c co
        | _ =>
            some <$> lowerDecl c co
      pure ⟨moduleName, decls, span⟩

  | _ =>
      lowerError "expected source file" span
      pure ⟨moduleName, #[], span⟩

/--
Lower a CST to an AST.
Always succeeds, returning an AST (possibly with error nodes) and diagnostics.
This enables LSP features to work even with syntax errors.
-/
def lower (tree : ParsedTree) (moduleName : String := "Main") : Module × Diagnostics :=
  let ctx : LowerContext := { source := tree.red.source, redTree := tree.red }
  (lowerModule tree.green 0 moduleName).run' ctx

/-- Lower a green tree directly (for testing the trivia invariant) -/
def lowerGreen (green : GreenNode) (source : SourceFile) (moduleName : String := "Main") : Module × Diagnostics :=
  let red := buildRedTree green source
  let ctx : LowerContext := { source := source, redTree := red }
  (lowerModule green 0 moduleName).run' ctx

/- todo: implement -/
-- theorem lower_trivia_invariant (green : GreenNode) (source : SourceFile) (moduleName : String) :
--     (lowerGreen (green.stripTrivia) source moduleName).1 =
--     (lowerGreen green source moduleName).1 := by
--   sorry

/-- Lower a single declaration from a RedNode -/
def lowerDeclFromRedNode (tree : ParsedTree) (node : RedNode) : Option (Decl × Diagnostics) :=
  match node.syntaxKind? with
  | some kind =>
    if kind.isDecl then
      let ctx : LowerContext := { source := tree.red.source, redTree := tree.red }
      some ((lowerDecl node.green node.offset).run' ctx)
    else
      none
  | none => none

/-- Lower specific declarations by their NodeIds -/
def lowerDeclarationsByIds (tree : ParsedTree) (declIds : Array NodeId)
    : Std.HashMap NodeId Decl × Diagnostics := Id.run do
  let mut result : Std.HashMap NodeId Decl := {}
  let mut allDiags : Diagnostics := #[]

  for nodeId in declIds do
    match tree.red.getById? nodeId with
    | some node =>
      match lowerDeclFromRedNode tree node with
      | some (decl, diags) =>
        result := result.insert nodeId decl
        allDiags := allDiags ++ diags
      | none => pure ()
    | none => pure ()

  return (result, allDiags)

/-- Collect all top-level declaration NodeIds from a parsed tree -/
def collectDeclNodeIds (tree : ParsedTree) : Array NodeId := Id.run do
  let mut declIds : Array NodeId := #[]
  -- The root should be a sourceFile node
  match tree.red.root with
  | some root =>
    -- Iterate through top-level children (declarations)
    let mut idx := root.selfIdx + 1
    for child in root.green.children do
      if h : idx < tree.red.nodes.size then
        let childNode := tree.red.nodes[idx]
        match childNode.syntaxKind? with
        | some kind =>
          if kind.isDecl then
            declIds := declIds.push childNode.id
        | none => pure ()
        idx := idx + RedTree.countGreenNodes child
    return declIds
  | none => return #[]

/-- Build a Module AST from a map of declaration ASTs (in source order) -/
def buildModuleFromDeclMap (tree : ParsedTree) (declAsts : Std.HashMap NodeId Decl)
    (moduleName : String) : Module := Id.run do
  let declIds := collectDeclNodeIds tree
  let decls := declIds.filterMap fun nodeId => declAsts.get? nodeId
  let span := match tree.red.root with
    | some root => root.span tree.red.source
    | none => panic! "buildModuleFromDeclMap: ParsedTree has no root"
  return { name := moduleName, decls := decls, span := span }

end Soma.Syntax
