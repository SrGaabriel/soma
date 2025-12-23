import Soma.Syntax.Source
import Soma.Syntax.Diagnostic
import Soma.Syntax.SyntaxKind
import Soma.Syntax.GreenTree
import Soma.Syntax.RedTree
import Soma.Syntax.Ast

namespace Soma.Syntax

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
  if green.isToken || green.isTrivia then false
  else if green.syntaxKind? == some .triviaToken then
    -- Operators (.varSymbol) are NOT semantic since they are handled specially in exprInfix
    match getTokenKind green with
    | some .lowerIdent | some .upperIdent | some .number | some .true_ | some .false_ => true
    | some (.string _) => true
    | _ => false  -- punctuation and operators wrapped in trivia are not semantic nodes
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
      | .lowerIdent => pure (.var ⟨text, span⟩)
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

  | .node kind children _ =>
      match kind with
      | .patVar =>
          match firstGreenChild green with
          | some child =>
              let text ← getGreenTokenText child offset
              pure (.var ⟨text, span⟩)
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
          let syntaxKids := syntaxGreenChildren green
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "constructor pattern missing name" span
            pure (.wildcard span)
          else
            let (nameNode, nameOffset) := kidsWithOffsets[0]!
            match firstGreenChild nameNode with
            | some nameChild =>
                let name ← getGreenTokenText nameChild nameOffset
                let nameSpan ← spanFor nameNode nameOffset
                let args ← kidsWithOffsets[1:].toArray.mapM fun (c, o) => lowerPattern c o
                pure (.con ⟨name, nameSpan⟩ args span)
            | none =>
                lowerError "constructor pattern missing name" span
                pure (.wildcard span)

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

      | .name =>
          match firstGreenChild green with
          | some child =>
              let text ← getGreenTokenText child offset
              if text.length > 0 && (String.Pos.Raw.get text ⟨0⟩).isUpper then
                pure (.con ⟨text, span⟩ #[] span)
              else
                pure (.var ⟨text, span⟩)
          | none =>
              lowerError "name missing text" span
              pure (.wildcard span)

      | _ =>
          lowerError s!"unexpected pattern kind: {kind}" span
          pure (.wildcard span)

  | .error message _ _ =>
      lowerError message span
      pure (.wildcard span)

  | .missing expected =>
      lowerError s!"missing {expected}" span
      pure (.wildcard span)

/-- Lower a CST type to AST TypeExpr -/
partial def lowerTypeExpr (green : GreenNode) (offset : Nat) : LowerM TypeExpr := do
  -- For triviaToken, recurse immediately with adjusted offset (don't compute span yet)
  if green.syntaxKind? == some .triviaToken then
    let unwrapped := unwrapTrivia green
    let adjustedOffset := offset + triviaOffset green
    return ← lowerTypeExpr unwrapped adjustedOffset

  let span ← spanFor green offset

  match green with
  | .token kind text =>
      match kind with
      | .lowerIdent => pure (.var ⟨text, span⟩)
      | .upperIdent => pure (.con ⟨text, span⟩)
      | _ =>
          lowerError s!"unexpected token in type: {kind}" span
          pure (.var ⟨"_error", span⟩)

  | .node .triviaToken _ _ => pure (.var ⟨"_error", span⟩)

  | .node kind _children _ =>
      match kind with
      | .typeVar =>
          match firstGreenChild green with
          | some child =>
              let text ← getGreenTokenText child offset
              pure (.var ⟨text, span⟩)
          | none =>
              lowerError "type variable missing name" span
              pure (.var ⟨"_error", span⟩)

      | .typeCon =>
          match firstGreenChild green with
          | some child =>
              let text ← getGreenTokenText child offset
              pure (.con ⟨text, span⟩)
          | none =>
              lowerError "type constructor missing name" span
              pure (.var ⟨"_error", span⟩)

      | .typeApp =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "empty type application" span
            pure (.var ⟨"_error", span⟩)
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
            pure (.var ⟨"_error", span⟩)

      | .typeTuple =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          let elems ← kidsWithOffsets.mapM fun (c, o) => lowerTypeExpr c o
          pure (.tuple elems span)

      | .typeList =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "list type requires element type" span
            pure (.var ⟨"_error", span⟩)
          else
            let elem ← lowerTypeExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            pure (.list elem span)

      | .typeForall =>
          let allKids := childrenWithOffsets green offset
          let varNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .typeVar
          let bodyNodes := allKids.filter fun (c, _) =>
            c.syntaxKind? != some .typeVar && c.syntaxKind? != some .tyParamList && isSemanticNode c
          let vars ← varNodes.mapM fun (v, o) => do
            match firstGreenChild v with
            | some child =>
                let text ← getGreenTokenText child o
                let vspan ← spanFor v o
                pure ⟨text, vspan⟩
            | none =>
                let vspan ← spanFor v o
                pure ⟨"_", vspan⟩
          if bodyNodes.isEmpty then
            lowerError "forall type requires body" span
            pure (.var ⟨"_error", span⟩)
          else
            let body ← lowerTypeExpr bodyNodes[0]!.1 bodyNodes[0]!.2
            pure (.forall_ vars body span)

      | .typeConstrained =>
          let allKids := childrenWithOffsets green offset
          let bodyNodes := allKids.filter fun (c, _) =>
            c.syntaxKind? != some .constraintList && c.syntaxKind? != some .constraint && isSemanticNode c
          let constraintNodes := allKids.filter fun (c, _) =>
            c.syntaxKind? == some .constraintList || c.syntaxKind? == some .constraint
          let constraints ← constraintNodes.mapM fun (cn, co) => do
            let c ← lowerConstraint cn co
            pure (c.className, c.args, c.span)
          if bodyNodes.isEmpty then
            lowerError "constrained type requires body" span
            pure (.var ⟨"_error", span⟩)
          else
            let body ← lowerTypeExpr bodyNodes[0]!.1 bodyNodes[0]!.2
            pure (.constrained constraints body span)

      | .typeParens =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            pure (.tuple #[] span)
          else
            let inner ← lowerTypeExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            pure (.parens inner span)

      | .signature =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "signature missing type" span
            pure (.var ⟨"_error", span⟩)
          else
            lowerTypeExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2

      | _ =>
          lowerError s!"unexpected type kind: {kind}" span
          pure (.var ⟨"_error", span⟩)

  | .error message _ _ =>
      lowerError message span
      pure (.var ⟨"_error", span⟩)

  | .missing expected =>
      lowerError s!"missing {expected}" span
      pure (.var ⟨"_error", span⟩)

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
          pure ⟨⟨"_error", span⟩, #[], span⟩
        else
          match getTokenText tokenKids[0]! with
          | some text => pure ⟨⟨text, span⟩, #[], span⟩
          | none => pure ⟨⟨"_error", span⟩, #[], span⟩
      else
        let (classNode, classOffset) := kidsWithOffsets[0]!
        let className ← match classNode.syntaxKind? with
        | some .typeCon =>
            match firstGreenChild classNode with
            | some child =>
                let text ← getGreenTokenText child classOffset
                let cspan ← spanFor classNode classOffset
                pure ⟨text, cspan⟩
            | none => pure ⟨"_error", span⟩
        | _ =>
            match getTokenText classNode with
            | some text =>
                let cspan ← spanFor classNode classOffset
                pure ⟨text, cspan⟩
            | none =>
                lowerError "expected class name in constraint" span
                pure ⟨"_error", span⟩
        let args ← kidsWithOffsets[1:].toArray.mapM fun (c, o) => lowerTypeExpr c o
        pure ⟨className, args, span⟩

  | .node .constraintList _ _ =>
      let constraintNodes := childrenOfGreenKind green .constraint
      if !constraintNodes.isEmpty then
        -- Find offset of first constraint
        let allKids := childrenWithOffsets green offset
        match allKids.find? fun (c, _) => c.syntaxKind? == some .constraint with
        | some (c, o) => lowerConstraint c o
        | none => pure ⟨⟨"_error", span⟩, #[], span⟩
      else
        let nestedLists := childrenOfGreenKind green .constraintList
        if !nestedLists.isEmpty then
          let allKids := childrenWithOffsets green offset
          match allKids.find? fun (c, _) => c.syntaxKind? == some .constraintList with
          | some (c, o) => lowerConstraint c o
          | none => pure ⟨⟨"_error", span⟩, #[], span⟩
        else
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "empty constraint list" span
            pure ⟨⟨"_error", span⟩, #[], span⟩
          else
            lowerConstraint kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2

  | .node kind _ _ =>
      if kind == .typeApp || kind == .typeCon || kind == .typeVar then
        let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
        if kidsWithOffsets.isEmpty then
          match kind with
          | .typeCon =>
              match firstGreenChild green with
              | some child =>
                  let text ← getGreenTokenText child offset
                  pure ⟨⟨text, span⟩, #[], span⟩
              | none =>
                  lowerError "expected constraint" span
                  pure ⟨⟨"_error", span⟩, #[], span⟩
          | _ =>
              lowerError "expected constraint" span
              pure ⟨⟨"_error", span⟩, #[], span⟩
        else
          let (classNode, classOffset) := kidsWithOffsets[0]!
          let className ← match classNode.syntaxKind? with
          | some .typeCon =>
              match firstGreenChild classNode with
              | some child =>
                  let text ← getGreenTokenText child classOffset
                  let cspan ← spanFor classNode classOffset
                  pure ⟨text, cspan⟩
              | none => pure ⟨"_error", span⟩
          | _ =>
              match getTokenText classNode with
              | some text =>
                  let cspan ← spanFor classNode classOffset
                  pure ⟨text, cspan⟩
              | none =>
                  match firstGreenChild classNode with
                  | some child =>
                      let text ← getGreenTokenText child classOffset
                      let cspan ← spanFor classNode classOffset
                      pure ⟨text, cspan⟩
                  | none => pure ⟨"_error", span⟩
          let args ← kidsWithOffsets[1:].toArray.mapM fun (c, o) => lowerTypeExpr c o
          pure ⟨className, args, span⟩
      else
        lowerError s!"unexpected constraint node kind: {kind}" span
        pure ⟨⟨"_error", span⟩, #[], span⟩

  | .token kind text =>
      if kind == .upperIdent then
        pure ⟨⟨text, span⟩, #[], span⟩
      else
        lowerError s!"unexpected token in constraint: {kind}" span
        pure ⟨⟨"_error", span⟩, #[], span⟩

  | _ =>
      lowerError "unexpected constraint node" span
      pure ⟨⟨"_error", span⟩, #[], span⟩

end

/-- Lower a data constructor -/
partial def lowerDataCon (green : GreenNode) (offset : Nat) : LowerM DataCon := do
  let span ← spanFor green offset

  match green with
  | .node .constructor _ _ =>
      let nameNodes := green.children.filter fun c => isTokenKind c .upperIdent
      let name := if nameNodes.isEmpty then ⟨"_Con", span⟩
        else match getTokenText nameNodes[0]! with
        | some text => ⟨text, span⟩
        | none => ⟨"_Con", span⟩

      let allKids := childrenWithOffsets green offset
      let fieldNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .field
      let fields ← fieldNodes.mapM fun (f, fo) => do
        let fKids := childrenWithOffsets f fo |>.filter fun (c, _) => isSemanticNode c
        if fKids.size >= 2 then
          match firstGreenChild fKids[0]!.1 with
          | some nameChild =>
              let fname ← getGreenTokenText nameChild fKids[0]!.2
              let fnameSpan ← spanFor fKids[0]!.1 fKids[0]!.2
              let ftype ← lowerTypeExpr fKids[1]!.1 fKids[1]!.2
              pure (some ⟨fname, fnameSpan⟩, ftype)
          | none =>
              let ftype ← lowerTypeExpr fKids[1]!.1 fKids[1]!.2
              pure (none, ftype)
        else if fKids.size == 1 then
          let ftype ← lowerTypeExpr fKids[0]!.1 fKids[0]!.2
          pure (none, ftype)
        else
          let fspan ← spanFor f fo
          pure (none, .var ⟨"_", fspan⟩)

      pure ⟨name, fields, span⟩

  | _ =>
      lowerError "expected constructor" span
      pure ⟨⟨"_Con", span⟩, #[], span⟩

/-- Lower a struct field -/
partial def lowerStructField (green : GreenNode) (offset : Nat) : LowerM StructField := do
  let span ← spanFor green offset
  let fKids := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c

  -- Look for name token
  let nameTokens := green.children.filter fun c => isTokenKind c .lowerIdent
  let fname ← if nameTokens.isEmpty then pure none
    else match getTokenText nameTokens[0]! with
    | some text => pure (some ⟨text, span⟩)
    | none => pure none

  if fKids.size >= 1 then
    let ftype ← lowerTypeExpr fKids[0]!.1 fKids[0]!.2
    pure ⟨fname, ftype, span⟩
  else
    lowerError "struct field missing type" span
    pure ⟨none, .var ⟨"_", span⟩, span⟩

/-- Lower a token to an expression -/
def lowerExprToken (kind : TokenKind) (text : String) (span : Span) : LowerM Expr := do
  match kind with
  | .lowerIdent => pure (.var ⟨text, span⟩)
  | .upperIdent => pure (.var ⟨text, span⟩)
  | .number => pure (.lit (.int text.toInt! span))
  | .string s => pure (.lit (.string s span))
  | .true_ => pure (.lit (.bool true span))
  | .false_ => pure (.lit (.bool false span))
  | _ =>
      lowerError s!"unexpected token in expression: {kind}" span
      pure (.var ⟨"_error", span⟩)

/-- Lower a single parameter -/
def lowerSingleParam (green : GreenNode) (offset : Nat) : LowerM (Name × Option TypeExpr) := do
  let span ← spanFor green offset
  match green.syntaxKind? with
  | some .patVar =>
      match firstGreenChild green with
      | some child =>
          let name ← getGreenTokenText child offset
          pure (⟨name, span⟩, none)
      | none => pure (⟨"_", span⟩, none)
  | some .field =>
      let tokenKids := green.children.filter fun c => isTokenKind c .lowerIdent
      if tokenKids.isEmpty then
        pure (⟨"_", span⟩, none)
      else
        match getTokenText tokenKids[0]! with
        | some text =>
            let typeNodes := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
            if typeNodes.size >= 1 then
              let ty ← lowerTypeExpr typeNodes[0]!.1 typeNodes[0]!.2
              pure (⟨text, span⟩, some ty)
            else
              pure (⟨text, span⟩, none)
        | none => pure (⟨"_", span⟩, none)
  | _ => pure (⟨"_", span⟩, none)

/-- Lower lambda parameters -/
def lowerLambdaParams (paramNodes : Array (GreenNode × Nat)) : LowerM (Array (Name × Option TypeExpr)) := do
  let mut result : Array (Name × Option TypeExpr) := #[]
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
        result := result.push (⟨"_", span⟩, none)
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
      pure (.var ⟨"_error", span⟩)

  | .node kind children _ =>
      match kind with
      | .exprVar =>
          match firstGreenChild green with
          | some child =>
              let text ← getGreenTokenText child offset
              pure (.var ⟨text, span⟩)
          | none =>
              lowerError "variable missing name" span
              pure (.var ⟨"_error", span⟩)

      | .exprLit =>
          match firstGreenChild green with
          | some child => lowerExpr child offset
          | none =>
              lowerError "literal missing value" span
              pure (.var ⟨"_error", span⟩)

      | .exprApp =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size < 2 then
            lowerError "application requires function and argument" span
            pure (.var ⟨"_error", span⟩)
          else
            let fn ← lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let arg ← lowerExpr kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            pure (.app fn arg span)

      | .exprInfix =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          let opNode := children.find? fun c => isTokenKind c .varSymbol
          match opNode, opNode.bind getTokenText with
          | some _, some opText =>
              if kidsWithOffsets.size >= 2 then
                let left ← lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
                let right ← lowerExpr kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
                pure (.infix ⟨opText, span⟩ left right span)
              else
                lowerError "infix expression requires two operands" span
                pure (.var ⟨"_error", span⟩)
          | _, _ =>
              lowerError "infix expression missing operator" span
              pure (.var ⟨"_error", span⟩)

      | .exprLambda =>
          let allKids := childrenWithOffsets green offset
          let paramNodes := allKids.filter fun (c, _) =>
            c.syntaxKind? == some .paramList || c.syntaxKind? == some .patVar
          let bodyNodes := allKids.filter fun (c, _) =>
            c.syntaxKind? != some .paramList && c.syntaxKind? != some .patVar && isSemanticNode c
          let params ← lowerLambdaParams paramNodes
          if bodyNodes.isEmpty then
            lowerError "lambda missing body" span
            pure (.var ⟨"_error", span⟩)
          else
            let body ← lowerExpr bodyNodes[0]!.1 bodyNodes[0]!.2
            pure (.lambda params body span)

      | .exprLet =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size >= 2 then
            let (nameOrPat, nameOffset) := kidsWithOffsets[0]!
            let name ← match nameOrPat.syntaxKind? with
            | some .name | some .patVar =>
                match firstGreenChild nameOrPat with
                | some child =>
                    let text ← getGreenTokenText child nameOffset
                    let nspan ← spanFor nameOrPat nameOffset
                    pure ⟨text, nspan⟩
                | none =>
                    let nspan ← spanFor nameOrPat nameOffset
                    pure ⟨"_", nspan⟩
            | _ =>
                let nspan ← spanFor nameOrPat nameOffset
                pure ⟨"_", nspan⟩

            let sigNodes := kidsWithOffsets.filter fun (c, _) => c.syntaxKind? == some .signature
            let sig ← if sigNodes.isEmpty then pure none
              else some <$> lowerTypeExpr sigNodes[0]!.1 sigNodes[0]!.2

            let valueIdx := if sigNodes.isEmpty then 1 else 2
            if h : valueIdx < kidsWithOffsets.size then
              let value ← lowerExpr kidsWithOffsets[valueIdx].1 kidsWithOffsets[valueIdx].2
              let bodyIdx := valueIdx + 1
              if h2 : bodyIdx < kidsWithOffsets.size then
                let body ← lowerExpr kidsWithOffsets[bodyIdx].1 kidsWithOffsets[bodyIdx].2
                pure (.let_ name sig value body span)
              else
                lowerError "let missing body" span
                pure (.let_ name sig value (.var ⟨"_error", span⟩) span)
            else
              lowerError "let missing value" span
              pure (.var ⟨"_error", span⟩)
          else
            lowerError "let expression incomplete" span
            pure (.var ⟨"_error", span⟩)

      | .exprIf =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.size >= 3 then
            let cond ← lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            let then_ ← lowerExpr kidsWithOffsets[1]!.1 kidsWithOffsets[1]!.2
            let else_ ← lowerExpr kidsWithOffsets[2]!.1 kidsWithOffsets[2]!.2
            pure (.if_ cond then_ else_ span)
          else
            lowerError "if expression incomplete" span
            pure (.var ⟨"_error", span⟩)

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
            pure (.var ⟨"_error", span⟩)

      | .exprCompose =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "compose block empty" span
            pure (.var ⟨"_error", span⟩)
          else if kidsWithOffsets.size == 1 then
            let body ← lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            pure (.compose body span)
          else
            let stmts ← kidsWithOffsets.mapM fun (c, o) => lowerExpr c o
            let body := stmts[stmts.size - 1]!
            let initStmts := stmts[:stmts.size - 1].toArray.reverse
            let mut result : Expr := body
            for stmt in initStmts do
              match stmt with
              | .let_ name ty val _ stmtSpan =>
                  result := Expr.let_ name ty val result stmtSpan
              | other =>
                  result := Expr.let_ ⟨"_", other.span⟩ none other result other.span
            pure (.compose result span)

      | .exprBind =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if kidsWithOffsets.isEmpty then
            lowerError "bind block empty" span
            pure (.var ⟨"_error", span⟩)
          else if kidsWithOffsets.size == 1 then
            let body ← lowerExpr kidsWithOffsets[0]!.1 kidsWithOffsets[0]!.2
            pure (.bind body span)
          else
            let stmts ← kidsWithOffsets.mapM fun (c, o) => lowerExpr c o
            let body := stmts[stmts.size - 1]!
            let initStmts := stmts[:stmts.size - 1].toArray.reverse
            let mut result : Expr := body
            for stmt in initStmts do
              match stmt with
              | .let_ name ty val _ stmtSpan =>
                  result := Expr.let_ name ty val result stmtSpan
              | other =>
                  result := Expr.let_ ⟨"_", other.span⟩ none other result other.span
            pure (.bind result span)

      | .composeLetStmt =>
          let kidsWithOffsets := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          let nameTokens := green.children.filter fun c => isTokenKind c .lowerIdent
          if kidsWithOffsets.isEmpty then
            lowerError "compose let statement missing value" span
            pure (.var ⟨"_error", span⟩)
          else
            let (valueNode, valueOffset) := kidsWithOffsets[kidsWithOffsets.size - 1]!
            let value ← lowerExpr valueNode valueOffset
            if !nameTokens.isEmpty then
              match getTokenText nameTokens[0]! with
              | some text =>
                  pure (.let_ ⟨text, span⟩ none value (.var ⟨"_", span⟩) span)
              | none =>
                  lowerError "compose let missing binding name" span
                  pure (.var ⟨"_error", span⟩)
            else if kidsWithOffsets.size >= 2 then
              let (patNode, patOffset) := kidsWithOffsets[0]!
              match patNode.syntaxKind? with
              | some k =>
                  if k.isPattern then
                    match firstGreenChild patNode with
                    | some child =>
                        let patText ← getGreenTokenText child patOffset
                        pure (.let_ ⟨patText, span⟩ none value (.var ⟨"_", span⟩) span)
                    | none =>
                        pure (.let_ ⟨"_pat", span⟩ none value (.var ⟨"_", span⟩) span)
                  else
                    lowerError s!"unexpected node in compose let: {k}" span
                    pure (.var ⟨"_error", span⟩)
              | none =>
                  lowerError "compose let missing binding" span
                  pure (.var ⟨"_error", span⟩)
            else
              lowerError "compose let statement incomplete" span
              pure (.var ⟨"_error", span⟩)

      | .name =>
          match firstGreenChild green with
          | some child =>
              let text ← getGreenTokenText child offset
              pure (.var ⟨text, span⟩)
          | none =>
              lowerError "name missing text" span
              pure (.var ⟨"_error", span⟩)

      | _ =>
          lowerError s!"unexpected expression kind: {kind}" span
          pure (.var ⟨"_error", span⟩)

  | .error message _ _ =>
      lowerError message span
      pure (.var ⟨"_error", span⟩)

  | .missing expected =>
      lowerError s!"missing {expected}" span
      pure (.var ⟨"_error", span⟩)

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
          pure (.mk patterns guard (.var ⟨"_error", span⟩) span)
        else
          let body ← lowerExpr bodyNodes[0]!.1 bodyNodes[0]!.2
          pure (.mk patterns guard body span)

    | _ =>
        lowerError "expected match arm" span
        pure (.mk #[] none (.var ⟨"_error", span⟩) span)

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
    pure ⟨patterns, guard, .var ⟨"_error", span⟩, span⟩
  else
    let body ← lowerExpr bodyNodes[0]!.1 bodyNodes[0]!.2
    pure ⟨patterns, guard, body, span⟩

/-- Lower a declaration -/
partial def lowerDecl (green : GreenNode) (offset : Nat) : LowerM Decl := do
  let span ← spanFor green offset

  match green with
  | .node kind _children _ =>
      match kind with
      | .declDef =>
          let allKids := childrenWithOffsets green offset
          let attrNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .attribute
          let attrs ← attrNodes.mapM fun (a, ao) => do
            let aspan ← spanFor a ao
            let nameTokens := a.children.filter fun c => isTokenKind c .lowerIdent
            if nameTokens.isEmpty then
              pure ⟨⟨"unknown", aspan⟩, #[], aspan⟩
            else
              match getTokenText nameTokens[0]! with
              | some text => pure ⟨⟨text, aspan⟩, #[], aspan⟩
              | none => pure ⟨⟨"unknown", aspan⟩, #[], aspan⟩

          let nameNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .name
          let opNameNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .operatorName
          let name ← if !nameNodes.isEmpty then
            let (n, no) := nameNodes[0]!
            match firstGreenChild n with
            | some child =>
                let text ← getGreenTokenText child no
                let nspan ← spanFor n no
                pure ⟨text, nspan⟩
            | none =>
                lowerError "definition missing name" span
                pure ⟨"_error", span⟩
          else if !opNameNodes.isEmpty then
            let (opNode, oo) := opNameNodes[0]!
            let opTokens := opNode.children.filter fun c => isTokenKind c .varSymbol
            if opTokens.isEmpty then
              lowerError "operator name missing operator" span
              pure ⟨"_error", span⟩
            else
              match getTokenText opTokens[0]! with
              | some text =>
                  let ospan ← spanFor opNode oo
                  pure ⟨text, ospan⟩
              | none => pure ⟨"_error", span⟩
          else
            lowerError "definition missing name" span
            pure ⟨"_error", span⟩

          -- Extract the return type signature (e.g., `-> Int` gives us `Int`)
          let sigNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .signature
          let returnTypeSig ← if sigNodes.isEmpty then pure none
            else some <$> lowerTypeExpr sigNodes[0]!.1 sigNodes[0]!.2

          -- Extract parameter list to get parameter types for building full function signature
          let paramListNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .paramList

          -- Extract parameter types from .field nodes in paramList
          let paramTypes ← if paramListNodes.isEmpty then pure #[]
            else
              let (plist, plistOffset) := paramListNodes[0]!
              let fieldNodes := childrenWithOffsets plist plistOffset |>.filter fun (c, _) =>
                c.syntaxKind? == some .field
              fieldNodes.filterMapM fun (f, fo) => do
                let typeNodes := childrenWithOffsets f fo |>.filter fun (c, _) => isSemanticNode c
                if typeNodes.isEmpty then pure none
                else some <$> lowerTypeExpr typeNodes[0]!.1 typeNodes[0]!.2

          -- Build the full function signature: paramType1 -> paramType2 -> ... -> returnType
          -- If we have both parameter types and a return type, construct the full arrow type
          let sig ← match returnTypeSig with
            | none => pure none
            | some retTy =>
              if paramTypes.isEmpty then
                pure (some retTy)
              else
                -- Build: paramTypes[0] -> paramTypes[1] -> ... -> retTy
                let fullSig := paramTypes.foldr (init := retTy) fun paramTy accTy =>
                  TypeExpr.arrow paramTy accTy span
                pure (some fullSig)

          let clauseNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .defClause
          let clauses ← clauseNodes.mapM fun (c, o) => lowerDefClause c o

          if clauses.isEmpty then
            let paramPatterns ← if paramListNodes.isEmpty then pure #[]
              else
                let (plist, plistOffset) := paramListNodes[0]!
                let varNodes := childrenWithOffsets plist plistOffset |>.filter fun (c, _) =>
                  c.syntaxKind? == some .patVar || c.syntaxKind? == some .field
                varNodes.mapM fun (v, vo) => do
                  let vspan ← spanFor v vo
                  match v.syntaxKind? with
                  | some .patVar =>
                      match firstGreenChild v with
                      | some child =>
                          let text ← getGreenTokenText child vo
                          pure (Pattern.var ⟨text, vspan⟩)
                      | none =>
                          lowerError "patVar missing name" vspan
                          pure (Pattern.var ⟨"_error", vspan⟩)
                  | some .field =>
                      let tokenKids := v.children.filter fun c => isTokenKind c .lowerIdent
                      if tokenKids.isEmpty then
                        lowerError "field missing name" vspan
                        pure (Pattern.var ⟨"_error", vspan⟩)
                      else
                        match getTokenText tokenKids[0]! with
                        | some text => pure (Pattern.var ⟨text, vspan⟩)
                        | none => pure (Pattern.var ⟨"_error", vspan⟩)
                  | _ =>
                      lowerError "unexpected node in param list" vspan
                      pure (Pattern.var ⟨"_error", vspan⟩)

            let bodyNodes := allKids.filter fun (c, _) =>
              c.syntaxKind? != some .name && c.syntaxKind? != some .operatorName &&
              c.syntaxKind? != some .signature && c.syntaxKind? != some .attribute &&
              c.syntaxKind? != some .paramList && isSemanticNode c
            if bodyNodes.isEmpty then
              pure (.def_ attrs name sig #[] span)
            else
              let body ← lowerExpr bodyNodes[0]!.1 bodyNodes[0]!.2
              let clause : DefClause := ⟨paramPatterns, none, body, body.span⟩
              pure (.def_ attrs name sig #[clause] span)
          else
            pure (.def_ attrs name sig clauses span)

      | .declData =>
          let nameNodes := green.children.filter fun c =>
            isTokenKind c .upperIdent || c.syntaxKind? == some .typeCon
          let name ← if nameNodes.isEmpty then
            lowerError "data type missing name" span
            pure ⟨"_Error", span⟩
          else
            -- Use getTokenText to handle both raw tokens and triviaToken wrappers
            match getTokenText nameNodes[0]! with
            | some text => pure ⟨text, span⟩
            | none =>
                match firstGreenChild nameNodes[0]! with
                | some child =>
                    let text ← getGreenTokenText child offset
                    pure ⟨text, span⟩
                | none =>
                    lowerError "data type missing name" span
                    pure ⟨"_Error", span⟩

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
                    pure ⟨text, vspan⟩
                | none =>
                    let vspan ← spanFor v vo
                    pure ⟨"_", vspan⟩

          let conNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .constructor
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

          pure (.data name params cons kindAnnot span)

      | .declStruct =>
          let nameNodes := green.children.filter fun c => isTokenKind c .upperIdent
          if nameNodes.size < 2 then
            lowerError "struct missing name or constructor" span
            pure (.struct ⟨"_Error", span⟩ #[] ⟨"_Con", span⟩ #[] span)
          else
            let name ← match getTokenText nameNodes[0]! with
            | some text => pure text
            | none => pure "_Error"
            let conName ← match getTokenText nameNodes[1]! with
            | some text => pure text
            | none => pure "_Con"

            let allKids := childrenWithOffsets green offset
            let fieldNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .field
            let fields ← fieldNodes.mapM fun (c, o) => lowerStructField c o

            pure (.struct ⟨name, span⟩ #[] ⟨conName, span⟩ fields span)

      | .declTrait =>
          let nameNodes := green.children.filter fun c => isTokenKind c .upperIdent
          let name ← if nameNodes.isEmpty then
            pure ⟨"_Error", span⟩
          else
            match getTokenText nameNodes[0]! with
            | some text => pure ⟨text, span⟩
            | none => pure ⟨"_Error", span⟩

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
                    pure ⟨text, vspan⟩
                | none =>
                    let vspan ← spanFor v vo
                    pure ⟨"_", vspan⟩

          let constraintNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .constraintList
          let constraints ← constraintNodes.mapM fun (c, o) => lowerConstraint c o

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
                    pure ⟨text, nspan⟩
                | none => pure ⟨"_", mspan⟩
              else if !opNameN.isEmpty then
                let (opNode, oo) := opNameN[0]!
                let opTokens := opNode.children.filter fun c => isTokenKind c .varSymbol
                if opTokens.isEmpty then pure ⟨"_", mspan⟩
                else
                  match getTokenText opTokens[0]! with
                  | some text =>
                      let ospan ← spanFor opNode oo
                      pure ⟨text, ospan⟩
                  | none => pure ⟨"_", mspan⟩
              else pure ⟨"_", mspan⟩
            let mtype ← if sigN.isEmpty then pure (.var ⟨"_", mspan⟩)
              else lowerTypeExpr sigN[0]!.1 sigN[0]!.2
            pure ⟨mname, mtype, mspan⟩

          pure (.trait name params constraints methods span)

      | .declInstance =>
          let allKids := childrenWithOffsets green offset
          let constraintNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .constraint
          let (traitName, args) ← if constraintNodes.isEmpty then
            pure (⟨"_Error", span⟩, #[])
          else
            let c ← lowerConstraint constraintNodes[0]!.1 constraintNodes[0]!.2
            pure (c.className, c.args)

          let superNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .constraintList
          let constraints ← superNodes.mapM fun (c, o) => lowerConstraint c o

          let methodNodes := allKids.filter fun (c, _) => c.syntaxKind? == some .declDef
          let methods ← methodNodes.mapM fun (c, o) => lowerDecl c o

          pure (.instance_ traitName args constraints methods span)

      | .declUse =>
          let allKids := childrenWithOffsets green offset
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
                    pure ⟨text, nspan⟩
                | none =>
                    let nspan ← spanFor n no
                    pure ⟨"_", nspan⟩

          pure (.use path items span)

      | .declExport =>
          let allKids := childrenWithOffsets green offset
          let itemNodes := allKids.filter fun (c, _) =>
            c.syntaxKind? == some .importItems || c.syntaxKind? == some .exportItems

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
                    pure ⟨text, nspan⟩
                | none =>
                    let nspan ← spanFor n no
                    pure ⟨"_", nspan⟩

          pure (.export_ items span)

      | .declIntrinsic =>
          let allKids := childrenWithOffsets green offset |>.filter fun (c, _) => isSemanticNode c
          if allKids.isEmpty then
            lowerError "intrinsic missing declaration" span
            pure (.intrinsic (.export_ #[] span) span)
          else
            let inner ← lowerDecl allKids[0]!.1 allKids[0]!.2
            pure (.intrinsic inner span)

      | _ =>
          lowerError s!"unexpected declaration kind: {kind}" span
          pure (.export_ #[] span)

  | .error message _ _ =>
      lowerError message span
      pure (.export_ #[] span)

  | .missing expected =>
      lowerError s!"missing {expected}" span
      pure (.export_ #[] span)

  | .token kind _ =>
      lowerError s!"unexpected token at declaration level: {kind}" span
      pure (.export_ #[] span)

/-- Lower a module from a green tree -/
def lowerModule (green : GreenNode) (offset : Nat) (moduleName : String) : LowerM Module := do
  let span ← spanFor green offset

  match green with
  | .node .sourceFile children _ =>
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
theorem lower_trivia_invariant (green : GreenNode) (source : SourceFile) (moduleName : String) :
    (lowerGreen (green.stripTrivia) source moduleName).1 =
    (lowerGreen green source moduleName).1 := by
  sorry

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
    | none => Span.uninhabited
  return { name := moduleName, decls := decls, span := span }

end Soma.Syntax
