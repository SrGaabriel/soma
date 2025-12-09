/-
  This module implements the core parser infrastructure. The key design:
  - **Infallible**: Parsing NEVER fails. It always produces a SyntaxNode.
  - **Error Recovery**: Errors become .error or .missing nodes in the CST.
  - **Diagnostic Accumulation**: Errors are collected, not thrown.

  The parser follows the same pattern as the Lexer - using StateT with
  a diagnostic accumulator.
-/

import Soma.Syntax.Source
import Soma.Syntax.Token
import Soma.Syntax.Diagnostic
import Soma.Syntax.SyntaxKind
import Soma.Syntax.SyntaxNode

namespace Soma.Syntax

/-- Parser state -/
structure ParserState where
  /-- Array of tokens from the lexer -/
  tokens : Array Token
  /-- Current position in the token array -/
  pos : Nat
  /-- Source file for creating spans -/
  source : SourceFile
  deriving Inhabited

namespace ParserState

/-- Create initial parser state -/
def init (tokens : Array Token) (source : SourceFile) : ParserState :=
  { tokens, pos := 0, source }

/-- Check if we're at end of tokens -/
def atEnd (s : ParserState) : Bool :=
  s.pos ≥ s.tokens.size

/-- Get current token (or a synthetic EOF) -/
def current (s : ParserState) : Token :=
  if h : s.pos < s.tokens.size then
    s.tokens[s.pos]
  else
    -- Synthetic EOF token
    let loc : SourceLoc := {
      file := s.source.id
      byteOffset := s.source.content.utf8ByteSize
      line := s.source.lineStarts.size
      column := 1
    }
    { kind := .eof, span := Span.point loc, text := "" }

/-- Peek at the next token -/
def peek (s : ParserState) : Token :=
  if h : s.pos + 1 < s.tokens.size then
    s.tokens[s.pos + 1]
  else
    s.current  -- Will be EOF if at end

/-- Peek n tokens ahead -/
def peekN (s : ParserState) (n : Nat) : Token :=
  if h : s.pos + n < s.tokens.size then
    s.tokens[s.pos + n]
  else
    s.current

/-- Advance to the next token -/
def advance (s : ParserState) : ParserState :=
  if s.atEnd then s
  else { s with pos := s.pos + 1 }

/-- Get current source location -/
def currentLoc (s : ParserState) : SourceLoc :=
  s.current.span.start

end ParserState

/-- Parser context for error messages -/
structure ParserContext where
  /-- Stack of contexts (e.g., "in function body", "in let binding") -/
  stack : Array String := #[]

namespace ParserContext

/-- Push a new context -/
def push (ctx : ParserContext) (label : String) : ParserContext :=
  { ctx with stack := ctx.stack.push label }

/-- Get a description of the current context -/
def describe (ctx : ParserContext) : String :=
  if ctx.stack.isEmpty then ""
  else String.intercalate ", " ctx.stack.toList

end ParserContext

abbrev ParserM := ReaderT ParserContext (StateT ParserState (StateT Diagnostics Id))

namespace ParserM

/-- Run the parser -/
def run' (p : ParserM α) (tokens : Array Token) (source : SourceFile) : α × Diagnostics :=
  let initState := ParserState.init tokens source
  let initCtx : ParserContext := {}
  let ((result, _), diagnostics) := ((p.run initCtx).run initState).run #[]
  (result, diagnostics)

end ParserM

-- Open ParserM namespace for the combinators so they don't conflict with Lexer
namespace ParserM

/-- Record a diagnostic -/
def recordDiagnostic (d : Diagnostic) : ParserM Unit := do
  -- ParserM = ReaderT ParserContext (StateT ParserState (StateT Diagnostics Id))
  -- Use do-notation to work within ReaderT, then lift through inner StateT
  (StateT.lift (modify (·.push d)) : StateT ParserState (StateT Diagnostics Id) Unit)

/-- Record an error at the current position -/
def recordError (msg : String) : ParserM Unit := do
  let s ← get
  let span := s.current.span
  recordDiagnostic (Diagnostic.error msg span)

/-- Record an error with a specific span -/
def recordErrorAt (msg : String) (span : Span) : ParserM Unit := do
  recordDiagnostic (Diagnostic.error msg span)

/-- Record a rich diagnostic with optional secondary labels, notes, and help -/
def recordRichError (msg : String) (span : Span)
    (secondary : Array (Span × String) := #[])
    (notes : Array String := #[])
    (help : Option String := none) : ParserM Unit := do
  let mut diag := Diagnostic.error msg span
  for (s, m) in secondary do
    diag := diag.withSecondary s m
  for n in notes do
    diag := diag.withNote n
  if let some h := help then
    diag := diag.withHelp h
  recordDiagnostic diag

/-- Check if at end of input -/
def atEnd : ParserM Bool := do
  let s ← get
  return s.atEnd

/-- Get current token -/
def current : ParserM Token := do
  let s ← get
  return s.current

/-- Peek at the next token -/
def peekNext : ParserM Token := do
  let s ← get
  return s.peek

/-- Peek n tokens ahead -/
def peekAhead (n : Nat) : ParserM Token := do
  let s ← get
  return s.peekN n

/-- Advance to the next token -/
def advance : ParserM Unit :=
  modify ParserState.advance

/-- Get current location -/
def currentLoc : ParserM SourceLoc := do
  let s ← get
  return s.currentLoc

/-- Get the source file -/
def getSource : ParserM SourceFile := do
  let s ← get
  return s.source

/-- Run parser with additional context label -/
def labelled (label : String) (p : ParserM α) : ParserM α :=
  withReader (·.push label) p

/-- Check if current token has the given kind -/
def check (kind : TokenKind) : ParserM Bool := do
  let tok ← current
  return tok.kind == kind

/-- Check if current token is one of the given kinds -/
def checkAny (kinds : Array TokenKind) : ParserM Bool := do
  let tok ← current
  return kinds.any (· == tok.kind)

/-- Consume the current token if it matches, return none otherwise -/
def tryConsume (kind : TokenKind) : ParserM (Option Token) := do
  let tok ← current
  if tok.kind == kind then
    advance
    return some tok
  else
    return none

/-- Consume the current token unconditionally -/
def consumeAny : ParserM Token := do
  let tok ← current
  advance
  return tok

/-- Expect a token, producing a .missing node if not found -/
def expect (kind : TokenKind) (forKind : SyntaxKind) : ParserM SyntaxNode := do
  match ← tryConsume kind with
  | some tok => return mkToken tok
  | none =>
      let loc ← currentLoc
      recordError s!"expected {kind.describe}"
      return mkMissing forKind loc

/-- Expect a token, returning it as a Token (not wrapped) -/
def expectToken (kind : TokenKind) : ParserM (Option Token) := do
  match ← tryConsume kind with
  | some tok => return some tok
  | none =>
      let tok ← current
      recordError s!"expected {kind.describe}, found {tok.kind.describe}"
      return none

/-- Skip layout separator tokens -/
def skipLayoutSep : ParserM Unit := do
  while (← check .layoutSep) do
    advance

/-- Skip all layout tokens (start, sep, end) -/
def skipLayout : ParserM Unit := do
  while (← checkAny #[.layoutStart, .layoutSep, .layoutEnd]) do
    advance

/-- Consume layout start if present -/
def tryLayoutStart : ParserM Bool := do
  if (← check .layoutStart) then
    advance
    return true
  else
    return false

/-- Consume layout end if present -/
def tryLayoutEnd : ParserM Bool := do
  if (← check .layoutEnd) then
    advance
    return true
  else
    return false

/-- Parse within a layout block -/
def inLayout (p : ParserM α) : ParserM α := do
  let _ ← tryLayoutStart
  let result ← p
  let _ ← tryLayoutEnd
  return result

/-- Parse a lower-case identifier -/
def parseLowerIdent : ParserM (Option Token) := do
  let tok ← current
  if tok.kind == .lowerIdent then
    advance
    return some tok
  else
    return none

/-- Parse an upper-case identifier -/
def parseUpperIdent : ParserM (Option Token) := do
  let tok ← current
  if tok.kind == .upperIdent then
    advance
    return some tok
  else
    return none

/-- Parse any identifier (lower or upper) -/
def parseIdent : ParserM (Option Token) := do
  let tok ← current
  if tok.kind == .lowerIdent || tok.kind == .upperIdent then
    advance
    return some tok
  else
    return none

/-- Parse an operator symbol -/
def parseOperator : ParserM (Option Token) := do
  let tok ← current
  if tok.kind == .varSymbol then
    advance
    return some tok
  else
    return none

/-- Parse an operator name in braces: {+}, {>>=} -/
def parseOperatorName : ParserM (Option SyntaxNode) := do
  if !(← check .leftBrace) then return none
  let startTok ← consumeAny  -- consume {
  match ← parseOperator with
  | some opTok =>
      match ← tryConsume .rightBrace with
      | some endTok =>
          let span := Span.merge startTok.span endTok.span
          return some (mkNodeSpan .operatorName #[mkToken startTok, mkToken opTok, mkToken endTok] span)
      | none =>
          recordError "expected '}' after operator"
          let span := Span.merge startTok.span opTok.span
          return some (mkError span "unclosed operator name" #[mkToken startTok, mkToken opTok])
  | none =>
      recordError "expected operator inside braces"
      return some (mkError startTok.span "expected operator" #[mkToken startTok])

/-- Tokens that typically start a new declaration or statement -/
def syncTokens : Array TokenKind :=
  #[.kw_def, .kw_data, .kw_struct, .kw_trait, .kw_instance, .kw_use, .kw_export,
    .kw_intrinsic, .layoutEnd, .eof]

/-- Check if current token is a sync point -/
def atSyncPoint : ParserM Bool := do
  let tok ← current
  return syncTokens.any (· == tok.kind) || tok.kind == .layoutSep

/-- Skip tokens until we reach a sync point -/
def skipToSync : ParserM (Array SyntaxNode) := do
  let mut skipped : Array SyntaxNode := #[]
  while !(← atEnd) && !(← atSyncPoint) do
    let tok ← consumeAny
    skipped := skipped.push (mkToken tok)
  return skipped

/-- Try to parse, recovering with error node on failure -/
def recover (p : ParserM SyntaxNode) (_expected : String) : ParserM SyntaxNode := do
  let result ← p
  return result

/-- Parse zero or more of something, separated by layout separators -/
def many (p : ParserM (Option SyntaxNode)) : ParserM (Array SyntaxNode) := do
  let mut results : Array SyntaxNode := #[]
  repeat do
    skipLayoutSep
    match ← p with
    | some node => results := results.push node
    | none => break
  return results

/-- Parse one or more of something, separated by layout separators -/
def many1 (p : ParserM (Option SyntaxNode)) : ParserM (Option (Array SyntaxNode)) := do
  skipLayoutSep
  match ← p with
  | some first =>
      let mut results := #[first]
      repeat do
        skipLayoutSep
        match ← p with
        | some node => results := results.push node
        | none => break
      return some results
  | none => return none

/-- Parse zero or more of something, separated by a specific token -/
def sepBy (p : ParserM (Option SyntaxNode)) (sep : TokenKind) : ParserM (Array SyntaxNode) := do
  match ← p with
  | some first =>
      let mut results := #[first]
      while (← check sep) do
        advance  -- consume separator
        match ← p with
        | some node => results := results.push node
        | none => break
      return results
  | none => return #[]

/-- Parse one or more of something, separated by a specific token -/
def sepBy1 (p : ParserM (Option SyntaxNode)) (sep : TokenKind) : ParserM (Option (Array SyntaxNode)) := do
  match ← p with
  | some first =>
      let mut results := #[first]
      while (← check sep) do
        advance  -- consume separator
        match ← p with
        | some node => results := results.push node
        | none => break
      return some results
  | none => return none

/-- Parse zero or more comma-separated items -/
def commaSep (p : ParserM (Option SyntaxNode)) : ParserM (Array SyntaxNode) :=
  sepBy p .comma

/-- Parse one or more comma-separated items -/
def commaSep1 (p : ParserM (Option SyntaxNode)) : ParserM (Option (Array SyntaxNode)) :=
  sepBy1 p .comma

/-- Parse something inside parentheses -/
def parens (p : ParserM SyntaxNode) : ParserM (Option SyntaxNode) := do
  match ← tryConsume .leftParen with
  | some lparen =>
      let inner ← p
      match ← tryConsume .rightParen with
      | some rparen =>
          let span := Span.merge lparen.span rparen.span
          return some (mkNodeSpan .exprParens #[mkToken lparen, inner, mkToken rparen] span)
      | none =>
          recordError "expected ')'"
          let span := Span.merge lparen.span inner.span
          return some (mkError span "unclosed parentheses" #[mkToken lparen, inner])
  | none => return none

/-- Parse something inside brackets -/
def brackets (p : ParserM SyntaxNode) : ParserM (Option SyntaxNode) := do
  match ← tryConsume .leftBracket with
  | some lbracket =>
      let inner ← p
      match ← tryConsume .rightBracket with
      | some rbracket =>
          let span := Span.merge lbracket.span rbracket.span
          return some (mkNodeSpan .exprList #[mkToken lbracket, inner, mkToken rbracket] span)
      | none =>
          recordError "expected ']'"
          let span := Span.merge lbracket.span inner.span
          return some (mkError span "unclosed brackets" #[mkToken lbracket, inner])
  | none => return none

/-- Parse something inside braces -/
def braces (p : ParserM SyntaxNode) : ParserM (Option SyntaxNode) := do
  match ← tryConsume .leftBrace with
  | some lbrace =>
      let inner ← p
      match ← tryConsume .rightBrace with
      | some rbrace =>
          let span := Span.merge lbrace.span rbrace.span
          return some (mkNodeSpan .exprRecord #[mkToken lbrace, inner, mkToken rbrace] span)
      | none =>
          recordError "expected '}'"
          let span := Span.merge lbrace.span inner.span
          return some (mkError span "unclosed braces" #[mkToken lbrace, inner])
  | none => return none

/-- Try to parse, returning none on failure without consuming input -/
def optional (p : ParserM (Option α)) : ParserM (Option α) := p

/-- Parse one of several alternatives -/
def choice (parsers : Array (ParserM (Option SyntaxNode))) : ParserM (Option SyntaxNode) := do
  for p in parsers do
    match ← p with
    | some node => return some node
    | none => continue
  return none

/-- Get the start location, run parser, compute span to current position -/
def withSpan (p : ParserM α) : ParserM (α × Span) := do
  let startLoc ← currentLoc
  let result ← p
  let endLoc ← currentLoc
  let span := { start := startLoc, stop := endLoc }
  return (result, span)

/-- Build a node with correct span tracking -/
def buildNode (kind : SyntaxKind) (p : ParserM (Array SyntaxNode)) : ParserM SyntaxNode := do
  let startLoc ← currentLoc
  let children ← p
  if children.isEmpty then
    return mkNodeSpan kind #[] (Span.point startLoc)
  else
    let span := Span.merge (children[0]!.span) (children[children.size - 1]!.span)
    return mkNodeSpan kind children span

end ParserM

end Soma.Syntax
