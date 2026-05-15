import Soma.Syntax.Source
import Soma.Syntax.GreenTree
import Soma.Syntax.RedTree
import Soma.Diagnostic
import Soma.Syntax.Lexer

namespace Soma.Syntax

open Soma (Diagnostics DiagBuilder Phase severity)
open Psychopomp (Diagnostic)

/-- A positioned token from the lexer, with leading trivia pre-attached -/
structure PosToken where
  /-- Leading trivia (whitespace/comments) before this token -/
  leadingTrivia : Array GreenNode
  /-- The actual token -/
  green : GreenNode
  /-- Byte offset of the first trivia token (or the token itself if no trivia) -/
  offset : Nat
  deriving Repr, Inhabited

namespace PosToken

def kind (t : PosToken) : Option TokenKind := t.green.tokenKind?
def text (t : PosToken) : String := t.green.text?.getD ""

/-- Total width including leading trivia -/
def totalWidth (t : PosToken) : Nat :=
  t.leadingTrivia.foldl (fun acc g => acc + g.width) 0 + t.green.width

/-- Offset where the actual token starts (after trivia) -/
def tokenOffset (t : PosToken) : Nat :=
  t.offset + t.leadingTrivia.foldl (fun acc g => acc + g.width) 0

/-- End offset (after the token) -/
def endOffset (t : PosToken) : Nat := t.offset + t.totalWidth

/-- Create a span from this token given a source file (spans the token, not trivia) -/
def span (t : PosToken) (source : SourceFile) : Span :=
  Span.fromOffsets source t.tokenOffset t.endOffset

/-- Build a green node that includes leading trivia wrapped in a triviaToken node -/
def toGreen (t : PosToken) : GreenNode :=
  if t.leadingTrivia.isEmpty then t.green
  else GreenNode.mkNode .triviaToken (t.leadingTrivia.push t.green)

end PosToken

/-- Parser state -/
structure ParserState where
  /-- Array of positioned tokens from lexer (trivia already attached) -/
  tokens : Array PosToken
  /-- Current position in token array -/
  pos : Nat
  /-- Source file for error spans -/
  source : SourceFile
  diag : DiagBuilder
  deriving Inhabited

namespace ParserState

def init (tokens : Array PosToken) (source : SourceFile) (diag : DiagBuilder)
    : ParserState :=
  { tokens, pos := 0, source, diag }

def atEnd (s : ParserState) : Bool := s.pos ≥ s.tokens.size

/-- Get the token at position -/
def tokenAt (s : ParserState) (idx : Nat) : PosToken :=
  if h : idx < s.tokens.size then s.tokens[idx]
  else { leadingTrivia := #[], green := .token .eof "", offset := s.source.content.utf8ByteSize }

def current (s : ParserState) : PosToken := s.tokenAt s.pos

def peek (s : ParserState) : PosToken := s.tokenAt (s.pos + 1)

def peekN (s : ParserState) (n : Nat) : PosToken := s.tokenAt (s.pos + n)

def advance (s : ParserState) : ParserState :=
  if s.atEnd then s
  else { s with pos := s.pos + 1 }

end ParserState

/-- Parser context for error messages -/
structure ParserContext where
  stack : Array String := #[]

namespace ParserContext
end ParserContext

abbrev ParserM := ReaderT ParserContext (StateT ParserState (StateT Diagnostics Id))

namespace ParserM

def run' (p : ParserM α) (tokens : Array PosToken) (source : SourceFile)
    (diag : DiagBuilder) : α × Diagnostics :=
  let initState := ParserState.init tokens source diag
  let initCtx : ParserContext := {}
  let ((result, _), diagnostics) := ((p.run initCtx).run initState).run #[]
  (result, diagnostics)

def recordDiagnostic (d : Diagnostic) : ParserM Unit :=
  (StateT.lift (modify (·.push d)) : StateT ParserState (StateT Diagnostics Id) Unit)

/-- Assemble a parser-phase diagnostic -/
private def buildDiag (s : ParserState) (msg : String) (span : Span)
    (secondary : Array (Span × String) := #[]) (notes : Array String := #[])
    (help : Option String := none) : Diagnostic :=
  { severity := severity .parse
    message := msg
    primary := s.diag.primary span msg
    secondary := (secondary.map fun (sec, m) => s.diag.support sec m).toList
    notes := notes.toList
    helps := match help with | some h => [h] | none => [] }

def recordError (msg : String) : ParserM Unit := do
  let s ← get
  let span := s.current.span s.source
  recordDiagnostic (buildDiag s msg span)

def atEnd : ParserM Bool := do return (← get).atEnd
def current : ParserM PosToken := do return (← get).current
def peekNext : ParserM PosToken := do return (← get).peek
def peekAhead (n : Nat) : ParserM PosToken := do return (← get).peekN n
def advance : ParserM Unit := modify ParserState.advance

/-- Describe what the parser is currently looking at -/
def describeCurrent : ParserM String := do
  let tok ← current
  return match tok.kind with
    | some k => TokenKind.describe k
    | none => "non-token"

/-- Record an `expected X, got Y` error at the current token -/
def recordExpected (expected : String) : ParserM Unit := do
  let got ← describeCurrent
  recordError s!"expected {expected}, got {got}"

def check (kind : TokenKind) : ParserM Bool := do
  return (← current).kind == some kind

def checkAny (kinds : Array TokenKind) : ParserM Bool := do
  let k := (← current).kind
  return kinds.any (some · == k)

/-- Try to consume a token of the given kind -/
def tryConsume (kind : TokenKind) : ParserM (Option GreenNode) := do
  let tok ← current
  if tok.kind == some kind then
    advance
    return some tok.toGreen
  else
    return none

/-- Consume current token along with its pre-attached leading trivia -/
def consumeAny : ParserM GreenNode := do
  let tok ← current
  advance
  return tok.toGreen

/-- Expect a token of the given kind, with trivia automatically included -/
def expect (kind : TokenKind) (forKind : SyntaxKind) : ParserM GreenNode := do
  match ← tryConsume kind with
  | some g => return g
  | none =>
      recordExpected kind.describe
      return .missing forKind

/-- Check if a token kind is a layout token -/
def isLayoutToken (kind : Option TokenKind) : Bool :=
  kind == some .layoutStart || kind == some .layoutSep || kind == some .layoutEnd

/-- Peek ahead to find the next non-layout token's kind -/
def peekNextRelevant : ParserM (Option TokenKind) := do
  let s ← get
  let mut i := s.pos
  while h : i < s.tokens.size do
    let tok := s.tokens[i]
    if !isLayoutToken tok.kind then
      return tok.kind
    i := i + 1
  return some .eof

/-- Check if the next relevant (non-layout) token is of the given kind -/
def checkNextRelevant (kind : TokenKind) : ParserM Bool := do
  return (← peekNextRelevant) == some kind

/-- Consume layoutStart if present -/
def tryLayoutStart : ParserM Bool := do
  if (← check .layoutStart) then advance; return true
  else return false

/-- Consume layoutEnd if present -/
def tryLayoutEnd : ParserM Bool := do
  if (← check .layoutEnd) then advance; return true
  else return false

/-- Consume layoutSep if present -/
def tryLayoutSep : ParserM Bool := do
  if (← check .layoutSep) then advance; return true
  else return false

/-- Run parser inside an optional layout block -/
def inLayout (p : ParserM α) : ParserM α := do
  let _ ← tryLayoutStart
  let result ← p
  let _ ← tryLayoutEnd
  return result

/-- Parse zero or more items separated by layoutSep, inside an optional layout block -/
def layoutSepBy (p : ParserM (Option GreenNode)) : ParserM (Array GreenNode) := do
  let _ ← tryLayoutStart
  let mut results : Array GreenNode := #[]
  -- Parse first item
  match ← p with
  | some node => results := results.push node
  | none =>
      let _ ← tryLayoutEnd
      return results
  -- Parse remaining items, each preceded by layoutSep
  while (← check .layoutSep) do
    advance
    match ← p with
    | some node => results := results.push node
    | none => break
  let _ ← tryLayoutEnd
  return results

/-- Parse a lower-case identifier -/
def parseLowerIdent : ParserM (Option GreenNode) := do
  let tok ← current
  if tok.kind == some .lowerIdent then
    advance
    return some tok.toGreen
  else
    return none

/-- Parse an upper-case identifier -/
def parseUpperIdent : ParserM (Option GreenNode) := do
  let tok ← current
  if tok.kind == some .upperIdent then
    advance
    return some tok.toGreen
  else
    return none

/-- Parse any identifier -/
def parseIdent : ParserM (Option GreenNode) := do
  let tok ← current
  if tok.kind == some .lowerIdent || tok.kind == some .upperIdent then
    advance
    return some tok.toGreen
  else
    return none

/-- Parse an operator symbol -/
def parseOperator : ParserM (Option GreenNode) := do
  let tok ← current
  if tok.kind == some .varSymbol then
    advance
    return some tok.toGreen
  else
    return none

/-- Parse an operator name in braces, returning a single node wrapping all -/
def parseOperatorName : ParserM (Option GreenNode) := do
  if !(← check .leftBrace) then return none
  let lbrace ← consumeAny
  match ← parseOperator with
  | some op =>
      match ← tryConsume .rightBrace with
      | some rbrace =>
          return some (GreenNode.mkNode .operatorName #[lbrace, op, rbrace])
      | none =>
          recordExpected "'}' after operator"
          return some (GreenNode.mkError "unclosed operator name" #[lbrace, op])
  | none =>
      recordExpected "operator inside braces"
      return some (GreenNode.mkError "expected operator" #[lbrace])

def syncTokens : Array TokenKind :=
  #[.kw_def, .kw_theorem, .kw_inductive, .kw_struct, .kw_trait, .kw_instance, .kw_use, .kw_pub,
    .layoutEnd, .eof]

def atSyncPoint : ParserM Bool := do
  let k := (← current).kind
  return syncTokens.any (some · == k) || k == some .layoutSep

def skipToSync : ParserM (Array GreenNode) := do
  let mut skipped : Array GreenNode := #[]
  while !(← atEnd) && !(← atSyncPoint) do
    skipped := skipped.push (← consumeAny)
  return skipped

/-- Parse zero or more items -/
def many (p : ParserM (Option GreenNode)) : ParserM (Array GreenNode) := do
  let mut results : Array GreenNode := #[]
  repeat do
    match ← p with
    | some node => results := results.push node
    | none => break
  return results

def sepBy (p : ParserM (Option GreenNode)) (sep : TokenKind) : ParserM (Array GreenNode) := do
  match ← p with
  | some first =>
      let mut results := #[first]
      while (← check sep) do
        let sepNode ← consumeAny
        results := results.push sepNode
        match ← p with
        | some node => results := results.push node
        | none => break
      return results
  | none => return #[]

def sepBy1 (p : ParserM (Option GreenNode)) (sep : TokenKind) : ParserM (Option (Array GreenNode)) := do
  match ← p with
  | some first =>
      let mut results := #[first]
      while (← check sep) do
        let sepNode ← consumeAny
        results := results.push sepNode
        match ← p with
        | some node => results := results.push node
        | none => break
      return some results
  | none => return none

def commaSep (p : ParserM (Option GreenNode)) : ParserM (Array GreenNode) := sepBy p .comma
def commaSep1 (p : ParserM (Option GreenNode)) : ParserM (Option (Array GreenNode)) := sepBy1 p .comma

/-- Parse a delimited, separated list with optional layout support -/
def delimitedSepBy (openTok closeTok : TokenKind) (sep : TokenKind)
    (p : ParserM (Option GreenNode)) (forKind : SyntaxKind)
    : ParserM (GreenNode × Array GreenNode × GreenNode) := do
  let openNode ← expect openTok forKind
  let _ ← tryLayoutStart
  let mut items : Array GreenNode := #[]
  -- Parse first item if present
  match ← p with
  | some first =>
      items := items.push first
      -- Parse remaining items, each preceded by separator (and optional layoutSep after)
      while (← check sep) do
        let sepNode ← consumeAny -- consume separator
        items := items.push sepNode
        let _ ← tryLayoutSep  -- consume layoutSep if present (for newline after comma)
        match ← p with
        | some item => items := items.push item
        | none => break
  | none => pure ()
  let _ ← tryLayoutEnd
  let closeNode ← expect closeTok forKind
  return (openNode, items, closeNode)

end ParserM

/-- Check if a token kind is trivia (whitespace or comment) -/
def isTrivia (kind : Option TokenKind) : Bool :=
  kind == some .whitespace || kind == some .comment

/-- Check if a token is a layout token that shouldn't consume trivia -/
def isLayoutToken (g : GreenNode) : Bool :=
  g.tokenKind? == some .layoutStart ||
  g.tokenKind? == some .layoutEnd ||
  g.tokenKind? == some .layoutSep

/-- Convert lexer output to positioned tokens, attaching leading trivia to each non-trivia token -/
def toPosTokens (greenTokens : Array GreenNode) : Array PosToken := Id.run do
  let mut result : Array PosToken := #[]
  let mut pendingTrivia : Array GreenNode := #[]
  let mut triviaOffset := 0  -- Offset where pending trivia started
  let mut offset := 0

  for g in greenTokens do
    if isTrivia g.tokenKind? then
      -- Accumulate trivia; record start offset if this is the first trivia token
      if pendingTrivia.isEmpty then
        triviaOffset := offset
      pendingTrivia := pendingTrivia.push g
    else if isLayoutToken g then
      -- Layout tokens should not consume trivia
      result := result.push {
        leadingTrivia := #[]
        green := g
        offset := offset
      }
    else
      -- Non-trivia token: attach any pending trivia to it
      let tokenOffset := if pendingTrivia.isEmpty then offset else triviaOffset
      result := result.push {
        leadingTrivia := pendingTrivia
        green := g
        offset := tokenOffset
      }
      pendingTrivia := #[]
    offset := offset + g.width

  -- This ensures the token array is never empty and parsing always terminates
  let eofOffset := if pendingTrivia.isEmpty then offset else triviaOffset
  result := result.push {
    leadingTrivia := pendingTrivia
    green := .token .eof ""
    offset := eofOffset
  }

  return result

/-- Parse source code into a green tree using a given parser -/
def parseGreenWith (parser : ParserM GreenNode) (tokens : Array GreenNode)
    (source : SourceFile) (diag : DiagBuilder) : GreenNode × Diagnostics :=
  let posTokens := toPosTokens tokens
  ParserM.run' parser posTokens source diag

/-- Full parsing pipeline: lex + parse using a given parser -/
def parseWith (parser : ParserM GreenNode) (source : SourceFile) (diag : DiagBuilder)
    : GreenNode × Diagnostics :=
  let (tokens, lexDiags) := lexCode source diag
  let (green, parseDiags) := parseGreenWith parser tokens source diag
  (green, lexDiags ++ parseDiags)

/-- Parse and wrap in a red tree with stable NodeIds using a given parser -/
def parseToTreeWith (parser : ParserM GreenNode) (source : SourceFile)
    (diag : DiagBuilder) : ParsedTree × Diagnostics :=
  let (green, diags) := parseWith parser source diag
  (ParsedTree.fromGreen green source, diags)

end Soma.Syntax
