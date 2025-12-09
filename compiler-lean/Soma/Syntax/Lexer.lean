import Soma.Syntax.Source
import Soma.Syntax.Token
import Soma.Syntax.Diagnostic

namespace Soma.Syntax

/-! ## Character Classification -/

/-- Check if a character is a space (not newline) -/
def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t'

/-- Check if a character is a digit -/
def isDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Check if a character is a letter -/
def isLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- Check if a character is an emoji (Unicode "Other Symbol" category) -/
def isEmoji (c : Char) : Bool :=
  -- Approximate check for common emoji ranges
  let n := c.toNat
  (0x1F300 ≤ n && n ≤ 0x1F9FF) ||  -- Miscellaneous Symbols and Pictographs, Emoticons, etc.
  (0x2600 ≤ n && n ≤ 0x26FF) ||    -- Miscellaneous Symbols
  (0x2700 ≤ n && n ≤ 0x27BF)       -- Dingbats

/-- Check if a character can start an identifier -/
def isIdentStart (c : Char) : Bool :=
  isLetter c || c == '_' || isEmoji c

/-- Check if a character can continue an identifier -/
def isIdentContinue (c : Char) : Bool :=
  isIdentStart c || isDigit c

/-- Check if a character is an operator character -/
def isOperatorChar (c : Char) : Bool :=
  c == '!' || c == '#' || c == '$' || c == '%' || c == '&' ||
  c == '*' || c == '+' || c == '.' || c == '-' || c == '/' ||
  c == '<' || c == '=' || c == '>' || c == '?' || c == '|'

/-! ## Lexer State -/

/-- Lexer state -/
structure LexerState where
  source : SourceFile
  pos : Nat  -- byte offset
  deriving Inhabited

/-- Create initial lexer state -/
def LexerState.init (source : SourceFile) : LexerState :=
  { source, pos := 0 }

/-- Check if we're at end of input -/
def LexerState.atEnd (s : LexerState) : Bool :=
  s.pos ≥ s.source.content.utf8ByteSize

/-- Get current character (or '\x00' if at end) -/
def LexerState.current (s : LexerState) : Char :=
  if s.atEnd then '\x00' else String.Pos.Raw.get s.source.content ⟨s.pos⟩

/-- Peek at next character (or '\x00' if at end) -/
def LexerState.peek (s : LexerState) : Char :=
  let nextPos := (String.Pos.Raw.next s.source.content ⟨s.pos⟩).byteIdx
  if nextPos ≥ s.source.content.utf8ByteSize then '\x00'
  else String.Pos.Raw.get s.source.content ⟨nextPos⟩

/-- Peek at character n positions ahead -/
def LexerState.peekN (s : LexerState) (n : Nat) : Char :=
  let rec go (pos : Nat) (remaining : Nat) : Char :=
    if pos ≥ s.source.content.utf8ByteSize then '\x00'
    else if h : remaining == 0 then String.Pos.Raw.get s.source.content ⟨pos⟩
    else
      have : remaining - 1 < remaining := Nat.sub_lt (Nat.pos_of_ne_zero (by simp_all)) (by omega)
      go (String.Pos.Raw.next s.source.content ⟨pos⟩).byteIdx (remaining - 1)
  termination_by remaining
  go s.pos n

/-- Advance by one character -/
def LexerState.advance (s : LexerState) : LexerState :=
  if s.atEnd then s
  else { s with pos := (String.Pos.Raw.next s.source.content ⟨s.pos⟩).byteIdx }

/-- Get current byte offset -/
def LexerState.byteOffset (s : LexerState) : Nat :=
  s.pos

/-- Create a SourceLoc from current position -/
def LexerState.currentLoc (s : LexerState) : SourceLoc :=
  SourceLoc.fromOffset s.source s.byteOffset

/-- Create a span from start offset to current position -/
def LexerState.spanFrom (s : LexerState) (startOffset : Nat) : Span :=
  Span.fromOffsets s.source startOffset s.byteOffset

/-- Get text between two offsets -/
def LexerState.textBetween (s : LexerState) (startOffset stopOffset : Nat) : String :=
  (s.source.slice startOffset stopOffset).toString

/-! ## Lexer Monad -/

/-- Lexer monad: state + error accumulation -/
abbrev LexerM := StateT LexerState (StateT Diagnostics Id)

/-- Run the lexer monad -/
def LexerM.run' (m : LexerM α) (source : SourceFile) : α × Diagnostics :=
  let initState := LexerState.init source
  let ((result, _), diagnostics) := m.run initState |>.run #[]
  (result, diagnostics)

/-- Record a diagnostic -/
def recordDiagnostic (d : Diagnostic) : LexerM Unit :=
  StateT.lift (modify (·.push d))

/-- Record an error at the current position -/
def recordError (msg : String) : LexerM Unit := do
  let s ← get
  let loc := s.currentLoc
  let span := Span.point loc
  recordDiagnostic (Diagnostic.error msg span)

/-- Record a rich error with secondary labels, notes, and help -/
def recordRichError (msg : String) (span : Span)
    (secondary : Array (Span × String) := #[])
    (notes : Array String := #[])
    (help : Option String := none) : LexerM Unit := do
  let mut diag := Diagnostic.error msg span
  for (s, m) in secondary do
    diag := diag.withSecondary s m
  for n in notes do
    diag := diag.withNote n
  if let some h := help then
    diag := diag.withHelp h
  recordDiagnostic diag

/-- Check if at end -/
def atEnd : LexerM Bool := do
  let s ← get
  return s.atEnd

/-- Get current character -/
def current : LexerM Char := do
  let s ← get
  return s.current

/-- Peek at next character -/
def peekNext : LexerM Char := do
  let s ← get
  return s.peek

/-- Peek n characters ahead -/
def peekAhead (n : Nat) : LexerM Char := do
  let s ← get
  return s.peekN n

/-- Advance one character -/
def advance : LexerM Unit :=
  modify LexerState.advance

/-- Get current byte offset -/
def getOffset : LexerM Nat := do
  let s ← get
  return s.byteOffset

/-- Get current source location -/
def getLoc : LexerM SourceLoc := do
  let s ← get
  return s.currentLoc

/-- Get text between offsets -/
def getText (startOffset stopOffset : Nat) : LexerM String := do
  let s ← get
  return s.textBetween startOffset stopOffset

/-- Create a span from start to current position -/
def spanFrom (startOffset : Nat) : LexerM Span := do
  let s ← get
  return s.spanFrom startOffset

/-- Skip while predicate holds -/
partial def skipWhile (pred : Char → Bool) : LexerM Unit := do
  if (← current) != '\x00' && pred (← current) then
    advance
    skipWhile pred

/-- Collect characters while predicate holds -/
def collectWhile (pred : Char → Bool) : LexerM String := do
  let start ← getOffset
  skipWhile pred
  let stop ← getOffset
  getText start stop

/-- Check if the next characters match a string -/
def lookingAt (str : String) : LexerM Bool := do
  let state ← get
  let mut pos := state.pos
  for c in str.toList do
    if pos ≥ state.source.content.utf8ByteSize then return false
    if String.Pos.Raw.get state.source.content ⟨pos⟩ != c then return false
    pos := (String.Pos.Raw.next state.source.content ⟨pos⟩).byteIdx
  return true

/-- Skip n characters -/
def skipN (n : Nat) : LexerM Unit := do
  for _ in [:n] do
    advance

/-! ## Token Production -/

/-- Make a token -/
def makeToken (kind : TokenKind) (startOffset : Nat) : LexerM Token := do
  let span ← spanFrom startOffset
  let s ← get
  let text := s.textBetween startOffset s.byteOffset
  return { kind, span, text }

/-- Make a single-char token and advance -/
def singleCharToken (kind : TokenKind) : LexerM Token := do
  let start ← getOffset
  advance
  makeToken kind start

/-- Make a multi-char token from already-consumed characters -/
def multiCharToken (kind : TokenKind) (startOffset : Nat) : LexerM Token := do
  makeToken kind startOffset

/-! ## Individual Token Lexers -/

/-- Lex a number -/
def lexNumber : LexerM Token := do
  let start ← getOffset
  skipWhile isDigit
  makeToken .number start

/-- Lex an identifier or keyword -/
def lexIdentifier : LexerM Token := do
  let start ← getOffset
  let firstChar ← current
  advance
  skipWhile isIdentContinue
  let text ← getText start (← getOffset)
  let kind := match lookupKeyword text with
    | some kw => kw
    | none => if firstChar.isLower then .lowerIdent else .upperIdent
  makeToken kind start

/-- Lex a backtick-quoted identifier -/
def lexBacktickIdent : LexerM Token := do
  let start ← getOffset
  advance  -- skip opening `
  let contentStart ← getOffset
  skipWhile (· != '`')
  let contentEnd ← getOffset
  if (← current) == '`' then
    advance  -- skip closing `
    let content ← getText contentStart contentEnd
    let kind := if content.isEmpty || (String.Pos.Raw.get content ⟨0⟩).isLower
                then .lowerIdent
                else .upperIdent
    makeToken kind start
  else
    recordError "unterminated backtick identifier"
    makeToken .error start

/-- Lex a regular string literal -/
def lexStringLit : LexerM Token := do
  let start ← getOffset
  let startLoc ← getLoc
  advance  -- skip opening "
  let contentStart ← getOffset
  while (← current) != '"' && (← current) != '\n' && (← current) != '\x00' do
    advance
  let contentEnd ← getOffset
  if (← current) == '"' then
    advance  -- skip closing "
    let content ← getText contentStart contentEnd
    makeToken (.string content) start
  else
    let endLoc ← getLoc
    let errorSpan := { start := endLoc, stop := endLoc : Span }
    let openingSpan := { start := startLoc, stop := startLoc : Span }
    recordRichError "unterminated string literal" errorSpan
      (secondary := #[(openingSpan, "string starts here")])
      (help := "add a closing '\"' to terminate the string")
    makeToken .error start

/-- Lex a triple-quoted string literal -/
def lexTripleString : LexerM Token := do
  let start ← getOffset
  let startLoc ← getLoc
  skipN 3  -- skip opening """
  let contentStart ← getOffset
  -- Look for closing """
  while !(← atEnd) do
    if (← current) == '"' && (← peekNext) == '"' && (← peekAhead 2) == '"' then
      break
    advance
  let contentEnd ← getOffset
  if (← current) == '"' then
    skipN 3  -- skip closing """
    let content ← getText contentStart contentEnd
    makeToken (.string content) start
  else
    let endLoc ← getLoc
    let errorSpan := { start := endLoc, stop := endLoc : Span }
    let openingSpan := { start := startLoc, stop := startLoc : Span }
    recordRichError "unterminated triple-quoted string" errorSpan
      (secondary := #[(openingSpan, "string starts here")])
      (help := "add closing '\"\"\"' to terminate the string")
    makeToken .error start

/-- Lex an operator -/
def lexOperator : LexerM Token := do
  let start ← getOffset
  skipWhile isOperatorChar
  makeToken .varSymbol start

/-- Skip a line comment (// ...) -/
def skipLineComment : LexerM Unit := do
  skipN 2  -- skip //
  skipWhile (· != '\n')

/-- Skip a block comment -/
def skipBlockComment : LexerM Bool := do
  let startLoc ← getLoc
  skipN 2  -- skip /*
  while !(← atEnd) do
    if (← current) == '*' && (← peekNext) == '/' then
      skipN 2
      return true
    advance
  let endLoc ← getLoc
  let errorSpan := { start := endLoc, stop := endLoc : Span }
  let openingSpan := { start := startLoc, stop := startLoc : Span }
  recordRichError "unterminated block comment" errorSpan
    (secondary := #[(openingSpan, "comment starts here")])
    (help := "add closing '*/' to terminate the comment")
  return false

/-! ## Main Tokenizer -/

/-- Lex a single token (or skip whitespace/comments) -/
partial def lexToken : LexerM (Option Token) := do
  if (← atEnd) then return none

  let c ← current
  let start ← getOffset

  -- Skip spaces (not newlines - those are significant for layout)
  if isSpace c then
    skipWhile isSpace
    return ← lexToken

  -- Handle various token types
  match c with
  -- Comments
  | '/' =>
    if (← peekNext) == '/' then
      skipLineComment
      return ← lexToken
    else if (← peekNext) == '*' then
      let _ ← skipBlockComment
      return ← lexToken
    else if isDigit (← peekNext) || isIdentStart (← peekNext) then
      -- Just a slash before something else
      advance
      return some (← makeToken .slash start)
    else
      -- Operator starting with /
      return some (← lexOperator)

  -- Single character tokens
  | '(' => return some (← singleCharToken .leftParen)
  | ')' => return some (← singleCharToken .rightParen)
  | '{' => return some (← singleCharToken .leftBrace)
  | '}' => return some (← singleCharToken .rightBrace)
  | '[' => return some (← singleCharToken .leftBracket)
  | ']' => return some (← singleCharToken .rightBracket)
  | ',' => return some (← singleCharToken .comma)
  | '@' => return some (← singleCharToken .at)
  | '_' =>
    -- Could be underscore or start of identifier
    if isIdentContinue (← peekNext) then
      return some (← lexIdentifier)
    else
      return some (← singleCharToken .underscore)
  | 'λ' => return some (← singleCharToken .lambda)
  | '\\' => return some (← singleCharToken .lambda)
  | '∀' => return some (← singleCharToken .forallSymbol)
  | '$' => return some (← singleCharToken .dollar)

  -- Multi-character punctuation
  | ':' =>
    if (← peekNext) == ':' then
      skipN 2
      return some (← makeToken .doubleColon start)
    else
      advance
      return some (← makeToken .colon start)

  | '-' =>
    if (← peekNext) == '>' then
      skipN 2
      return some (← makeToken .arrow start)
    else
      return some (← lexOperator)

  | '=' =>
    if (← peekNext) == '>' then
      skipN 2
      return some (← makeToken .fatArrow start)
    else if (← peekNext) == '=' then
      return some (← lexOperator)
    else
      advance
      return some (← makeToken .equals start)

  | '<' =>
    if (← peekNext) == '-' then
      skipN 2
      -- Check for trailing space (Haskell lexer expects "<- ")
      if isSpace (← current) then
        advance
      return some (← makeToken .leftArrow start)
    else if isOperatorChar (← peekNext) then
      return some (← lexOperator)
    else
      advance
      return some (← makeToken .leftAngle start)

  | '>' =>
    if isOperatorChar (← peekNext) then
      return some (← lexOperator)
    else
      advance
      return some (← makeToken .rightAngle start)

  | '|' =>
    if isSpace (← peekNext) then
      advance
      -- Skip the space too
      if isSpace (← current) then advance
      return some (← makeToken .pipe start)
    else
      return some (← lexOperator)

  -- Strings
  | '"' =>
    if (← peekNext) == '"' && (← peekAhead 2) == '"' then
      return some (← lexTripleString)
    else
      return some (← lexStringLit)

  -- Backtick identifiers
  | '`' => return some (← lexBacktickIdent)

  -- Newlines (preserved for layout)
  | '\n' =>
    advance
    return some (← makeToken .layoutSep start)  -- Temporary marker, layout pass will fix

  -- Numbers
  | _ =>
    if isDigit c then
      return some (← lexNumber)
    else if isIdentStart c then
      return some (← lexIdentifier)
    else if isOperatorChar c then
      return some (← lexOperator)
    else
      -- Unknown character
      recordError s!"unexpected character '{c}'"
      advance
      return ← lexToken

/-- Lex all tokens from source -/
partial def tokenize : LexerM (Array Token) := do
  let mut tokens : Array Token := #[]
  while !(← atEnd) do
    match ← lexToken with
    | some tok => tokens := tokens.push tok
    | none => break
  return tokens

/-! ## Layout Transformation -/

/--
Layout state for tracking indentation.
The stack contains column numbers of active layout blocks.
-/
structure LayoutState where
  /-- Stack of indentation levels (column numbers). Always non-empty. -/
  indentStack : List Nat := [0]
  /-- Output tokens -/
  output : Array Token := #[]
  /-- Source file for creating spans -/
  source : SourceFile
  deriving Inhabited

/-- Get current indentation level -/
def LayoutState.currentIndent (s : LayoutState) : Nat :=
  s.indentStack.head!

/-- Push a new indentation level -/
def LayoutState.pushIndent (s : LayoutState) (col : Nat) : LayoutState :=
  { s with indentStack := col :: s.indentStack }

/-- Pop an indentation level -/
def LayoutState.popIndent (s : LayoutState) : LayoutState :=
  match s.indentStack with
  | [] => s  -- Should never happen
  | [_] => s  -- Keep at least one level
  | _ :: rest => { s with indentStack := rest }

/-- Add a token to output -/
def LayoutState.emit (s : LayoutState) (tok : Token) : LayoutState :=
  { s with output := s.output.push tok }

/-- Create a synthetic layout token at a position -/
def LayoutState.syntheticToken (_ : LayoutState) (kind : TokenKind) (loc : SourceLoc) : Token :=
  { kind
  , span := Span.point loc
  , text := ""
  }

/-- Find the next non-newline token and its column -/
def findNextToken (idx : Nat) (toks : Array Token) : Nat × Nat :=
  let rec go (i : Nat) : Nat × Nat :=
    if h : i < toks.size then
      let tok := toks[i]
      if tok.kind == .layoutSep then
        go (i + 1)
      else
        (i, tok.span.start.column)
    else
      (i, 0)
  termination_by toks.size - i
  go idx

/-- Close layout blocks until we reach or pass the target indentation -/
def dedentTo (state : LayoutState) (targetCol : Nat) (loc : SourceLoc) : LayoutState × Bool :=
  let rec go (st : LayoutState) (stack : List Nat) : LayoutState × Bool :=
    match stack with
    | [] => (st, false)
    | [_] => ({ st with indentStack := stack }, st.currentIndent == targetCol)
    | top :: rest =>
      if top <= targetCol then
        ({ st with indentStack := stack }, top == targetCol)
      else
        let newState := st.emit (st.syntheticToken .layoutEnd loc)
        go { newState with indentStack := rest } rest
  termination_by stack.length
  go state state.indentStack

/-- Close all remaining layout blocks at end of file -/
def closeAll (state : LayoutState) : LayoutState :=
  let loc : SourceLoc := {
    file := state.source.id
    byteOffset := state.source.content.utf8ByteSize
    line := state.source.lineStarts.size
    column := 1
  }
  let rec go (st : LayoutState) (stack : List Nat) : LayoutState :=
    match stack with
    | [] => st
    | [_] => st  -- Don't emit LayoutEnd for the base level
    | _ :: rest =>
      let newState := st.emit (st.syntheticToken .layoutEnd loc)
      go { newState with indentStack := rest } rest
  termination_by stack.length
  go state state.indentStack

/--
Process tokens applying layout rules. Extracted as top-level for theorem proving.
-/
def processLayoutTokens (tokens : Array Token) (idx : Nat) (state : LayoutState) : LayoutState :=
  if h : idx < tokens.size then
    let tok := tokens[idx]
    match tok.kind with
    | .layoutSep =>
      -- This is a newline marker from tokenization
      -- Look ahead to find the next non-whitespace token
      let (nextIdx, nextCol) := findNextToken (idx + 1) tokens
      if nextIdx < tokens.size then
        -- Compare with current indent
        let currentIndent := state.currentIndent
        if nextCol > currentIndent then
          -- Deeper indentation: start new layout block
          let state := state.emit (state.syntheticToken .layoutStart tok.span.start)
          let state := state.pushIndent nextCol
          processLayoutTokens tokens (idx + 1) state
        else if nextCol == currentIndent then
          -- Same indentation: layout separator
          let state := state.emit (state.syntheticToken .layoutSep tok.span.start)
          processLayoutTokens tokens (idx + 1) state
        else
          -- Less indentation: close layout blocks
          let (state, _) := dedentTo state nextCol tok.span.start
          let state := state.emit (state.syntheticToken .layoutSep tok.span.start)
          processLayoutTokens tokens (idx + 1) state
      else
        -- No more tokens after newline, skip it
        processLayoutTokens tokens (idx + 1) state
    | _ =>
      -- Regular token: just emit it
      let state := state.emit tok
      processLayoutTokens tokens (idx + 1) state
  else
    -- End of tokens: close all remaining layout blocks
    closeAll state
termination_by tokens.size - idx

/--
Apply layout rules to a stream of tokens.

Layout rules (inspired by Haskell):
1. After a newline, compare the new column to the current layout context:
   - If greater: emit LayoutStart, push new indent level
   - If equal: emit LayoutSep
   - If less: emit LayoutEnd(s), pop indent levels until we match or go past

2. Certain keywords (def, let, case, where, etc.) start a layout context
   if followed by a newline with greater indentation.
-/
def applyLayout (tokens : Array Token) (source : SourceFile) : Array Token :=
  let initState : LayoutState := { source, indentStack := [0], output := #[] }
  let finalState := processLayoutTokens tokens 0 initState
  finalState.output

/-! ## Public API -/

/--
Lex source code into tokens with layout processing.

This is the main entry point for the lexer.
Returns tokens and any diagnostics (errors/warnings) encountered.
-/
def lexCode (source : SourceFile) : Array Token × Diagnostics :=
  -- Phase 1: Raw tokenization
  let (rawTokens, diagnostics) := LexerM.run' tokenize source
  -- Phase 2: Layout transformation
  let tokens := applyLayout rawTokens source
  (tokens, diagnostics)

/-- Convenience function to lex a string -/
def lex (content : String) (path : String := "<input>") : Array Token × Diagnostics :=
  let source := SourceFile.create ⟨0⟩ path content
  lexCode source

end Soma.Syntax
