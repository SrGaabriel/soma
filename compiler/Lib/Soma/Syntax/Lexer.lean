import Soma.Syntax.Source
import Soma.Syntax.GreenTree
import Soma.Syntax.Diagnostic

namespace Soma.Syntax

def isSpace (c : Char) : Bool := c == ' ' || c == '\t'
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isLetter (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def isEmoji (c : Char) : Bool :=
  let n := c.toNat
  (0x1F300 ≤ n && n ≤ 0x1F9FF) || (0x2600 ≤ n && n ≤ 0x26FF) || (0x2700 ≤ n && n ≤ 0x27BF)

def isIdentStart (c : Char) : Bool := isLetter c || c == '_' || isEmoji c
def isIdentContinue (c : Char) : Bool := isIdentStart c || isDigit c

def isOperatorChar (c : Char) : Bool :=
  c == '!' || c == '$' || c == '%' || c == '&' ||
  c == '*' || c == '+' || c == '.' || c == '-' || c == '/' ||
  c == '<' || c == '=' || c == '>' || c == '?' || c == '|'

/-! ## Lexer State -/

structure LexerState where
  source : SourceFile
  pos : Nat  -- byte offset
  deriving Inhabited

namespace LexerState

def init (source : SourceFile) : LexerState := { source, pos := 0 }

def atEnd (s : LexerState) : Bool := s.pos ≥ s.source.content.utf8ByteSize

def current (s : LexerState) : Char :=
  if s.atEnd then '\x00' else String.Pos.Raw.get s.source.content ⟨s.pos⟩

def peek (s : LexerState) : Char :=
  let nextPos := (String.Pos.Raw.next s.source.content ⟨s.pos⟩).byteIdx
  if nextPos ≥ s.source.content.utf8ByteSize then '\x00'
  else String.Pos.Raw.get s.source.content ⟨nextPos⟩

def peekN (s : LexerState) (n : Nat) : Char :=
  let rec go (pos : Nat) (remaining : Nat) : Char :=
    if pos ≥ s.source.content.utf8ByteSize then '\x00'
    else if h : remaining == 0 then String.Pos.Raw.get s.source.content ⟨pos⟩
    else
      have : remaining - 1 < remaining := Nat.sub_lt (Nat.pos_of_ne_zero (by simp_all)) (by omega)
      go (String.Pos.Raw.next s.source.content ⟨pos⟩).byteIdx (remaining - 1)
  termination_by remaining
  go s.pos n

def advance (s : LexerState) : LexerState :=
  if s.atEnd then s
  else { s with pos := (String.Pos.Raw.next s.source.content ⟨s.pos⟩).byteIdx }

def textBetween (s : LexerState) (startOffset stopOffset : Nat) : String :=
  s.source.slice startOffset stopOffset

def currentLoc (s : LexerState) : SourceLoc :=
  SourceLoc.fromOffset s.source s.pos

def spanFrom (s : LexerState) (startOffset : Nat) : Span :=
  Span.fromOffsets s.source startOffset s.pos

end LexerState

/-! ## Lexer Monad -/

abbrev LexerM := StateT LexerState (StateT Diagnostics Id)

namespace LexerM

def run' (m : LexerM α) (source : SourceFile) : α × Diagnostics :=
  let ((result, _), diagnostics) := m.run (LexerState.init source) |>.run #[]
  (result, diagnostics)

def recordDiagnostic (d : Diagnostic) : LexerM Unit :=
  StateT.lift (modify (·.push d))

def recordError (msg : String) : LexerM Unit := do
  let s ← get
  recordDiagnostic (Diagnostic.error msg (Span.point s.currentLoc))

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

def atEnd : LexerM Bool := do return (← get).atEnd
def current : LexerM Char := do return (← get).current
def peekNext : LexerM Char := do return (← get).peek
def peekAhead (n : Nat) : LexerM Char := do return (← get).peekN n
def advance : LexerM Unit := modify LexerState.advance
def getOffset : LexerM Nat := do return (← get).pos
def getLoc : LexerM SourceLoc := do return (← get).currentLoc
def getText (start stop : Nat) : LexerM String := do return (← get).textBetween start stop
def spanFrom (start : Nat) : LexerM Span := do return (← get).spanFrom start

partial def skipWhile (pred : Char → Bool) : LexerM Unit := do
  if (← current) != '\x00' && pred (← current) then
    advance
    skipWhile pred

def collectWhile (pred : Char → Bool) : LexerM String := do
  let start ← getOffset
  skipWhile pred
  getText start (← getOffset)

def lookingAt (str : String) : LexerM Bool := do
  let state ← get
  let mut pos := state.pos
  for c in str.toList do
    if pos ≥ state.source.content.utf8ByteSize then return false
    if String.Pos.Raw.get state.source.content ⟨pos⟩ != c then return false
    pos := (String.Pos.Raw.next state.source.content ⟨pos⟩).byteIdx
  return true

def skipN (n : Nat) : LexerM Unit := do
  for _ in [:n] do advance
end LexerM

-- Open LexerM for use in tokenization code below
open LexerM


/-- Raw token with offset info (before building green tree) -/
structure RawToken where
  kind : TokenKind
  text : String
  offset : Nat
  deriving Repr, Inhabited

def makeToken (kind : TokenKind) (startOffset : Nat) : LexerM RawToken := do
  let text ← getText startOffset (← getOffset)
  return { kind, text, offset := startOffset }

def singleCharToken (kind : TokenKind) : LexerM RawToken := do
  let start ← getOffset
  advance
  makeToken kind start

def lexNumber : LexerM RawToken := do
  let start ← getOffset
  skipWhile isDigit
  makeToken .number start

def lexIdentifier : LexerM RawToken := do
  let start ← getOffset
  let firstChar ← current
  advance
  skipWhile isIdentContinue
  let text ← getText start (← getOffset)
  let kind := match lookupKeyword text with
    | some kw => kw
    | none => if firstChar.isLower then .lowerIdent else .upperIdent
  makeToken kind start

def lexBacktickIdent : LexerM RawToken := do
  let start ← getOffset
  advance  -- skip `
  let contentStart ← getOffset
  skipWhile (· != '`')
  let contentEnd ← getOffset
  if (← current) == '`' then
    advance
    let content ← getText contentStart contentEnd
    let kind := if content.isEmpty || (String.Pos.Raw.get content ⟨0⟩).isLower
                then .lowerIdent else .upperIdent
    makeToken kind start
  else
    recordError "unterminated backtick identifier"
    makeToken .error start

def lexStringLit : LexerM RawToken := do
  let start ← getOffset
  advance  -- skip "
  let contentStart ← getOffset
  while (← current) != '"' && (← current) != '\n' && (← current) != '\x00' do
    advance
  let contentEnd ← getOffset
  if (← current) == '"' then
    advance
    let content ← getText contentStart contentEnd
    makeToken (.string content) start
  else
    let span ← spanFrom start
    recordRichError "unterminated string literal" span
      (help := "add a closing '\"' to terminate the string")
    makeToken .error start

def lexTripleString : LexerM RawToken := do
  let start ← getOffset
  skipN 3  -- skip """
  let contentStart ← getOffset
  while !(← atEnd) do
    if (← current) == '"' && (← peekNext) == '"' && (← peekAhead 2) == '"' then
      break
    advance
  let contentEnd ← getOffset
  if (← current) == '"' then
    skipN 3
    let content ← getText contentStart contentEnd
    makeToken (.string content) start
  else
    let span ← spanFrom start
    recordRichError "unterminated triple-quoted string" span
      (help := "add closing '\"\"\"' to terminate the string")
    makeToken .error start

def lexOperator : LexerM RawToken := do
  let start ← getOffset
  skipWhile isOperatorChar
  makeToken .varSymbol start

def lexLineComment (start : Nat) : LexerM RawToken := do
  skipN 2
  skipWhile (· != '\n')
  makeToken .comment start

def lexBlockComment (start : Nat) : LexerM (Option RawToken) := do
  let startLoc ← getLoc
  skipN 2
  while !(← atEnd) do
    if (← current) == '*' && (← peekNext) == '/' then
      skipN 2
      return some (← makeToken .comment start)
    advance
  let span ← spanFrom startLoc.byteOffset
  recordRichError "unterminated block comment" span
    (help := "add closing '*/' to terminate the comment")
  -- Still return a token for the partial comment so spans are preserved
  return some (← makeToken .comment start)

/-! ## Main Tokenizer -/

partial def lexToken : LexerM (Option RawToken) := do
  if (← atEnd) then return none

  let c ← current
  let start ← getOffset

  -- Produce whitespace token (but not newlines - they become layoutSep)
  if isSpace c && c != '\n' then
    skipWhile (fun ch => isSpace ch && ch != '\n')
    return some (← makeToken .whitespace start)

  match c with
  | '/' =>
    if (← peekNext) == '/' then return some (← lexLineComment start)
    else if (← peekNext) == '*' then return (← lexBlockComment start)
    else if isDigit (← peekNext) || isIdentStart (← peekNext) then
      advance; return some (← makeToken .slash start)
    else return some (← lexOperator)
  | '(' => return some (← singleCharToken .leftParen)
  | ')' => return some (← singleCharToken .rightParen)
  | '{' => return some (← singleCharToken .leftBrace)
  | '}' => return some (← singleCharToken .rightBrace)
  | '[' => return some (← singleCharToken .leftBracket)
  | ']' => return some (← singleCharToken .rightBracket)
  | ',' => return some (← singleCharToken .comma)
  | '@' => return some (← singleCharToken .at)
  | '_' =>
    if isIdentContinue (← peekNext) then return some (← lexIdentifier)
    else return some (← singleCharToken .underscore)
  | 'λ' => return some (← singleCharToken .lambda)
  | '\\' => return some (← singleCharToken .lambda)
  | '∀' => return some (← singleCharToken .forallSymbol)
  | '×' => return some (← singleCharToken .times)
  | 'ω' => return some (← singleCharToken .omega)
  | '$' => return some (← singleCharToken .dollar)
  | ':' =>
    if (← peekNext) == ':' then skipN 2; return some (← makeToken .doubleColon start)
    else advance; return some (← makeToken .colon start)
  | '-' =>
    if (← peekNext) == '>' then skipN 2; return some (← makeToken .arrow start)
    else return some (← lexOperator)
  | '=' =>
    if (← peekNext) == '>' then skipN 2; return some (← makeToken .fatArrow start)
    else if (← peekNext) == '=' then return some (← lexOperator)
    else advance; return some (← makeToken .equals start)
  | '<' =>
    if (← peekNext) == '-' then
      skipN 2
      if isSpace (← current) then advance
      return some (← makeToken .leftArrow start)
    else if isOperatorChar (← peekNext) then return some (← lexOperator)
    else advance; return some (← makeToken .leftAngle start)
  | '>' =>
    if isOperatorChar (← peekNext) then return some (← lexOperator)
    else advance; return some (← makeToken .rightAngle start)
  | '|' =>
    if isSpace (← peekNext) then
      advance
      if isSpace (← current) then advance
      return some (← makeToken .pipe start)
    else return some (← lexOperator)
  | '.' =>
    if isIdentStart (← peekNext) then
      return some (← singleCharToken .dot)
    else return some (← lexOperator)
  | '"' =>
    if (← peekNext) == '"' && (← peekAhead 2) == '"' then return some (← lexTripleString)
    else return some (← lexStringLit)
  | '`' => return some (← lexBacktickIdent)
  | '#' => return some (← singleCharToken .hash)
  | '\n' => advance; return some (← makeToken .layoutSep start)
  | _ =>
    if isDigit c then return some (← lexNumber)
    else if isIdentStart c then return some (← lexIdentifier)
    else if isOperatorChar c then return some (← lexOperator)
    else recordError s!"unexpected character '{c}'"; advance; return ← lexToken

partial def tokenize : LexerM (Array RawToken) := do
  let mut tokens : Array RawToken := #[]
  while !(← atEnd) do
    match ← lexToken with
    | some tok => tokens := tokens.push tok
    | none => break
  return tokens

/-! ## Layout Transformation -/

structure LayoutState where
  indentStack : List Nat := [1]  -- 1-based column (matches columnAt)
  output : Array RawToken := #[]
  lastWasSep : Bool := false  -- Track if last emitted token was layoutSep (to avoid duplicates from blank lines)
  deriving Inhabited

def LayoutState.currentIndent (s : LayoutState) : Nat := s.indentStack.head!

def LayoutState.pushIndent (s : LayoutState) (col : Nat) : LayoutState :=
  { s with indentStack := col :: s.indentStack }

def LayoutState.popIndent (s : LayoutState) : LayoutState :=
  match s.indentStack with
  | [] | [_] => s
  | _ :: rest => { s with indentStack := rest }

def LayoutState.emit (s : LayoutState) (tok : RawToken) : LayoutState :=
  { s with
    output := s.output.push tok
    -- Only update lastWasSep for non-trivia tokens (whitespace shouldn't reset the flag)
    lastWasSep := if tok.kind == .whitespace then s.lastWasSep else tok.kind == .layoutSep }

def LayoutState.syntheticToken (kind : TokenKind) (offset : Nat) (text : String := "") : RawToken :=
  { kind, text, offset }

def findNextToken (idx : Nat) (toks : Array RawToken) (source : SourceFile) : Nat × Nat :=
  let rec go (i : Nat) : Nat × Nat :=
    if h : i < toks.size then
      let tok := toks[i]
      -- Skip both layoutSep and whitespace to find the next meaningful token
      if tok.kind == .layoutSep || tok.kind == .whitespace then go (i + 1)
      else (i, source.columnAt tok.offset)
    else (i, 0)
  termination_by toks.size - i
  go idx

def dedentTo (st : LayoutState) (targetCol : Nat) (offset : Nat) : LayoutState × Bool :=
  match hstack : st.indentStack with
  | [] => (st, false)
  | [_] => (st, st.currentIndent == targetCol)
  | top :: tl =>
    if top <= targetCol then (st, top == targetCol)
    else
      have hLen : tl.length < st.indentStack.length := by simp only [hstack, List.length_cons]; omega
      dedentTo { st.emit (LayoutState.syntheticToken .layoutEnd offset) with indentStack := tl } targetCol offset
termination_by st.indentStack.length

def closeAll (st : LayoutState) (offset : Nat) : LayoutState :=
  match hstack : st.indentStack with
  | [] | [_] => st
  | _ :: tl =>
    have hLen : tl.length < st.indentStack.length := by simp only [hstack, List.length_cons]; omega
    closeAll { st.emit (LayoutState.syntheticToken .layoutEnd offset) with indentStack := tl } offset
termination_by st.indentStack.length

def processLayoutTokens (tokens : Array RawToken) (idx : Nat) (state : LayoutState) (source : SourceFile) : LayoutState :=
  if h : idx < tokens.size then
    let tok := tokens[idx]
    match tok.kind with
    | .layoutSep =>
      let (nextIdx, nextCol) := findNextToken (idx + 1) tokens source
      if nextIdx < tokens.size then
        let currentIndent := state.currentIndent
        if nextCol > currentIndent then
          -- Emit zero-width layoutStart, then the newline as whitespace trivia
          let state := state.emit (LayoutState.syntheticToken .layoutStart tok.offset)
          let state := state.emit { tok with kind := .whitespace }
          let state := state.pushIndent nextCol
          processLayoutTokens tokens (idx + 1) state source
        else if nextCol == currentIndent then
          -- Only emit layoutSep if we're inside a layout block (more than base indent)
          -- and we haven't just emitted one (blank lines cause duplicate separators)
          if state.indentStack.length > 1 && !state.lastWasSep then
            -- Emit zero-width layoutSep, then the newline as whitespace trivia
            let state := state.emit (LayoutState.syntheticToken .layoutSep tok.offset)
            let state := state.emit { tok with kind := .whitespace }
            processLayoutTokens tokens (idx + 1) state source
          else
            -- At base level or duplicate sep, emit as whitespace trivia (preserves offset tracking)
            let state := state.emit { tok with kind := .whitespace }
            processLayoutTokens tokens (idx + 1) state source
        else
          -- Dedent to the target column - layoutEnd(s) will be emitted
          -- Emit the newline as whitespace to preserve offset tracking
          let (state, atMatchingLevel) := dedentTo state nextCol tok.offset
          -- If we landed at a matching indentation level, also emit a layoutSep
          let state := if atMatchingLevel && state.indentStack.length > 1 then
            state.emit (LayoutState.syntheticToken .layoutSep tok.offset)
          else state
          let state := state.emit { tok with kind := .whitespace }
          processLayoutTokens tokens (idx + 1) state source
      else
        -- At end of file, emit the newline as whitespace to preserve byte width
        let state := state.emit { tok with kind := .whitespace }
        processLayoutTokens tokens (idx + 1) state source
    | _ =>
      let state := state.emit tok
      processLayoutTokens tokens (idx + 1) state source
  else
    closeAll state (if tokens.isEmpty then 0 else tokens[tokens.size - 1]!.offset)
termination_by tokens.size - idx

def applyLayout (tokens : Array RawToken) (source : SourceFile) : Array RawToken :=
  let finalState := processLayoutTokens tokens 0 {} source
  finalState.output

/--
Lex source code into green tokens.

Returns an array of green token nodes and any diagnostics.
-/
def lexCode (source : SourceFile) : Array GreenNode × Diagnostics :=
  let (rawTokens, diagnostics) := LexerM.run' tokenize source
  let layoutTokens := applyLayout rawTokens source
  let greenTokens := layoutTokens.map fun tok => GreenNode.token tok.kind tok.text
  (greenTokens, diagnostics)

/-- Convenience function to lex a string -/
def lex (content : String) (path : String := "<input>") : Array GreenNode × Diagnostics :=
  let source := SourceFile.create ⟨0⟩ path content
  lexCode source

end Soma.Syntax
