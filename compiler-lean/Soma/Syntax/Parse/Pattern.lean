import Soma.Syntax.Parser
import Soma.Syntax.Parse.Type

namespace Soma.Syntax.Parse

open ParserM

/-- Parse a variable pattern -/
def parsePatternVar : ParserM (Option SyntaxNode) := do
  match ← parseLowerIdent with
  | some tok => return some (mkNodeSpan .patVar #[mkToken tok] tok.span)
  | none => return none

/-- Parse a wildcard pattern -/
def parsePatternWildcard : ParserM (Option SyntaxNode) := do
  match ← tryConsume .underscore with
  | some tok => return some (mkNodeSpan .patWildcard #[mkToken tok] tok.span)
  | none => return none

/-- Parse a literal pattern (number, string, bool) -/
def parsePatternLit : ParserM (Option SyntaxNode) := do
  let tok ← current
  match tok.kind with
  | .number =>
      advance
      return some (mkNodeSpan .patLit #[mkToken tok] tok.span)
  | .string _ =>
      advance
      return some (mkNodeSpan .patLit #[mkToken tok] tok.span)
  | .true_ =>
      advance
      return some (mkNodeSpan .patLit #[mkToken tok] tok.span)
  | .false_ =>
      advance
      return some (mkNodeSpan .patLit #[mkToken tok] tok.span)
  | _ => return none

/-- Parse a constructor name (uppercase identifier) -/
def parseConstructorName : ParserM (Option SyntaxNode) := do
  match ← parseUpperIdent with
  | some tok => return some (mkNodeSpan .name #[mkToken tok] tok.span)
  | none => return none

mutual

/-- Parse patterns inside parentheses: grouping, tuple, or cons -/
partial def parseParenPattern : ParserM (Option SyntaxNode) := do
  match ← tryConsume .leftParen with
  | some lparen =>
      -- Check for empty tuple ()
      if (← check .rightParen) then
        let rparen ← consumeAny
        let span := Span.merge lparen.span rparen.span
        return some (mkNodeSpan .patTuple #[mkToken lparen, mkToken rparen] span)

      -- Parse first pattern
      match ← parsePattern with
      | some first =>
          let tok ← current
          match tok.kind with
          -- Cons pattern: (x:xs)
          | .colon =>
              let colonTok ← consumeAny
              match ← parsePattern with
              | some tail =>
                  match ← tryConsume .rightParen with
                  | some rparen =>
                      let span := Span.merge lparen.span rparen.span
                      return some (mkNodeSpan .patCons #[mkToken lparen, first, mkToken colonTok, tail, mkToken rparen] span)
                  | none =>
                      recordRichError "expected ')' after cons pattern"
                        (← current).span
                        (secondary := #[(lparen.span, "'(' is here")])
                        (notes := #["cons pattern syntax: (head : tail)", "matches list construction"])
                        (help := "add ')' to close the cons pattern")
                      let span := Span.merge lparen.span tail.span
                      return some (mkError span "unclosed cons pattern" #[mkToken lparen, first, tail])
              | none =>
                  recordRichError "expected pattern after ':'"
                    (← current).span
                    (secondary := #[(colonTok.span, "':' is here")])
                    (notes := #["cons pattern syntax: (head : tail)"])
                    (help := "provide a pattern for the tail (usually a list pattern or variable)")
                  let span := Span.merge lparen.span colonTok.span
                  return some (mkError span "incomplete cons pattern" #[mkToken lparen, first, mkToken colonTok])

          -- Tuple pattern: (a, b, c)
          | .comma =>
              let mut elements := #[first]
              while (← check .comma) do
                let commaTok ← consumeAny  -- consume comma
                match ← parsePattern with
                | some elem => elements := elements.push elem
                | none =>
                    recordRichError "expected pattern after ','"
                      (← current).span
                      (secondary := #[(commaTok.span, "comma is here")])
                      (help := "provide a pattern after the comma, e.g., '(a, b, c)'")
                    break
              match ← tryConsume .rightParen with
              | some rparen =>
                  let span := Span.merge lparen.span rparen.span
                  return some (mkNodeSpan .patTuple (#[mkToken lparen] ++ elements ++ #[mkToken rparen]) span)
              | none =>
                  recordRichError "expected ')' after tuple pattern"
                    (← current).span
                    (secondary := #[(lparen.span, "'(' is here")])
                    (help := "add ')' to close the tuple pattern")
                  let span := Span.merge lparen.span (elements[elements.size - 1]!.span)
                  return some (mkError span "unclosed tuple pattern" (#[mkToken lparen] ++ elements))

          -- Parenthesized pattern: (pat)
          | .rightParen =>
              let rparen ← consumeAny
              let span := Span.merge lparen.span rparen.span
              return some (mkNodeSpan .patParens #[mkToken lparen, first, mkToken rparen] span)

          | _ =>
              recordRichError s!"expected ')', ':', or ',' in pattern, found {tok.kind.describe}"
                tok.span
                (secondary := #[(lparen.span, "'(' is here")])
                (notes := #["parenthesized pattern: (pat)", "tuple pattern: (p1, p2)", "cons pattern: (h : t)"])
                (help := "add ')', add ',', or add ':' depending on the pattern type")
              return some (mkError lparen.span "malformed parenthesized pattern" #[mkToken lparen, first])

      | none =>
          recordRichError "expected pattern after '('"
            lparen.span
            (help := "provide a pattern, or use '()' for unit pattern")
          return some (mkError lparen.span "empty parentheses" #[mkToken lparen])

  | none => return none

/-- Parse a list pattern: [a, b, c] -/
partial def parseListPattern : ParserM (Option SyntaxNode) := do
  match ← tryConsume .leftBracket with
  | some lbracket =>
      -- Check for empty list []
      if (← check .rightBracket) then
        let rbracket ← consumeAny
        let span := Span.merge lbracket.span rbracket.span
        return some (mkNodeSpan .patList #[mkToken lbracket, mkToken rbracket] span)

      -- Parse comma-separated patterns
      let elements ← commaSep parsePattern
      match ← tryConsume .rightBracket with
      | some rbracket =>
          let span := Span.merge lbracket.span rbracket.span
          return some (mkNodeSpan .patList (#[mkToken lbracket] ++ elements ++ #[mkToken rbracket]) span)
      | none =>
          recordRichError "expected ']' after list pattern"
            (← current).span
            (secondary := #[(lbracket.span, "'[' is here")])
            (notes := #["list pattern syntax: [p1, p2, p3]"])
            (help := "add ']' to close the list pattern")
          let lastSpan := if elements.isEmpty then lbracket.span else elements[elements.size - 1]!.span
          return some (mkError (Span.merge lbracket.span lastSpan) "unclosed list pattern" (#[mkToken lbracket] ++ elements))

  | none => return none

/--
Parse a single pattern atom (no application).
-/
partial def parsePatternAtom : ParserM (Option SyntaxNode) := do
  -- Try each pattern form
  if let some pat ← parsePatternVar then return some pat
  if let some pat ← parsePatternWildcard then return some pat
  if let some pat ← parsePatternLit then return some pat
  if let some pat ← parseParenPattern then return some pat
  if let some pat ← parseListPattern then return some pat
  if let some pat ← parseConstructorName then return some pat
  return none

/--
Parse a pattern, which may be a constructor application: Some x, Cons h t

Constructor patterns are parsed as a constructor name followed by zero or more
pattern atoms.
-/
partial def parsePattern : ParserM (Option SyntaxNode) := do
  match ← parsePatternAtom with
  | some first =>
      -- Check if this is a constructor (uppercase name)
      if first.kind? == some .name then
        -- Try to parse more pattern atoms as constructor arguments
        let mut args := #[first]
        while true do
          -- Don't consume patterns that could be the start of another clause
          let tok ← current
          if tok.kind == .fatArrow || tok.kind == .equals ||
             tok.kind == .pipe || tok.kind == .layoutSep ||
             tok.kind == .layoutEnd || tok.kind == .rightParen ||
             tok.kind == .rightBracket || tok.kind == .comma ||
             tok.kind == .colon || tok.kind == .kw_if then
            break
          match ← parsePatternAtom with
          | some arg => args := args.push arg
          | none => break
        if args.size == 1 then
          -- Just the constructor name, could be a nullary constructor
          return some first
        else
          -- Constructor with arguments
          let span := Span.merge args[0]!.span args[args.size - 1]!.span
          return some (mkNodeSpan .patCon args span)
      else
        return some first
  | none => return none

end  -- end mutual block

/-- Parse a pattern with optional type annotation: (pat :: Type) -/
partial def parseTypedPattern : ParserM (Option SyntaxNode) := do
  match ← parsePattern with
  | some pat =>
      if (← check .doubleColon) then
        let colonTok ← consumeAny
        match ← parseType with
        | some ty =>
            let span := Span.merge pat.span ty.span
            return some (mkNodeSpan .patTyped #[pat, mkToken colonTok, ty] span)
        | none =>
            recordRichError "expected type after '::'"
              (← current).span
              (secondary := #[(colonTok.span, "'::' is here")])
              (notes := #["typed pattern syntax: (pattern :: Type)"])
              (help := "provide a type")
            return some pat
      else
        return some pat
  | none => return none

end Soma.Syntax.Parse
