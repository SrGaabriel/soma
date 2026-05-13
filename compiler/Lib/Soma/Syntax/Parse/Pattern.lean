import Soma.Syntax.Parser

namespace Soma.Syntax.Parse

open ParserM

def parsePatternVar : ParserM (Option GreenNode) := do
  let tok ← current
  if tok.kind != some .lowerIdent then return none
  let nextTok ← peekNext
  if nextTok.kind == some .doubleColon then return none
  match ← parseLowerIdent with
  | some nameTok => return some (GreenNode.mkNode .patVar #[nameTok])
  | none => return none

def parsePatternWildcard : ParserM (Option GreenNode) := do
  match ← tryConsume .underscore with
  | some tok => return some (GreenNode.mkNode .patWildcard #[tok])
  | none => return none

def parsePatternLit : ParserM (Option GreenNode) := do
  let tok ← current
  match tok.kind with
  | some .number | some (.string _) | some .true_ | some .false_ =>
      let g ← consumeAny
      return some (GreenNode.mkNode .patLit #[g])
  | _ => return none

private def parseIdentAny : ParserM (Option GreenNode) := do
  let tok ← current
  match tok.kind with
  | some .lowerIdent | some .upperIdent => some <$> consumeAny
  | _ => return none

def parseConstructorName : ParserM (Option GreenNode) := do
  match ← parseIdentAny with
  | none => return none
  | some first =>
      let mut parts : Array GreenNode := #[first]
      let mut sawQualified := false
      while (← check .doubleColon) do
        sawQualified := true
        let sep ← consumeAny
        match ← parseIdentAny with
        | some next =>
            parts := parts.push sep
            parts := parts.push next
        | none =>
            recordExpected "identifier after '::' in constructor name"
            return some (GreenNode.mkError "incomplete qualified constructor" (parts.push sep))

      -- Keep old behavior for single-segment names: only UpperIdent is a constructor.
      if !sawQualified then
        let headTok := first
        if headTok.tokenKind? != some .upperIdent then
          return none

      return some (GreenNode.mkNode .name parts)

mutual

partial def parseParenPattern : ParserM (Option GreenNode) := do
  match ← tryConsume .leftParen with
  | some lparen =>
      if (← check .rightParen) then
        let rparen ← consumeAny
        return some (GreenNode.mkNode .patTuple #[lparen, rparen])

      match ← parsePattern with
      | some first =>
          if (← check .colon) then
            let colonTok ← consumeAny
            match ← parsePattern with
            | some tail =>
                match ← tryConsume .rightParen with
                | some rparen =>
                    return some (GreenNode.mkNode .patCons #[lparen, first, colonTok, tail, rparen])
                | none =>
                    recordExpected "')' after cons pattern"
                    return some (GreenNode.mkError "unclosed cons pattern" #[lparen, first, colonTok, tail])
            | none =>
                recordExpected "pattern after ':'"
                return some (GreenNode.mkError "incomplete cons pattern" #[lparen, first, colonTok])
          else if (← check .comma) then
            let mut elements := #[first]
            while (← check .comma) do
              let comma ← consumeAny
              elements := elements.push comma
              match ← parsePattern with
              | some elem => elements := elements.push elem
              | none => recordExpected "pattern after ','"; break
            match ← tryConsume .rightParen with
            | some rparen =>
                return some (GreenNode.mkNode .patTuple (#[lparen] ++ elements ++ #[rparen]))
            | none =>
                recordExpected "')' after tuple pattern"
                return some (GreenNode.mkError "unclosed tuple pattern" (#[lparen] ++ elements))
          else
            match ← tryConsume .rightParen with
            | some rparen =>
                return some (GreenNode.mkNode .patParens #[lparen, first, rparen])
            | none =>
                recordExpected "')', ':', or ',' in pattern"
                return some (GreenNode.mkError "malformed parenthesized pattern" #[lparen, first])
      | none =>
          recordExpected "pattern after '('"
          return some (GreenNode.mkError "empty parentheses" #[lparen])
  | none => return none

partial def parseListPattern : ParserM (Option GreenNode) := do
  match ← tryConsume .leftBracket with
  | some lbracket =>
      if (← check .rightBracket) then
        let rbracket ← consumeAny
        return some (GreenNode.mkNode .patList #[lbracket, rbracket])

      let elements ← commaSep parsePattern
      match ← tryConsume .rightBracket with
      | some rbracket =>
          return some (GreenNode.mkNode .patList (#[lbracket] ++ elements ++ #[rbracket]))
      | none =>
          recordExpected "']' after list pattern"
          return some (GreenNode.mkError "unclosed list pattern" (#[lbracket] ++ elements))
  | none => return none

/-- Parse a variant pattern: .label or .label pat -/
partial def parseVariantPattern : ParserM (Option GreenNode) := do
  -- Check for .identifier pattern (variant pattern)
  let tok ← current
  if tok.kind != some .dot then return none
  let nextTok ← peekNext
  -- Accept both upper and lower case identifiers for variant labels
  if nextTok.kind != some .lowerIdent && nextTok.kind != some .upperIdent then return none
  -- Parse .label
  let dotTok ← consumeAny
  let labelTok ← consumeAny
  -- Optionally parse an argument pattern (but don't consume delimiters, etc.)
  let argTok ← current
  if argTok.kind == some .fatArrow || argTok.kind == some .equals ||
     argTok.kind == some .pipe || argTok.kind == some .layoutStart ||
     argTok.kind == some .layoutSep || argTok.kind == some .layoutEnd ||
     argTok.kind == some .rightParen || argTok.kind == some .rightBracket ||
     argTok.kind == some .comma || argTok.kind == some .colon ||
     argTok.kind == some .kw_if || argTok.kind == some .eof then
    -- No argument, just .label
    return some (GreenNode.mkNode .patVariant #[dotTok, labelTok])
  else
    -- Try to parse an argument pattern atom
    match ← parsePatternAtom with
    | some arg =>
        return some (GreenNode.mkNode .patVariant #[dotTok, labelTok, arg])
    | none =>
        -- No argument parsed, just .label
        return some (GreenNode.mkNode .patVariant #[dotTok, labelTok])

partial def parsePatternAtom : ParserM (Option GreenNode) := do
  if let some pat ← parseVariantPattern then return some pat
  if let some pat ← parsePatternVar then return some pat
  if let some pat ← parsePatternWildcard then return some pat
  if let some pat ← parsePatternLit then return some pat
  if let some pat ← parseParenPattern then return some pat
  if let some pat ← parseListPattern then return some pat
  if let some pat ← parseConstructorName then return some pat
  return none

partial def parsePattern : ParserM (Option GreenNode) := do
  match ← parsePatternAtom with
  | some first =>
      if first.syntaxKind? == some .name then
        let mut args := #[first]
        while true do
          let tok ← current
          if tok.kind == some .fatArrow || tok.kind == some .equals ||
             tok.kind == some .pipe || tok.kind == some .layoutStart ||
             tok.kind == some .layoutSep || tok.kind == some .layoutEnd ||
             tok.kind == some .rightParen || tok.kind == some .rightBracket ||
             tok.kind == some .comma || tok.kind == some .colon ||
             tok.kind == some .kw_if || tok.kind == some .eof then
            break
          match ← parsePatternAtom with
          | some arg => args := args.push arg
          | none => break
        if args.size == 1 then return some first
        else return some (GreenNode.mkNode .patCon args)
      else
        return some first
  | none => return none

end

end Soma.Syntax.Parse
