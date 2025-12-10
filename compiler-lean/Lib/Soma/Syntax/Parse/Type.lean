import Soma.Syntax.Parser

namespace Soma.Syntax.Parse

open ParserM

/-! ## Type Atoms -/

/-- Parse a type variable (lower-case identifier) -/
def parseTypeVar : ParserM (Option SyntaxNode) := do
  match ← parseLowerIdent with
  | some tok => return some (mkNodeSpan .typeVar #[mkToken tok] tok.span)
  | none => return none

/-- Parse a type constructor (upper-case identifier) -/
def parseTypeCon : ParserM (Option SyntaxNode) := do
  match ← parseUpperIdent with
  | some tok => return some (mkNodeSpan .typeCon #[mkToken tok] tok.span)
  | none => return none

/-- Check if current token is a dot operator -/
def checkDot : ParserM Bool := do
  let tok ← current
  return tok.kind == .varSymbol && tok.text == "."

/-- Consume a dot operator if present -/
def tryConsumeDot : ParserM (Option Token) := do
  if (← checkDot) then
    let tok ← consumeAny
    return some tok
  else
    return none

mutual

/-- Parse types inside parentheses: grouping or tuple -/
partial def parseParenType : ParserM (Option SyntaxNode) := do
  match ← tryConsume .leftParen with
  | some lparen =>
      -- Check for empty tuple type ()
      if (← check .rightParen) then
        let rparen ← consumeAny
        let span := Span.merge lparen.span rparen.span
        return some (mkNodeSpan .typeTuple #[mkToken lparen, mkToken rparen] span)

      -- Parse first type
      match ← parseType with
      | some first =>
          let tok ← current
          match tok.kind with
          -- Tuple type: (a, b, c)
          | .comma =>
              let mut elements := #[first]
              while (← check .comma) do
                let commaTok ← consumeAny  -- consume comma
                match ← parseType with
                | some elem => elements := elements.push elem
                | none =>
                    recordRichError "expected type after ','"
                      (← current).span
                      (secondary := #[(commaTok.span, "comma is here")])
                      (help := "provide a type after the comma, e.g., '(Int, String, Bool)'")
                    break
              match ← tryConsume .rightParen with
              | some rparen =>
                  let span := Span.merge lparen.span rparen.span
                  return some (mkNodeSpan .typeTuple (#[mkToken lparen] ++ elements ++ #[mkToken rparen]) span)
              | none =>
                  recordRichError "expected ')' after tuple type"
                    (← current).span
                    (secondary := #[(lparen.span, "opening '(' is here")])
                    (help := "add ')' to close the tuple type")
                  let span := Span.merge lparen.span (elements[elements.size - 1]!.span)
                  return some (mkError span "unclosed tuple type" (#[mkToken lparen] ++ elements))

          -- Parenthesized type: (Type)
          | .rightParen =>
              let rparen ← consumeAny
              let span := Span.merge lparen.span rparen.span
              return some (mkNodeSpan .typeParens #[mkToken lparen, first, mkToken rparen] span)

          | _ =>
              recordRichError s!"expected ')' or ',' in type, found {tok.kind.describe}"
                tok.span
                (secondary := #[(lparen.span, "parenthesized type starts here")])
                (notes := #["tuple type syntax: (Type1, Type2, Type3)", "parenthesized type syntax: (Type)"])
                (help := "add ')' to close, or add ',' if this is a tuple")
              return some (mkError lparen.span "malformed parenthesized type" #[mkToken lparen, first])

      | none =>
          recordRichError "expected type after '('"
            lparen.span
            (help := "provide a type, or use '()' for unit type")
          return some (mkError lparen.span "empty type parentheses" #[mkToken lparen])

  | none => return none

/-- Parse a list type: [a] -/
partial def parseListType : ParserM (Option SyntaxNode) := do
  match ← tryConsume .leftBracket with
  | some lbracket =>
      match ← parseType with
      | some elemType =>
          match ← tryConsume .rightBracket with
          | some rbracket =>
              let span := Span.merge lbracket.span rbracket.span
              return some (mkNodeSpan .typeList #[mkToken lbracket, elemType, mkToken rbracket] span)
          | none =>
              recordRichError "expected ']' after list type"
                (← current).span
                (secondary := #[(lbracket.span, "'[' is here")])
                (notes := #["list type syntax: [ElementType]"])
                (help := "add ']' to close the list type")
              return some (mkError (Span.merge lbracket.span elemType.span) "unclosed list type" #[mkToken lbracket, elemType])
      | none =>
          -- Empty brackets [] - could be list type with missing element
          match ← tryConsume .rightBracket with
          | some rbracket =>
              -- This is actually valid as a list type for empty list literal type
              let span := Span.merge lbracket.span rbracket.span
              return some (mkNodeSpan .typeList #[mkToken lbracket, mkToken rbracket] span)
          | none =>
              recordRichError "expected type or ']' after '['"
                (← current).span
                (secondary := #[(lbracket.span, "'[' is here")])
                (help := "provide a type for list elements, or use '[]' for empty list type")
              return some (mkError lbracket.span "incomplete list type" #[mkToken lbracket])

  | none => return none

/-- Parse forall type: forall a b. Type -/
partial def parseForallType : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_forall with
  | some forallTok =>
      -- Parse type variables
      let mut vars : Array SyntaxNode := #[]
      while true do
        match ← parseLowerIdent with
        | some varTok =>
            vars := vars.push (mkNodeSpan .typeVar #[mkToken varTok] varTok.span)
        | none => break

      if vars.isEmpty then
        recordRichError "expected type variables after 'forall'"
          (← current).span
          (secondary := #[(forallTok.span, "'forall' is here")])
          (notes := #["forall syntax: forall a b. Type", "forall binds type variables"])
          (help := "provide type variable names (lowercase identifiers)")

      -- Expect a dot (which is lexed as varSymbol ".")
      match ← tryConsumeDot with
      | some dotTok =>
          -- Parse the body type
          match ← parseType with
          | some body =>
              let span := Span.merge forallTok.span body.span
              let varList := mkNodeSpan .tyParamList vars (if vars.isEmpty then forallTok.span else Span.merge vars[0]!.span vars[vars.size-1]!.span)
              return some (mkNodeSpan .typeForall #[mkToken forallTok, varList, mkToken dotTok, body] span)
          | none =>
              recordRichError "expected type after 'forall ... .'"
                (← current).span
                (secondary := #[(dotTok.span, "'.' is here")])
                (notes := #["forall syntax: forall a b. Type", "the dot separates variables from the body type"])
                (help := "provide the body type after the dot")
              return some (mkError forallTok.span "incomplete forall type" #[mkToken forallTok])
      | none =>
          recordRichError "expected '.' after forall type variables"
            (← current).span
            (secondary := #[(forallTok.span, "'forall' is here")])
            (notes := #["forall syntax: forall a b. Type", "the dot separates variables from the body"])
            (help := "add '.' after the type variables")
          -- Try to parse body anyway for error recovery
          match ← parseType with
          | some body =>
              let span := Span.merge forallTok.span body.span
              let varList := mkNodeSpan .tyParamList vars (if vars.isEmpty then forallTok.span else Span.merge vars[0]!.span vars[vars.size-1]!.span)
              return some (mkNodeSpan .typeForall #[mkToken forallTok, varList, body] span)
          | none =>
              return some (mkError forallTok.span "incomplete forall type" #[mkToken forallTok])

  | none => return none

/-- Parse the forall symbol type: ∀ a b. Type -/
partial def parseForallSymbolType : ParserM (Option SyntaxNode) := do
  match ← tryConsume .forallSymbol with
  | some forallTok =>
      -- Same as parseForallType but with ∀ symbol
      let mut vars : Array SyntaxNode := #[]
      while true do
        match ← parseLowerIdent with
        | some varTok =>
            vars := vars.push (mkNodeSpan .typeVar #[mkToken varTok] varTok.span)
        | none => break

      if vars.isEmpty then
        recordRichError "expected type variables after '∀'"
          (← current).span
          (secondary := #[(forallTok.span, "'∀' is here")])
          (notes := #["∀ (Unicode forall) syntax: ∀ a b. Type"])
          (help := "provide type variable names")

      -- Expect a dot (which is lexed as varSymbol ".")
      match ← tryConsumeDot with
      | some dotTok =>
          match ← parseType with
          | some body =>
              let span := Span.merge forallTok.span body.span
              let varList := mkNodeSpan .tyParamList vars (if vars.isEmpty then forallTok.span else Span.merge vars[0]!.span vars[vars.size-1]!.span)
              return some (mkNodeSpan .typeForall #[mkToken forallTok, varList, mkToken dotTok, body] span)
          | none =>
              recordRichError "expected type after '∀ ... .'"
                (← current).span
                (secondary := #[(dotTok.span, "'.' is here")])
                (help := "provide the body type after the dot")
              return some (mkError forallTok.span "incomplete forall type" #[mkToken forallTok])
      | none =>
          recordRichError "expected '.' after ∀ type variables"
            (← current).span
            (secondary := #[(forallTok.span, "'∀' is here")])
            (help := "add '.' after the type variables")
          match ← parseType with
          | some body =>
              let span := Span.merge forallTok.span body.span
              let varList := mkNodeSpan .tyParamList vars (if vars.isEmpty then forallTok.span else Span.merge vars[0]!.span vars[vars.size-1]!.span)
              return some (mkNodeSpan .typeForall #[mkToken forallTok, varList, body] span)
          | none =>
              return some (mkError forallTok.span "incomplete forall type" #[mkToken forallTok])

  | none => return none

/--
Parse a type atom (no application or arrows).
-/
partial def parseTypeAtom : ParserM (Option SyntaxNode) := do
  -- Try forall types first (they start with keywords)
  if let some ty ← parseForallType then return some ty
  if let some ty ← parseForallSymbolType then return some ty
  -- Then structural types
  if let some ty ← parseParenType then return some ty
  if let some ty ← parseListType then return some ty
  -- Then simple types
  if let some ty ← parseTypeVar then return some ty
  if let some ty ← parseTypeCon then return some ty
  return none

/--
Parse type application: Option a, Either e a, Map k v
Type constructors are followed by zero or more type atoms.
-/
partial def parseTypeApp : ParserM (Option SyntaxNode) := do
  match ← parseTypeAtom with
  | some first =>
      let mut args := #[first]
      while true do
        -- Don't consume tokens that end type context
        let tok ← current
        if tok.kind == .arrow || tok.kind == .fatArrow ||
           tok.kind == .rightParen || tok.kind == .rightBracket ||
           tok.kind == .comma || tok.kind == .kw_with ||
           tok.kind == .kw_where || tok.kind == .pipe ||
           tok.kind == .equals || tok.kind == .layoutSep ||
           tok.kind == .layoutEnd || tok.kind == .eof then
          break
        match ← parseTypeAtom with
        | some arg => args := args.push arg
        | none => break
      if args.size == 1 then
        return some first
      else
        let span := Span.merge args[0]!.span args[args.size - 1]!.span
        return some (mkNodeSpan .typeApp args span)
  | none => return none

/--
Parse function type: a -> b -> c
Right-associative.
-/
partial def parseTypeArrow : ParserM (Option SyntaxNode) := do
  match ← parseTypeApp with
  | some left =>
      if (← check .arrow) then
        let arrowTok ← consumeAny
        match ← parseTypeArrow with  -- Right-associative
        | some right =>
            let span := Span.merge left.span right.span
            return some (mkNodeSpan .typeArrow #[left, mkToken arrowTok, right] span)
        | none =>
            recordRichError "expected type after '->'"
              (← current).span
              (secondary := #[(arrowTok.span, "'->' is here")])
              (notes := #["function type syntax: InputType -> OutputType", "arrow associates right: a -> b -> c is a -> (b -> c)"])
              (help := "provide the return type")
            return some (mkError (Span.merge left.span arrowTok.span) "incomplete arrow type" #[left, mkToken arrowTok])
      else
        return some left
  | none => return none

/-- Parse a single constraint: Show a, Functor f -/
partial def parseConstraint : ParserM (Option SyntaxNode) := do
  -- Constraint is: ClassName TypeAtom+
  match ← parseUpperIdent with
  | some classTok =>
      let className := mkNodeSpan .typeCon #[mkToken classTok] classTok.span
      let mut args := #[className]
      while true do
        -- Only parse type atoms, not full applications
        let tok ← current
        if tok.kind == .comma || tok.kind == .rightParen ||
           tok.kind == .kw_where || tok.kind == .kw_with ||
           tok.kind == .layoutSep || tok.kind == .layoutEnd then
          break
        match ← parseTypeAtom with
        | some arg => args := args.push arg
        | none => break
      let span := Span.merge classTok.span (if args.size > 1 then args[args.size-1]!.span else classTok.span)
      return some (mkNodeSpan .constraint args span)
  | none => return none

/-- Parse constraint list: (Show a, Eq a) or just Show a -/
partial def parseConstraints : ParserM (Option SyntaxNode) := do
  if (← check .leftParen) then
    let lparen ← consumeAny
    let constraints ← commaSep parseConstraint
    match ← tryConsume .rightParen with
    | some rparen =>
        let span := Span.merge lparen.span rparen.span
        return some (mkNodeSpan .constraintList (#[mkToken lparen] ++ constraints ++ #[mkToken rparen]) span)
    | none =>
        recordRichError "expected ')' after constraint list"
          (← current).span
          (secondary := #[(lparen.span, "'(' is here")])
          (notes := #["constraint list syntax: (Show a, Eq a)"])
          (help := "add ')' to close the constraint list")
        let lastSpan := if constraints.isEmpty then lparen.span else constraints[constraints.size-1]!.span
        return some (mkError (Span.merge lparen.span lastSpan) "unclosed constraint list" (#[mkToken lparen] ++ constraints))
  else
    -- Single constraint without parens
    parseConstraint

/--
Parse a full type, including 'with' constraints.
-/
partial def parseType : ParserM (Option SyntaxNode) := do
  match ← parseTypeArrow with
  | some ty =>
      if (← check .kw_with) then
        let withTok ← consumeAny
        match ← parseConstraints with
        | some constraints =>
            let span := Span.merge ty.span constraints.span
            return some (mkNodeSpan .typeConstrained #[ty, mkToken withTok, constraints] span)
        | none =>
            recordRichError "expected constraints after 'with'"
              (← current).span
              (secondary := #[(withTok.span, "'with' is here")])
              (notes := #["constrained type syntax: Type with Constraint", "constraints: (Show a, Eq a) or Show a"])
              (help := "provide a constraint or constraint list")
            return some (mkError (Span.merge ty.span withTok.span) "missing constraints" #[ty, mkToken withTok])
      else
        return some ty
  | none => return none

end  -- end mutual block

/-- Parse a type signature: :: Type -/
def parseTypeSignature : ParserM (Option SyntaxNode) := do
  match ← tryConsume .doubleColon with
  | some colonTok =>
      match ← parseType with
      | some ty =>
          let span := Span.merge colonTok.span ty.span
          return some (mkNodeSpan .signature #[mkToken colonTok, ty] span)
      | none =>
          recordRichError "expected type after '::'"
            (← current).span
            (secondary := #[(colonTok.span, "'::' is here")])
            (notes := #["type signature syntax: name :: Type"])
            (help := "provide a type")
          return some (mkError colonTok.span "missing type in signature" #[mkToken colonTok])
  | none => return none

/-- Parse an optional type signature -/
def parseOptionalSignature : ParserM (Option SyntaxNode) := do
  if (← check .doubleColon) then
    parseTypeSignature
  else
    return none

mutual

/-- Parse a kind atom: * or (kind) -/
partial def parseKindAtom : ParserM (Option SyntaxNode) := do
  let tok ← current
  -- Kind star: *
  if tok.kind == .varSymbol && tok.text == "*" then
    advance
    return some (mkNodeSpan .typeCon #[mkToken tok] tok.span)
  -- Parenthesized kind
  if tok.kind == .leftParen then
    let lparen ← consumeAny
    match ← parseKind with
    | some inner =>
        match ← tryConsume .rightParen with
        | some rparen =>
            let span := Span.merge lparen.span rparen.span
            return some (mkNodeSpan .typeParens #[mkToken lparen, inner, mkToken rparen] span)
        | none =>
            recordError "expected ')' after kind"
            return some inner
    | none =>
        recordError "expected kind after '('"
        return none
  return none

/-- Parse a kind: * -> * -> * -/
partial def parseKind : ParserM (Option SyntaxNode) := do
  match ← parseKindAtom with
  | some left =>
      if (← check .arrow) then
        let arrowTok ← consumeAny
        match ← parseKind with  -- Right-associative
        | some right =>
            let span := Span.merge left.span right.span
            return some (mkNodeSpan .typeArrow #[left, mkToken arrowTok, right] span)
        | none =>
            recordError "expected kind after '->'"
            return some left
      else
        return some left
  | none => return none

end

end Soma.Syntax.Parse
