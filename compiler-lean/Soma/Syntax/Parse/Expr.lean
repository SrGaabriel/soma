import Soma.Syntax.Parser
import Soma.Syntax.Parse.Pattern
import Soma.Syntax.Parse.Type

namespace Soma.Syntax.Parse

open ParserM

inductive Assoc where
  | left
  | right
  | none
  deriving BEq, Repr


def operatorPrecedence (op : String) : Nat × Assoc :=
  match op with
  -- Function composition (highest)
  | "." => (9, .right)
  -- Exponentiation
  | "^" => (8, .right)
  -- Multiplicative
  | "*" | "/" | "%" => (7, .left)
  -- Additive
  | "+" | "-" => (6, .left)
  -- Cons (list construction)
  | ":" => (5, .right)
  -- String/monoid append
  | "<>" | "++" => (5, .right)
  -- Comparison
  | "==" | "/=" | "!=" | "<" | ">" | "<=" | ">=" => (4, .none)
  -- Logical and
  | "&&" => (3, .right)
  -- Logical or
  | "||" => (2, .right)
  -- Monadic bind/sequence
  | ">>=" | ">>" => (1, .left)
  -- Applicative operators
  | "<*>" | "*>" | "<*" => (4, .left)
  | "<$>" | "<&>" => (4, .left)
  -- Application (lowest precedence, right associative)
  | "$" => (0, .right)
  -- Default: medium precedence, left associative
  | _ => (5, .left)

/-- Parse a variable (lower-case identifier) -/
def parseExprVar : ParserM (Option SyntaxNode) := do
  match ← parseLowerIdent with
  | some tok => return some (mkNodeSpan .exprVar #[mkToken tok] tok.span)
  | none => return none

/-- Parse a constructor (upper-case identifier) - treated as expression -/
def parseExprCon : ParserM (Option SyntaxNode) := do
  match ← parseUpperIdent with
  | some tok => return some (mkNodeSpan .exprVar #[mkToken tok] tok.span)
  | none => return none

/-- Parse a numeric literal -/
def parseExprNumber : ParserM (Option SyntaxNode) := do
  match ← tryConsume .number with
  | some tok => return some (mkNodeSpan .exprLit #[mkToken tok] tok.span)
  | none => return none

/-- Parse a string literal -/
def parseExprString : ParserM (Option SyntaxNode) := do
  let tok ← current
  match tok.kind with
  | .string _ =>
      advance
      return some (mkNodeSpan .exprLit #[mkToken tok] tok.span)
  | _ => return none

/-- Parse a boolean literal -/
def parseExprBool : ParserM (Option SyntaxNode) := do
  let tok ← current
  match tok.kind with
  | .true_ | .false_ =>
      advance
      return some (mkNodeSpan .exprLit #[mkToken tok] tok.span)
  | _ => return none

mutual

/-- Parse expressions inside parentheses: grouping or tuple -/
partial def parseParenExpr : ParserM (Option SyntaxNode) := do
  match ← tryConsume .leftParen with
  | some lparen =>
      -- Check for empty tuple ()
      if (← check .rightParen) then
        let rparen ← consumeAny
        let span := Span.merge lparen.span rparen.span
        return some (mkNodeSpan .exprTuple #[mkToken lparen, mkToken rparen] span)

      -- Check for operator section like (+) or (>>=)
      if (← check .varSymbol) then
        let opTok ← consumeAny
        if (← check .rightParen) then
          let rparen ← consumeAny
          let span := Span.merge lparen.span rparen.span
          -- This is an operator as a function: (+)
          return some (mkNodeSpan .exprVar #[mkToken lparen, mkToken opTok, mkToken rparen] span)
        else
          -- Could be a section like (+ 1) - parse the rest as expression
          match ← parseExpr with
          | some arg =>
              match ← tryConsume .rightParen with
              | some rparen =>
                  let span := Span.merge lparen.span rparen.span
                  return some (mkNodeSpan .exprSection #[mkToken lparen, mkToken opTok, arg, mkToken rparen] span)
              | none =>
                  recordRichError "expected ')' after operator section"
                    (← current).span
                    (secondary := #[(lparen.span, "operator section starts here")])
                    (notes := #["operator sections like (+) or (* 2) must be enclosed in parentheses"])
                    (help := "add ')' to close the section")
                  return some (mkError (Span.merge lparen.span arg.span) "unclosed section" #[mkToken lparen, mkToken opTok, arg])
          | none =>
              recordRichError "expected expression after operator in section"
                opTok.span
                (notes := #["sections can be left-partial like (+ 1) or right-partial like (1 +)"])
                (help := "provide an expression, e.g., '(+ 1)' or '(1 +)'")
              return some (mkError lparen.span "incomplete section" #[mkToken lparen, mkToken opTok])

      -- Parse first expression
      match ← parseExpr with
      | some first =>
          let tok ← current
          match tok.kind with
          -- Tuple: (a, b, c)
          | .comma =>
              let mut elements := #[first]
              while (← check .comma) do
                let commaTok ← consumeAny  -- consume comma
                match ← parseExpr with
                | some elem => elements := elements.push elem
                | none =>
                    recordRichError "expected expression after ','"
                      (← current).span
                      (secondary := #[(commaTok.span, "comma is here")])
                      (help := "provide an expression after the comma, e.g., '(1, 2, 3)'")
                    break
              match ← tryConsume .rightParen with
              | some rparen =>
                  let span := Span.merge lparen.span rparen.span
                  return some (mkNodeSpan .exprTuple (#[mkToken lparen] ++ elements ++ #[mkToken rparen]) span)
              | none =>
                  let curTok ← current
                  recordRichError "unclosed tuple"
                    curTok.span
                    (secondary := #[(lparen.span, "tuple starts here")])
                    (help := "add ')' to close the tuple")
                  let span := Span.merge lparen.span (elements[elements.size - 1]!.span)
                  return some (mkError span "unclosed tuple" (#[mkToken lparen] ++ elements))

          -- Section like (1 +) - expression followed by operator
          | .varSymbol =>
              let opTok ← consumeAny
              if (← check .rightParen) then
                let rparen ← consumeAny
                let span := Span.merge lparen.span rparen.span
                return some (mkNodeSpan .exprSection #[mkToken lparen, first, mkToken opTok, mkToken rparen] span)
              else
                recordRichError "expected ')' after operator in section"
                  (← current).span
                  (secondary := #[(lparen.span, "opening '(' is here")])
                  (notes := #["section syntax: (expr op) or (op expr) or (op)"])
                  (help := "add ')' to complete the operator section")
                return some (mkError lparen.span "malformed section" #[mkToken lparen, first, mkToken opTok])

          -- Parenthesized expression: (expr)
          | .rightParen =>
              let rparen ← consumeAny
              let span := Span.merge lparen.span rparen.span
              return some (mkNodeSpan .exprParens #[mkToken lparen, first, mkToken rparen] span)

          | _ =>
              recordRichError s!"unclosed parentheses"
                tok.span
                (secondary := #[(lparen.span, "opening '(' is here")])
                (notes := #[s!"found {tok.kind.userFriendly} but expected ')', ',', or an operator"])
                (help := "add ')' to close the parentheses, or add more expressions separated by ','")
              return some (mkError lparen.span "malformed parenthesized expression" #[mkToken lparen, first])

      | none =>
          recordRichError "expected expression after '('"
            lparen.span
            (notes := #["parentheses require an expression inside: (expr)"])
            (help := "provide an expression, or use '()' for unit/empty tuple")
          return some (mkError lparen.span "empty parentheses" #[mkToken lparen])

  | none => return none

/-- Parse a list literal: [1, 2, 3] -/
partial def parseListExpr : ParserM (Option SyntaxNode) := do
  match ← tryConsume .leftBracket with
  | some lbracket =>
      -- Check for empty list []
      if (← check .rightBracket) then
        let rbracket ← consumeAny
        let span := Span.merge lbracket.span rbracket.span
        return some (mkNodeSpan .exprList #[mkToken lbracket, mkToken rbracket] span)

      -- Parse comma-separated expressions
      let elements ← commaSep parseExpr
      match ← tryConsume .rightBracket with
      | some rbracket =>
          let span := Span.merge lbracket.span rbracket.span
          return some (mkNodeSpan .exprList (#[mkToken lbracket] ++ elements ++ #[mkToken rbracket]) span)
      | none =>
          let curTok ← current
          recordRichError "unclosed list"
            curTok.span
            (secondary := #[(lbracket.span, "list starts here")])
            (help := "add ']' to close the list")
          let lastSpan := if elements.isEmpty then lbracket.span else elements[elements.size - 1]!.span
          return some (mkError (Span.merge lbracket.span lastSpan) "unclosed list" (#[mkToken lbracket] ++ elements))

  | none => return none

/-- Parse a lambda: \x y -> body or λx y -> body -/
partial def parseLambda : ParserM (Option SyntaxNode) := do
  match ← tryConsume .lambda with
  | some lambdaTok =>
      -- Parse parameters (identifiers or typed patterns in parens)
      let mut params : Array SyntaxNode := #[]
      while true do
        -- Check for typed parameter: (x: Type)
        if (← check .leftParen) then
          let lparen ← consumeAny
          match ← parseLowerIdent with
          | some nameTok =>
              if (← check .colon) then
                let colonTok ← consumeAny
                match ← parseType with
                | some ty =>
                    match ← tryConsume .rightParen with
                    | some rparen =>
                        let span := Span.merge lparen.span rparen.span
                        let param := mkNodeSpan .paramList #[mkToken lparen, mkToken nameTok, mkToken colonTok, ty, mkToken rparen] span
                        params := params.push param
                    | none =>
                        recordRichError "expected ')' after typed parameter"
                          (← current).span
                          (secondary := #[(lparen.span, "parameter starts here")])
                          (help := "add ')' to close the parameter, e.g., '\\(x: Int) -> ...'")
                        params := params.push (mkError lparen.span "unclosed typed parameter" #[mkToken lparen, mkToken nameTok, mkToken colonTok, ty])
                | none =>
                    recordRichError "expected type after ':' in parameter"
                      colonTok.span
                      (secondary := #[(nameTok.span, "parameter name is here")])
                      (help := "provide a type expression, e.g., '\\(x: Int) -> ...'")
                    params := params.push (mkError lparen.span "missing parameter type" #[mkToken lparen, mkToken nameTok, mkToken colonTok])
              else
                -- Just a parenthesized identifier
                match ← tryConsume .rightParen with
                | some rparen =>
                    let span := Span.merge lparen.span rparen.span
                    params := params.push (mkNodeSpan .patVar #[mkToken lparen, mkToken nameTok, mkToken rparen] span)
                | none =>
                    recordRichError "expected ')' after parameter"
                      (← current).span
                      (secondary := #[(lparen.span, "opening '(' is here")])
                      (help := "add ')' to close the parenthesized parameter")
                    params := params.push (mkError lparen.span "unclosed parameter" #[mkToken lparen, mkToken nameTok])
          | none =>
              recordRichError "expected parameter name after '('"
                (← current).span
                (secondary := #[(lparen.span, "'(' is here")])
                (help := "provide a parameter name, e.g., '\\(x: Int) -> ...'")
              -- Skip to closing paren for recovery
              while !(← check .rightParen) && !(← atEnd) do
                advance
              if (← check .rightParen) then advance
              break
        else
          -- Simple identifier parameter
          match ← parseLowerIdent with
          | some nameTok =>
              params := params.push (mkNodeSpan .patVar #[mkToken nameTok] nameTok.span)
          | none => break

      -- Expect -> or =>
      let arrowTok ← current
      if arrowTok.kind == .arrow || arrowTok.kind == .fatArrow then
        advance
        match ← parseExpr with
        | some body =>
            let span := Span.merge lambdaTok.span body.span
            let paramList := mkNodeSpan .paramList params (if params.isEmpty then lambdaTok.span else Span.merge params[0]!.span params[params.size-1]!.span)
            return some (mkNodeSpan .exprLambda #[mkToken lambdaTok, paramList, mkToken arrowTok, body] span)
        | none =>
            recordRichError "expected expression after '->' in lambda"
              arrowTok.span
              (notes := #["lambda syntax: \\param1 param2 -> body", "the body must be an expression"])
              (help := "provide the lambda body expression")
            return some (mkError lambdaTok.span "incomplete lambda" #[mkToken lambdaTok])
      else
        recordRichError "expected '->' after lambda parameters"
          (← current).span
          (secondary := #[(lambdaTok.span, "lambda starts here")])
          (notes := #["lambda syntax: \\x y -> expr or λx y -> expr"])
          (help := "add '->' between parameters and body, e.g., '\\x -> x + 1'")
        -- Try to parse body anyway
        match ← parseExpr with
        | some body =>
            let span := Span.merge lambdaTok.span body.span
            let paramList := mkNodeSpan .paramList params (if params.isEmpty then lambdaTok.span else Span.merge params[0]!.span params[params.size-1]!.span)
            return some (mkNodeSpan .exprLambda #[mkToken lambdaTok, paramList, body] span)
        | none =>
            return some (mkError lambdaTok.span "incomplete lambda" #[mkToken lambdaTok])

  | none => return none

/-- Parse a let expression: let x = e1 in e2 -/
partial def parseLetExpr : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_let with
  | some letTok =>
      -- Parse binding name (could be a pattern but commonly just an identifier)
      match ← parseLowerIdent with
      | some nameTok =>
          -- Optional type annotation
          let typeAnnot ← if (← check .doubleColon) then
            parseTypeSignature
          else
            pure none

          -- Expect =
          match ← tryConsume .equals with
          | some eqTok =>
              match ← parseExpr with
              | some value =>
                  -- Expect 'in'
                  match ← tryConsume .kw_in with
                  | some inTok =>
                      match ← parseExpr with
                      | some body =>
                          let span := Span.merge letTok.span body.span
                          let children := #[mkToken letTok, mkToken nameTok] ++
                            (match typeAnnot with | some t => #[t] | none => #[]) ++
                            #[mkToken eqTok, value, mkToken inTok, body]
                          return some (mkNodeSpan .exprLet children span)
                      | none =>
                          recordRichError "expected expression after 'in'"
                            (← current).span
                            (secondary := #[(inTok.span, "'in' is here")])
                            (notes := #["let binding syntax: let x = value in body"])
                            (help := "provide an expression as the body, e.g., 'let x = 1 in x + 1'")
                          return some (mkError letTok.span "incomplete let" #[mkToken letTok, mkToken nameTok, mkToken eqTok, value])
                  | none =>
                      -- 'in' might be implicit with layout
                      if (← check .layoutSep) || (← check .layoutEnd) then
                        skipLayoutSep
                        match ← parseExpr with
                        | some body =>
                            let span := Span.merge letTok.span body.span
                            let children := #[mkToken letTok, mkToken nameTok] ++
                              (match typeAnnot with | some t => #[t] | none => #[]) ++
                              #[mkToken eqTok, value, body]
                            return some (mkNodeSpan .exprLet children span)
                        | none =>
                            -- Let without body is an error but we can recover
                            recordError "expected 'in' or expression after let binding"
                            let span := Span.merge letTok.span value.span
                            return some (mkNodeSpan .exprLet #[mkToken letTok, mkToken nameTok, mkToken eqTok, value] span)
                      else
                        recordRichError "expected 'in' after let binding"
                          (← current).span
                          (secondary := #[(letTok.span, "'let' starts here")])
                          (notes := #["let bindings require 'in' followed by the body expression"])
                          (help := "add 'in <expr>' after the binding, e.g., 'let x = 1 in x + 1'")
                        return some (mkError letTok.span "missing 'in'" #[mkToken letTok, mkToken nameTok, mkToken eqTok, value])
              | none =>
                  recordRichError "expected expression after '=' in let"
                    eqTok.span
                    (secondary := #[(nameTok.span, "binding name is here")])
                    (help := "provide the value expression, e.g., 'let x = 42 in ...'")
                  return some (mkError letTok.span "missing let value" #[mkToken letTok, mkToken nameTok, mkToken eqTok])
          | none =>
              recordRichError "expected '=' after let binding name"
                (← current).span
                (secondary := #[(letTok.span, "'let' is here"), (nameTok.span, "binding name is here")])
                (notes := #["let syntax: let name = expression in body"])
                (help := "add '=' between the binding name and its value")
              return some (mkError letTok.span "missing '=' in let" #[mkToken letTok, mkToken nameTok])
      | none =>
          -- Could be a destructuring pattern
          match ← parsePattern with
          | some pat =>
              match ← tryConsume .equals with
              | some eqTok =>
                  match ← parseExpr with
                  | some value =>
                      match ← tryConsume .kw_in with
                      | some inTok =>
                          match ← parseExpr with
                          | some body =>
                              let span := Span.merge letTok.span body.span
                              return some (mkNodeSpan .exprLet #[mkToken letTok, pat, mkToken eqTok, value, mkToken inTok, body] span)
                          | none =>
                              recordRichError "expected expression after 'in'"
                                (← current).span
                                (secondary := #[(inTok.span, "'in' is here")])
                                (help := "provide the body expression")
                              return some (mkError letTok.span "incomplete let" #[mkToken letTok, pat, mkToken eqTok, value])
                      | none =>
                          recordRichError "expected 'in' after let binding"
                            (← current).span
                            (secondary := #[(eqTok.span, "'=' is here")])
                            (help := "add 'in <body_expr>' after the binding value")
                          return some (mkError letTok.span "missing 'in'" #[mkToken letTok, pat, mkToken eqTok, value])
                  | none =>
                      recordRichError "expected expression after '='"
                        (← current).span
                        (secondary := #[(eqTok.span, "'=' is here")])
                        (help := "provide an expression for the let binding value")
                      return some (mkError letTok.span "missing let value" #[mkToken letTok, pat, mkToken eqTok])
              | none =>
                  recordRichError "expected '=' after pattern"
                    (← current).span
                    (secondary := #[(letTok.span, "'let' is here"), (pat.span, "pattern is here")])
                    (help := "add '=' after the pattern")
                  return some (mkError letTok.span "missing '=' in let" #[mkToken letTok, pat])
          | none =>
              recordRichError "expected binding name or pattern after 'let'"
                (← current).span
                (secondary := #[(letTok.span, "'let' is here")])
                (notes := #["let requires a name or pattern", "examples: let x = ..., let (a, b) = ..., let Some x = ..."])
                (help := "provide a binding name or pattern after 'let'")
              return some (mkError letTok.span "missing let binding" #[mkToken letTok])

  | none => return none

/-- Parse an if expression: if cond then e1 else e2 -/
partial def parseIfExpr : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_if with
  | some ifTok =>
      match ← parseExpr with
      | some cond =>
          match ← tryConsume .kw_then with
          | some thenTok =>
              match ← parseExpr with
              | some thenBranch =>
                  match ← tryConsume .kw_else with
                  | some elseTok =>
                      match ← parseExpr with
                      | some elseBranch =>
                          let span := Span.merge ifTok.span elseBranch.span
                          return some (mkNodeSpan .exprIf #[mkToken ifTok, cond, mkToken thenTok, thenBranch, mkToken elseTok, elseBranch] span)
                      | none =>
                          recordRichError "expected expression after 'else'"
                            (← current).span
                            (secondary := #[(elseTok.span, "'else' is here")])
                            (help := "provide an expression for the else branch")
                          return some (mkError ifTok.span "missing else branch" #[mkToken ifTok, cond, mkToken thenTok, thenBranch, mkToken elseTok])
                  | none =>
                      let curTok ← current
                      recordRichError "missing 'else' branch"
                        curTok.span
                        (secondary := #[(ifTok.span, "'if' expression starts here")])
                        (notes := #["'if' expressions must have both 'then' and 'else' branches"])
                        (help := "add 'else <expr>' after the 'then' branch")
                      return some (mkError ifTok.span "missing 'else'" #[mkToken ifTok, cond, mkToken thenTok, thenBranch])
              | none =>
                  recordRichError "expected expression after 'then'"
                    (← current).span
                    (secondary := #[(thenTok.span, "'then' is here")])
                    (help := "provide an expression for the then branch")
                  return some (mkError ifTok.span "missing then branch" #[mkToken ifTok, cond, mkToken thenTok])
          | none =>
              recordRichError "expected 'then' after condition"
                (← current).span
                (secondary := #[(ifTok.span, "'if' is here")])
                (notes := #["if syntax: if condition then expr1 else expr2"])
                (help := "add 'then' after the condition")
              return some (mkError ifTok.span "missing 'then'" #[mkToken ifTok, cond])
      | none =>
          recordRichError "expected condition after 'if'"
            (← current).span
            (secondary := #[(ifTok.span, "'if' is here")])
            (help := "provide a boolean condition expression")
          return some (mkError ifTok.span "missing condition" #[mkToken ifTok])

  | none => return none

/-- Parse a match arm: | pattern => body or | pattern if guard => body -/
partial def parseMatchArm : ParserM (Option SyntaxNode) := do
  match ← tryConsume .pipe with
  | some pipeTok =>
      -- Parse patterns (one or more)
      let mut patterns : Array SyntaxNode := #[]
      while true do
        match ← parsePattern with
        | some pat => patterns := patterns.push pat
        | none => break
        -- Check if more patterns or end of pattern list
        let tok ← current
        if tok.kind == .fatArrow || tok.kind == .equals || tok.kind == .kw_if then
          break

      if patterns.isEmpty then
        recordRichError "expected pattern after '|'"
          (← current).span
          (secondary := #[(pipeTok.span, "'|' is here")])
          (notes := #["match arms start with '|' followed by one or more patterns"])
          (help := "provide a pattern, e.g., '| Some x => ...', '| (a, b) => ...', '| _ => ...'")
        return some (mkError pipeTok.span "missing pattern" #[mkToken pipeTok])

      -- Optional guard: if expr
      let guard ← if (← check .kw_if) then do
        let ifTok ← consumeAny
        match ← parseExpr with
        | some guardExpr => pure (some (mkNodeSpan .matchGuard #[mkToken ifTok, guardExpr] (Span.merge ifTok.span guardExpr.span)))
        | none =>
            recordRichError "expected expression after 'if' guard"
              (← current).span
              (secondary := #[(ifTok.span, "'if' guard is here")])
              (notes := #["match guard syntax: | pattern if condition => body"])
              (help := "provide a boolean expression for the guard")
            pure none
      else
        pure none

      -- Expect => or =
      let arrowTok ← current
      if arrowTok.kind == .fatArrow || arrowTok.kind == .equals then
        advance
        -- Handle layout block for multi-line arm bodies
        let _ ← tryLayoutStart
        skipLayoutSep
        match ← parseExpr with
        | some body =>
            let _ ← tryLayoutEnd
            let span := Span.merge pipeTok.span body.span
            let children := #[mkToken pipeTok] ++ patterns ++
              (match guard with | some g => #[g] | none => #[]) ++
              #[mkToken arrowTok, body]
            return some (mkNodeSpan .matchArm children span)
        | none =>
            let _ ← tryLayoutEnd
            recordRichError "expected expression after '=>'"
              (← current).span
              (secondary := #[(arrowTok.span, "'=>' is here")])
              (notes := #["match arm syntax: | pattern => body"])
              (help := "provide an expression for the arm body")
            let lastPat := patterns[patterns.size - 1]!
            return some (mkError (Span.merge pipeTok.span lastPat.span) "missing arm body" (#[mkToken pipeTok] ++ patterns))
      else
        recordRichError "expected '=>' after pattern"
          (← current).span
          (secondary := #[(pipeTok.span, "'|' is here")])
          (notes := #["match arms use '=>' to separate patterns from bodies"])
          (help := "add '=>' after the pattern(s)")
        let lastPat := patterns[patterns.size - 1]!
        return some (mkError (Span.merge pipeTok.span lastPat.span) "missing '=>'" (#[mkToken pipeTok] ++ patterns))

  | none => return none

/-- Parse a case expression: case e1, e2 of | pat => body ... -/
partial def parseCaseExpr : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_case with
  | some caseTok =>
      -- Parse scrutinees (one or more comma-separated expressions)
      let scrutinees ← commaSep1 parseExpr
      match scrutinees with
      | some scruts =>
          -- No 'of' keyword in Soma - arms follow directly (with layout)
          skipLayoutSep
          let _ ← tryLayoutStart

          -- Parse arms
          let mut arms : Array SyntaxNode := #[]
          while true do
            skipLayoutSep
            match ← parseMatchArm with
            | some arm => arms := arms.push arm
            | none => break

          let _ ← tryLayoutEnd

          if arms.isEmpty then
            recordRichError "expected at least one match arm after 'case'"
              (← current).span
              (secondary := #[(caseTok.span, "'case' is here")])
              (notes := #["case expression syntax: case expr of | pat1 => body1 | pat2 => body2"])
              (help := "provide at least one match arm starting with '|'")

          let lastSpan := if arms.isEmpty then scruts[scruts.size - 1]!.span else arms[arms.size - 1]!.span
          let span := Span.merge caseTok.span lastSpan
          return some (mkNodeSpan .exprCase (#[mkToken caseTok] ++ scruts ++ arms) span)

      | none =>
          recordRichError "expected expression after 'case'"
            (← current).span
            (secondary := #[(caseTok.span, "'case' is here")])
            (notes := #["case syntax: case expr1, expr2 of | pattern => body"])
            (help := "provide expressions to match on")
          return some (mkError caseTok.span "missing scrutinee" #[mkToken caseTok])

  | none => return none

/-- Parse a sequence of statements in a compose/bind block. -/
partial def parseBlockStatements : ParserM (Array SyntaxNode) := do
  let mut stmts : Array SyntaxNode := #[]
  while true do
    skipLayoutSep
    -- Check if we've reached the end of the block
    if (← check .layoutEnd) || (← check .eof) then
      break
    -- Try to parse a let binding or expression
    if (← check .kw_let) then
      match ← parseLetExpr with
      | some letExpr => stmts := stmts.push letExpr
      | none => break
    else
      match ← parseExpr with
      | some expr => stmts := stmts.push expr
      | none => break
    -- After parsing a statement, we may have more
    -- Check for layout separator indicating more statements
    if !(← check .layoutSep) && !(← check .layoutEnd) && !(← check .eof) then
      break
  return stmts

/-- Parse a compose block: compose ... -/
partial def parseComposeExpr : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_compose with
  | some composeTok =>
      let _ ← tryLayoutStart
      let stmts ← parseBlockStatements
      let _ ← tryLayoutEnd

      if stmts.isEmpty then
        recordRichError "expected expression in compose block"
          (← current).span
          (secondary := #[(composeTok.span, "'compose' is here")])
          (help := "provide at least one expression in the compose block")
        return some (mkError composeTok.span "empty compose" #[mkToken composeTok])
      else
        let lastSpan := stmts[stmts.size - 1]!.span
        let span := Span.merge composeTok.span lastSpan
        return some (mkNodeSpan .exprCompose (#[mkToken composeTok] ++ stmts) span)

  | none => return none

/-- Parse a bind block: bind ... -/
partial def parseBindExpr : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_bind with
  | some bindTok =>
      let _ ← tryLayoutStart
      let stmts ← parseBlockStatements
      let _ ← tryLayoutEnd

      if stmts.isEmpty then
        recordRichError "expected expression in bind block"
          (← current).span
          (secondary := #[(bindTok.span, "'bind' is here")])
          (help := "provide at least one expression in the bind block")
        return some (mkError bindTok.span "empty bind" #[mkToken bindTok])
      else
        let lastSpan := stmts[stmts.size - 1]!.span
        let span := Span.merge bindTok.span lastSpan
        return some (mkNodeSpan .exprBind (#[mkToken bindTok] ++ stmts) span)

  | none => return none

/--
Parse an expression atom (no application or infix).
-/
partial def parseExprAtom : ParserM (Option SyntaxNode) := do
  -- Try keyword expressions first
  if let some e ← parseLambda then return some e
  if let some e ← parseLetExpr then return some e
  if let some e ← parseIfExpr then return some e
  if let some e ← parseCaseExpr then return some e
  if let some e ← parseComposeExpr then return some e
  if let some e ← parseBindExpr then return some e
  -- Then structural
  if let some e ← parseParenExpr then return some e
  if let some e ← parseListExpr then return some e
  -- Then literals
  if let some e ← parseExprNumber then return some e
  if let some e ← parseExprString then return some e
  if let some e ← parseExprBool then return some e
  -- Then identifiers
  if let some e ← parseExprVar then return some e
  if let some e ← parseExprCon then return some e
  return none

/--
Parse function application: f x y z
Left-associative: f x y = (f x) y
-/
partial def parseExprApp : ParserM (Option SyntaxNode) := do
  match ← parseExprAtom with
  | some first =>
      let mut result := first
      while true do
        -- Don't consume tokens that end application context
        let tok ← current
        if tok.kind == .varSymbol || tok.kind == .rightParen ||
           tok.kind == .rightBracket || tok.kind == .rightBrace ||
           tok.kind == .comma || tok.kind == .pipe ||
           tok.kind == .fatArrow || tok.kind == .equals ||
           tok.kind == .kw_in || tok.kind == .kw_then ||
           tok.kind == .kw_else || tok.kind == .kw_where ||
           tok.kind == .kw_with || tok.kind == .doubleColon ||
           tok.kind == .layoutSep || tok.kind == .layoutEnd ||
           tok.kind == .eof then
          break
        match ← parseExprAtom with
        | some arg =>
            let span := Span.merge result.span arg.span
            result := mkNodeSpan .exprApp #[result, arg] span
        | none => break
      return some result
  | none => return none

/--
Parse infix expression with precedence climbing (Pratt parsing).
Handles operator precedence and associativity correctly:
  - 1 + 2 * 3 parses as 1 + (2 * 3)
  - 1 - 2 - 3 parses as (1 - 2) - 3 (left associative)
  - a $ b $ c parses as a $ (b $ c) (right associative)
-/
partial def parseExprInfixWithPrec (minPrec : Nat) : ParserM (Option SyntaxNode) := do
  match ← parseExprApp with
  | some first =>
      parseExprInfixLoop first minPrec
  | none => return none

where
  /-- Main loop for precedence climbing -/
  parseExprInfixLoop (left : SyntaxNode) (minPrec : Nat) : ParserM (Option SyntaxNode) := do
    let mut result := left
    while (← check .varSymbol) do
      let opTok ← current
      let (prec, assoc) := operatorPrecedence opTok.text

      -- Only continue if this operator has high enough precedence
      if prec < minPrec then
        break

      -- Consume the operator
      advance

      -- Handle layout after operator
      skipLayoutSep

      -- Parse the right operand
      -- For right-associative operators, use same precedence
      -- For left-associative operators, use precedence + 1
      let nextMinPrec := match assoc with
        | .right => prec
        | .left => prec + 1
        | .none => prec + 1

      match ← parseExprApp with
      | some rightAtom =>
          -- Recursively handle any higher-precedence operators on the right
          match ← parseExprInfixLoop rightAtom nextMinPrec with
          | some right =>
              let span := Span.merge result.span right.span
              result := mkNodeSpan .exprInfix #[result, mkToken opTok, right] span
          | none =>
              let span := Span.merge result.span rightAtom.span
              result := mkNodeSpan .exprInfix #[result, mkToken opTok, rightAtom] span
      | none =>
          recordRichError s!"expected expression after operator '{opTok.text}'"
            (← current).span
            (secondary := #[(opTok.span, "operator is here")])
            (notes := #[s!"binary operator '{opTok.text}' requires expressions on both sides"])
            (help := "provide a right-hand side expression")
          break

    return some result

/-- Parse infix expression starting from precedence 0 -/
partial def parseExprInfix : ParserM (Option SyntaxNode) := do
  parseExprInfixWithPrec 0

/--
Parse a full expression.
-/
partial def parseExpr : ParserM (Option SyntaxNode) := do
  match ← parseExprInfix with
  | some expr =>
      -- Check for type annotation: expr :: Type
      if (← check .doubleColon) then
        let colonTok ← consumeAny
        match ← parseType with
        | some ty =>
            let span := Span.merge expr.span ty.span
            return some (mkNodeSpan .exprTypeAnnot #[expr, mkToken colonTok, ty] span)
        | none =>
            recordRichError "expected type after '::'"
              (← current).span
              (secondary := #[(colonTok.span, "'::' is here")])
              (notes := #["type annotation syntax: expr :: Type"])
              (help := "provide a type expression")
            return some (mkError (Span.merge expr.span colonTok.span) "missing type annotation" #[expr, mkToken colonTok])
      else
        return some expr
  | none => return none

end  -- end mutual block

end Soma.Syntax.Parse
