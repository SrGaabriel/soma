import Soma.Syntax.Parser
import Soma.Syntax.Parse.Pattern
import Soma.Syntax.Parse.Type

namespace Soma.Syntax.Parse

open ParserM

inductive Assoc where | left | right | none deriving BEq, Repr

def operatorPrecedence (op : String) : Nat × Assoc :=
  match op with
  | "." => (9, .right)
  | "^" => (8, .right)
  | "*" | "/" | "%" => (7, .left)
  | "+" | "-" => (6, .left)
  | ":" => (5, .right)
  | "<>" | "++" => (5, .right)
  | "=" => (4, .none)
  | "==" | "/=" | "!=" | "<" | ">" | "<=" | ">=" => (4, .none)
  | "&&" => (3, .right)
  | "||" => (2, .right)
  | ">>=" | ">>" => (1, .left)
  | "<*>" | "*>" | "<*" => (4, .left)
  | "<$>" | "<&>" => (4, .left)
  | "$" => (0, .right)
  | _ => (5, .left)

private def parseIdentAny : ParserM (Option GreenNode) := do
  let tok ← current
  match tok.kind with
  | some .lowerIdent | some .upperIdent => some <$> consumeAny
  | _ => return none

/-- Parse an expression name reference, including qualified forms with `::` -/
def parseExprVar : ParserM (Option GreenNode) := do
  match ← parseIdentAny with
  | none => return none
  | some first =>
      let mut parts : Array GreenNode := #[first]
      while (← check .doubleColon) do
        let sep ← consumeAny
        match ← parseIdentAny with
        | some next =>
            parts := parts.push sep
            parts := parts.push next
        | none =>
            recordError "expected identifier after '::'"
            return some (GreenNode.mkError "incomplete qualified name" (parts.push sep))
      return some (GreenNode.mkNode .exprVar parts)

def parseExprNumber : ParserM (Option GreenNode) := do
  match ← tryConsume .number with
  | some tok => return some (GreenNode.mkNode .exprLit #[tok])
  | none => return none

def parseExprString : ParserM (Option GreenNode) := do
  let tok ← current
  match tok.kind with
  | some (.string _) =>
      let g ← consumeAny
      return some (GreenNode.mkNode .exprLit #[g])
  | _ => return none

def parseExprBool : ParserM (Option GreenNode) := do
  let tok ← current
  match tok.kind with
  | some .true_ | some .false_ =>
      let g ← consumeAny
      return some (GreenNode.mkNode .exprLit #[g])
  | _ => return none

mutual

partial def parseParenExpr : ParserM (Option GreenNode) := do
  match ← tryConsume .leftParen with
  | some lparen =>
      if (← check .rightParen) then
        let rparen ← consumeAny
        return some (GreenNode.mkNode .exprTuple #[lparen, rparen])

      if (← check .varSymbol) then
        let opTok ← consumeAny
        if (← check .rightParen) then
          let rparen ← consumeAny
          return some (GreenNode.mkNode .exprVar #[lparen, opTok, rparen])
        else
          match ← parseExpr with
          | some arg =>
              match ← tryConsume .rightParen with
              | some rparen =>
                  return some (GreenNode.mkNode .exprSection #[lparen, opTok, arg, rparen])
              | none =>
                  recordError "expected ')' after operator section"
                  return some (GreenNode.mkError "unclosed section" #[lparen, opTok, arg])
          | none =>
              recordError "expected expression after operator in section"
              return some (GreenNode.mkError "incomplete section" #[lparen, opTok])

      match ← parseExpr with
      | some first =>
          if (← check .comma) then
            let mut elements := #[first]
            while (← check .comma) do
              let comma ← consumeAny
              elements := elements.push comma
              match ← parseExpr with
              | some elem => elements := elements.push elem
              | none => recordError "expected expression after ','"; break
            match ← tryConsume .rightParen with
            | some rparen =>
                return some (GreenNode.mkNode .exprTuple (#[lparen] ++ elements ++ #[rparen]))
            | none =>
                recordError "unclosed tuple"
                return some (GreenNode.mkError "unclosed tuple" (#[lparen] ++ elements))
          else if (← check .varSymbol) then
            let opTok ← consumeAny
            if (← check .rightParen) then
              let rparen ← consumeAny
              return some (GreenNode.mkNode .exprSection #[lparen, first, opTok, rparen])
            else
              recordError "expected ')' after operator in section"
              return some (GreenNode.mkError "malformed section" #[lparen, first, opTok])
          else
            match ← tryConsume .rightParen with
            | some rparen =>
                return some (GreenNode.mkNode .exprParens #[lparen, first, rparen])
            | none =>
                recordError "unclosed parentheses"
                return some (GreenNode.mkError "malformed parenthesized expression" #[lparen, first])
      | none =>
          recordError "expected expression after '('"
          return some (GreenNode.mkError "empty parentheses" #[lparen])
  | none => return none

partial def parseListExpr : ParserM (Option GreenNode) := do
  match ← tryConsume .leftBracket with
  | some lbracket =>
      if (← check .rightBracket) then
        let rbracket ← consumeAny
        return some (GreenNode.mkNode .exprList #[lbracket, rbracket])

      let elements ← commaSep parseExpr
      match ← tryConsume .rightBracket with
      | some rbracket =>
          return some (GreenNode.mkNode .exprList (#[lbracket] ++ elements ++ #[rbracket]))
      | none =>
          recordError "unclosed list"
          return some (GreenNode.mkError "unclosed list" (#[lbracket] ++ elements))
  | none => return none

/-- Parse a record field -/
partial def parseRecordField : ParserM (Option GreenNode) := do
  match ← parseLowerIdent with
  | some nameTok =>
      match ← tryConsume .colonEquals with
      | some eqTok =>
          match ← parseExpr with
          | some valExpr =>
              return some (GreenNode.mkNode .recordField #[nameTok, eqTok, valExpr])
          | none =>
              recordError "expected expression after ':=' in record field"
              return some (GreenNode.mkError "missing field value" #[nameTok, eqTok])
      | none =>
          -- Punning: { x } means { x := x }
          return some (GreenNode.mkNode .recordField #[nameTok])
  | none => return none

/-- Parse a record literal: { x = 1, y = 2 } or record update: { r | x = 3 } -/
partial def parseRecordExpr : ParserM (Option GreenNode) := do
  match ← tryConsume .leftBrace with
  | some lbrace =>
      -- Check for empty record
      if (← check .rightBrace) then
        let rbrace ← consumeAny
        return some (GreenNode.mkNode .exprRecord #[lbrace, rbrace])

      -- First, check if it's lowerIdent followed by = (field) or | (base for update)
      let tok ← current
      match tok.kind with
      | some .lowerIdent =>
          let nameTok ← consumeAny
          let nextTok ← current
          match nextTok.kind with
          | some .colonEquals =>
              let eqTok ← consumeAny
              match ← parseExpr with
              | some valExpr =>
                  let firstField := GreenNode.mkNode .recordField #[nameTok, eqTok, valExpr]
                  -- Parse remaining fields
                  let mut fields := #[firstField]
                  while (← check .comma) do
                    let comma ← consumeAny
                    fields := fields.push comma
                    match ← parseRecordField with
                    | some field => fields := fields.push field
                    | none => recordError "expected field after ','"; break
                  match ← tryConsume .rightBrace with
                  | some rbrace =>
                      return some (GreenNode.mkNode .exprRecord (#[lbrace] ++ fields ++ #[rbrace]))
                  | none =>
                      recordError "unclosed record"
                      return some (GreenNode.mkError "unclosed record" (#[lbrace] ++ fields))
              | none =>
                  recordError "expected expression after ':=' in record field"
                  return some (GreenNode.mkError "missing field value" #[lbrace, nameTok, eqTok])
          | some .pipe =>
              -- It's a record update: { base | field = val }
              let baseExpr := GreenNode.mkNode .exprVar #[nameTok]
              let pipeTok ← consumeAny
              let mut fields : Array GreenNode := #[]
              match ← parseRecordField with
              | some field => fields := fields.push field
              | none => recordError "expected field after '|' in record update"
              while (← check .comma) do
                let comma ← consumeAny
                fields := fields.push comma
                match ← parseRecordField with
                | some field => fields := fields.push field
                | none => recordError "expected field after ','"; break
              match ← tryConsume .rightBrace with
              | some rbrace =>
                  return some (GreenNode.mkNode .exprRecordUpdate (#[lbrace, baseExpr, pipeTok] ++ fields ++ #[rbrace]))
              | none =>
                  recordError "unclosed record update"
                  return some (GreenNode.mkError "unclosed record update" (#[lbrace, baseExpr, pipeTok] ++ fields))
          | some .comma =>
              -- Punning: { x, y } means { x = x, y = y }
              let firstField := GreenNode.mkNode .recordField #[nameTok]
              let mut fields := #[firstField]
              while (← check .comma) do
                let comma ← consumeAny
                fields := fields.push comma
                match ← parseRecordField with
                | some field => fields := fields.push field
                | none => recordError "expected field after ','"; break
              match ← tryConsume .rightBrace with
              | some rbrace =>
                  return some (GreenNode.mkNode .exprRecord (#[lbrace] ++ fields ++ #[rbrace]))
              | none =>
                  recordError "unclosed record"
                  return some (GreenNode.mkError "unclosed record" (#[lbrace] ++ fields))
          | some .rightBrace =>
              -- Single punned field: { x }
              let firstField := GreenNode.mkNode .recordField #[nameTok]
              let rbrace ← consumeAny
              return some (GreenNode.mkNode .exprRecord #[lbrace, firstField, rbrace])
          | _ =>
              recordError "expected '=', '|', ',' or '}' after field name in record"
              return some (GreenNode.mkError "malformed record" #[lbrace, nameTok])
      | _ =>
          match ← parseExpr with
          | some baseExpr =>
              match ← tryConsume .pipe with
              | some pipeTok =>
                  let mut fields : Array GreenNode := #[]
                  match ← parseRecordField with
                  | some field => fields := fields.push field
                  | none => recordError "expected field after '|' in record update"
                  while (← check .comma) do
                    let comma ← consumeAny
                    fields := fields.push comma
                    match ← parseRecordField with
                    | some field => fields := fields.push field
                    | none => recordError "expected field after ','"; break
                  match ← tryConsume .rightBrace with
                  | some rbrace =>
                      return some (GreenNode.mkNode .exprRecordUpdate (#[lbrace, baseExpr, pipeTok] ++ fields ++ #[rbrace]))
                  | none =>
                      recordError "unclosed record update"
                      return some (GreenNode.mkError "unclosed record update" (#[lbrace, baseExpr, pipeTok] ++ fields))
              | none =>
                  recordError "expected '|' after base expression in record update"
                  return some (GreenNode.mkError "malformed record update" #[lbrace, baseExpr])
          | none =>
              recordError "expected field or expression in record"
              return some (GreenNode.mkError "empty record" #[lbrace])
  | none => return none

partial def parseLambda : ParserM (Option GreenNode) := do
  match ← tryConsume .lambda with
  | some lambdaTok =>
      let mut params : Array GreenNode := #[]
      while true do
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
                        params := params.push (GreenNode.mkNode .paramList #[lparen, nameTok, colonTok, ty, rparen])
                    | none =>
                        recordError "expected ')' after typed parameter"
                        params := params.push (GreenNode.mkError "unclosed typed parameter" #[lparen, nameTok, colonTok, ty])
                | none =>
                    recordError "expected type after ':' in parameter"
                    params := params.push (GreenNode.mkError "missing parameter type" #[lparen, nameTok, colonTok])
              else
                match ← tryConsume .rightParen with
                | some rparen =>
                    params := params.push (GreenNode.mkNode .patVar #[lparen, nameTok, rparen])
                | none =>
                    recordError "expected ')' after parameter"
                    params := params.push (GreenNode.mkError "unclosed parameter" #[lparen, nameTok])
          | none =>
              recordError "expected parameter name after '('"
              while !(← check .rightParen) && !(← atEnd) do advance
              if (← check .rightParen) then advance
              break
        else
          match ← parseLowerIdent with
          | some nameTok => params := params.push (GreenNode.mkNode .patVar #[nameTok])
          | none => break

      let tok ← current
      if tok.kind == some .arrow || tok.kind == some .fatArrow then
        let arrowTok ← consumeAny
        match ← parseExpr with
        | some body =>
            let paramList := GreenNode.mkNode .paramList params
            return some (GreenNode.mkNode .exprLambda #[lambdaTok, paramList, arrowTok, body])
        | none =>
            recordError "expected expression after '->' in lambda"
            return some (GreenNode.mkError "incomplete lambda" #[lambdaTok])
      else
        recordError "expected '->' after lambda parameters"
        match ← parseExpr with
        | some body =>
            let paramList := GreenNode.mkNode .paramList params
            return some (GreenNode.mkNode .exprLambda #[lambdaTok, paramList, body])
        | none =>
            return some (GreenNode.mkError "incomplete lambda" #[lambdaTok])
  | none => return none

partial def parseLetExpr : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_let with
  | some letTok =>
      match ← parseLowerIdent with
      | some nameTok =>
          let typeAnnot ← if (← check .doubleColon) then parseTypeSignature else pure none
          match ← tryConsume .colonEquals with
          | some eqTok =>
              match ← parseExpr with
              | some value =>
                  match ← tryConsume .kw_in with
                  | some inTok =>
                      let _ ← tryLayoutSep
                      match ← parseExpr with
                      | some body =>
                          let children := #[letTok, nameTok] ++
                            (match typeAnnot with | some t => #[t] | none => #[]) ++
                            #[eqTok, value, inTok, body]
                          return some (GreenNode.mkNode .exprLet children)
                      | none =>
                          recordError "expected expression after 'in'"
                          return some (GreenNode.mkError "incomplete let" #[letTok, nameTok, eqTok, value])
                  | none =>
                      if (← check .layoutSep) || (← check .layoutEnd) then
                        let _ ← tryLayoutSep
                        match ← parseExpr with
                        | some body =>
                            let children := #[letTok, nameTok] ++
                              (match typeAnnot with | some t => #[t] | none => #[]) ++
                              #[eqTok, value, body]
                            return some (GreenNode.mkNode .exprLet children)
                        | none =>
                            recordError "expected 'in' or expression after let binding"
                            let children := #[letTok, nameTok] ++
                              (match typeAnnot with | some t => #[t] | none => #[]) ++
                              #[eqTok, value]
                            return some (GreenNode.mkNode .exprLet children)
                      else
                        recordError "expected 'in' after let binding"
                        return some (GreenNode.mkError "missing 'in'" #[letTok, nameTok, eqTok, value])
              | none =>
                  recordError "expected expression after ':=' in let"
                  return some (GreenNode.mkError "missing let value" #[letTok, nameTok, eqTok])
          | none =>
              recordError "expected ':=' after let binding name"
              return some (GreenNode.mkError "missing ':=' in let" #[letTok, nameTok])
      | none =>
          match ← parsePattern with
          | some pat =>
              match ← tryConsume .colonEquals with
              | some eqTok =>
                  match ← parseExpr with
                  | some value =>
                      match ← tryConsume .kw_in with
                      | some inTok =>
                          let _ ← tryLayoutSep
                          match ← parseExpr with
                          | some body =>
                              return some (GreenNode.mkNode .exprLet #[letTok, pat, eqTok, value, inTok, body])
                          | none =>
                              recordError "expected expression after 'in'"
                              return some (GreenNode.mkError "incomplete let" #[letTok, pat, eqTok, value])
                      | none =>
                          if (← check .layoutSep) || (← check .layoutEnd) then
                            let _ ← tryLayoutSep
                            match ← parseExpr with
                            | some body =>
                                return some (GreenNode.mkNode .exprLet #[letTok, pat, eqTok, value, body])
                            | none =>
                                recordError "expected 'in' or expression after let binding"
                                return some (GreenNode.mkNode .exprLet #[letTok, pat, eqTok, value])
                          else
                            recordError "expected 'in' after let binding"
                            return some (GreenNode.mkError "missing 'in'" #[letTok, pat, eqTok, value])
                  | none =>
                      recordError "expected expression after ':='"
                      return some (GreenNode.mkError "missing let value" #[letTok, pat, eqTok])
              | none =>
                  recordError "expected ':=' after pattern"
                  return some (GreenNode.mkError "missing ':=' in let" #[letTok, pat])
          | none =>
              recordError "expected binding name or pattern after 'let'"
              return some (GreenNode.mkError "missing let binding" #[letTok])
  | none => return none

partial def parseIfExpr : ParserM (Option GreenNode) := do
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
                          return some (GreenNode.mkNode .exprIf #[ifTok, cond, thenTok, thenBranch, elseTok, elseBranch])
                      | none =>
                          recordError "expected expression after 'else'"
                          return some (GreenNode.mkError "missing else branch" #[ifTok, cond, thenTok, thenBranch, elseTok])
                  | none =>
                      recordError "missing 'else' branch"
                      return some (GreenNode.mkError "missing 'else'" #[ifTok, cond, thenTok, thenBranch])
              | none =>
                  recordError "expected expression after 'then'"
                  return some (GreenNode.mkError "missing then branch" #[ifTok, cond, thenTok])
          | none =>
              recordError "expected 'then' after condition"
              return some (GreenNode.mkError "missing 'then'" #[ifTok, cond])
      | none =>
          recordError "expected condition after 'if'"
          return some (GreenNode.mkError "missing condition" #[ifTok])
  | none => return none

partial def parseMatchArm : ParserM (Option GreenNode) := do
  match ← tryConsume .pipe with
  | some pipeTok =>
      let mut patternsWithDelims : Array GreenNode := #[]
      let mut patternCount := 0

      match ← parsePattern with
      | some pat =>
          patternsWithDelims := patternsWithDelims.push pat
          patternCount := patternCount + 1
      | none =>
          recordError "expected pattern after '|'"
          return some (GreenNode.mkError "missing pattern" #[pipeTok])

      while true do
        let tok ← current
        if tok.kind == some .fatArrow || tok.kind == some .kw_if then
          break
        if tok.kind == some .comma then
          let commaTok ← consumeAny
          patternsWithDelims := patternsWithDelims.push commaTok
          match ← parsePattern with
          | some pat =>
              patternsWithDelims := patternsWithDelims.push pat
              patternCount := patternCount + 1
          | none =>
              recordError "expected pattern after ','"
              return some (GreenNode.mkError "missing pattern after ','" (#[pipeTok] ++ patternsWithDelims))
        else
          recordError "expected ',' between multiple patterns"
          return some (GreenNode.mkError "missing ',' between patterns" (#[pipeTok] ++ patternsWithDelims))

      if patternCount == 0 then
        recordError "expected pattern after '|'"
        return some (GreenNode.mkError "missing pattern" #[pipeTok])

      let guard ← if (← check .kw_if) then do
        let ifTok ← consumeAny
        match ← parseExpr with
        | some guardExpr => pure (some (GreenNode.mkNode .matchGuard #[ifTok, guardExpr]))
        | none => recordError "expected expression after 'if' guard"; pure none
      else pure none

      let tok ← current
      if tok.kind == some .fatArrow then
        let arrowTok ← consumeAny
        match ← inLayout parseExpr with
        | some body =>
            let children := #[pipeTok] ++ patternsWithDelims ++
              (match guard with | some g => #[g] | none => #[]) ++
              #[arrowTok, body]
            return some (GreenNode.mkNode .matchArm children)
        | none =>
            recordError "expected expression after '=>'"
            return some (GreenNode.mkError "missing arm body" (#[pipeTok] ++ patternsWithDelims))
      else
        recordError "expected '=>' after pattern"
        return some (GreenNode.mkError "missing '=>'" (#[pipeTok] ++ patternsWithDelims))
  | none => return none

partial def parseCaseExpr : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_case with
  | some caseTok =>
      let scrutinees ← commaSep1 parseExpr
      match scrutinees with
      | some scruts =>
          let arms ← layoutSepBy parseMatchArm
          return some (GreenNode.mkNode .exprCase (#[caseTok] ++ scruts ++ arms))
      | none =>
          recordError "expected expression after 'case'"
          return some (GreenNode.mkError "missing scrutinee" #[caseTok])
  | none => return none

partial def parseComposeLetStmt : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_let with
  | some letTok =>
      match ← parseLowerIdent with
      | some nameTok =>
          match ← tryConsume .colonEquals with
          | some eqTok =>
              match ← parseExpr with
              | some value =>
                  return some (GreenNode.mkNode .composeLetStmt #[letTok, nameTok, eqTok, value])
              | none =>
                  recordError "expected expression after ':=' in let"
                  return some (GreenNode.mkError "missing let value" #[letTok, nameTok, eqTok])
          | none =>
              recordError "expected ':=' after let binding name"
              return some (GreenNode.mkError "missing ':=' in let" #[letTok, nameTok])
      | none =>
          match ← parsePattern with
          | some pat =>
              match ← tryConsume .colonEquals with
              | some eqTok =>
                  match ← parseExpr with
                  | some value =>
                      return some (GreenNode.mkNode .composeLetStmt #[letTok, pat, eqTok, value])
                  | none =>
                      recordError "expected expression after ':=' in let"
                      return some (GreenNode.mkError "missing let value" #[letTok, pat, eqTok])
              | none =>
                  recordError "expected ':=' after let pattern"
                  return some (GreenNode.mkError "missing ':=' in let" #[letTok, pat])
          | none =>
              recordError "expected binding name or pattern after 'let'"
              return some (GreenNode.mkError "missing let binding" #[letTok])
  | none => return none

partial def parseComposeBindStmt : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_bind with
  | some bindTok =>
      match ← parseLowerIdent with
      | some nameTok =>
          match ← tryConsume .leftArrow with
          | some arrowTok =>
              match ← parseExpr with
              | some value =>
                  return some (GreenNode.mkNode .composeBindStmt #[bindTok, nameTok, arrowTok, value])
              | none =>
                  recordError "expected expression after '<-' in bind"
                  return some (GreenNode.mkError "missing bind value" #[bindTok, nameTok, arrowTok])
          | none =>
              recordError "expected '<-' after bind variable name"
              return some (GreenNode.mkError "missing '<-' in bind" #[bindTok, nameTok])
      | none =>
          recordError "expected variable name after 'bind'"
          return some (GreenNode.mkError "missing bind variable" #[bindTok])
  | none => return none

partial def parseBlockStatement : ParserM (Option GreenNode) := do
  if (← check .kw_let) then
    parseComposeLetStmt
  else if (← check .kw_bind) then
    parseComposeBindStmt
  else
    parseExpr

partial def parseBlockStatements : ParserM (Array GreenNode) := do
  layoutSepBy parseBlockStatement

partial def parseComposeExpr : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_compose with
  | some composeTok =>
      let stmts ← parseBlockStatements

      if stmts.isEmpty then
        recordError "expected expression in compose block"
        return some (GreenNode.mkError "empty compose" #[composeTok])
      else
        return some (GreenNode.mkNode .exprCompose (#[composeTok] ++ stmts))
  | none => return none

partial def parseProjection : ParserM (Option GreenNode) := do
  -- Check for Type.field projection syntax
  let tok ← current
  if tok.kind != some .upperIdent then return none
  let nextTok ← peekNext
  if nextTok.kind != some .dot then return none
  let fieldTok ← peekAhead 2
  if fieldTok.kind != some .lowerIdent then return none
  -- Parse Type.field as a projection
  let typeTok ← consumeAny
  let dotTok ← consumeAny
  let fieldTok ← consumeAny
  return some (GreenNode.mkNode .exprProjection #[typeTok, dotTok, fieldTok])

/-- Parse a variant injection: .Label or .Label arg -/
partial def parseVariantExpr : ParserM (Option GreenNode) := do
  -- Check for .identifier pattern (variant injection)
  let tok ← current
  if tok.kind != some .dot then return none
  let nextTok ← peekNext
  -- Accept both upper and lower case identifiers for variant labels
  if nextTok.kind != some .lowerIdent && nextTok.kind != some .upperIdent then return none
  -- Parse .label
  let dotTok ← consumeAny
  let labelTok ← consumeAny
  -- Optionally parse an argument (but don't consume operators, delimiters, etc.)
  let argTok ← current
  if argTok.kind == some .varSymbol || argTok.kind == some .equals ||
     argTok.kind == some .rightParen || argTok.kind == some .rightBracket ||
     argTok.kind == some .rightBrace || argTok.kind == some .comma ||
     argTok.kind == some .pipe || argTok.kind == some .fatArrow ||
     argTok.kind == some .kw_in || argTok.kind == some .kw_then ||
     argTok.kind == some .kw_else || argTok.kind == some .kw_where ||
     argTok.kind == some .doubleColon ||
     argTok.kind == some .layoutStart || argTok.kind == some .layoutSep ||
     argTok.kind == some .layoutEnd || argTok.kind == some .eof then
    -- No argument, just .label
    return some (GreenNode.mkNode .exprVariant #[dotTok, labelTok])
  else
    -- Try to parse an argument atom
    match ← parseExprAtom with
    | some arg =>
        return some (GreenNode.mkNode .exprVariant #[dotTok, labelTok, arg])
    | none =>
        -- No argument parsed, just .label
        return some (GreenNode.mkNode .exprVariant #[dotTok, labelTok])

partial def parseExprTypeApp : ParserM (Option GreenNode) := do
  match ← tryConsume .at with
  | some atTok =>
    let tok ← current
    match tok.kind with
    | some .lowerIdent =>
      -- @label - label application
      let labelTok ← consumeAny
      return some (GreenNode.mkNode .exprTypeApp #[atTok, labelTok])
    | some .upperIdent =>
      -- @Type - type constructor application
      match ← parseTypeAtom with
      | some typeTok =>
        return some (GreenNode.mkNode .exprTypeApp #[atTok, typeTok])
      | none =>
        recordError "expected type after '@'"
        return some (GreenNode.mkError "incomplete type application" #[atTok])
    | some .leftParen =>
      -- @(Type) - parenthesized type application
      match ← parseTypeAtom with
      | some typeTok =>
        return some (GreenNode.mkNode .exprTypeApp #[atTok, typeTok])
      | none =>
        recordError "expected type after '@'"
        return some (GreenNode.mkError "incomplete type application" #[atTok])
    | _ =>
      recordError "expected type or label after '@'"
      return some (GreenNode.mkError "incomplete type application" #[atTok])
  | none => return none

partial def parseExprAtom : ParserM (Option GreenNode) := do
  if let some e ← parseLambda then return some e
  if let some e ← parseLetExpr then return some e
  if let some e ← parseIfExpr then return some e
  if let some e ← parseCaseExpr then return some e
  if let some e ← parseComposeExpr then return some e
  if let some e ← parseParenExpr then return some e
  if let some e ← parseListExpr then return some e
  if let some e ← parseRecordExpr then return some e
  if let some e ← parseExprNumber then return some e
  if let some e ← parseExprString then return some e
  if let some e ← parseExprBool then return some e
  if let some e ← parseExprTypeApp then return some e
  if let some e ← parseVariantExpr then return some e
  if let some e ← parseProjection then return some e
  if let some e ← parseExprVar then return some e
  return none

partial def parseExprApp : ParserM (Option GreenNode) := do
  match ← parseExprAtom with
  | some first =>
      let mut result := first
      while true do
        let tok ← current
        -- Check for field access: expr.field
        if tok.kind == some .dot then
          let dotTok ← consumeAny
          -- After dot, expect a lower-case identifier (field name)
          match ← parseLowerIdent with
          | some fieldTok =>
              result := GreenNode.mkNode .exprFieldAccess #[result, dotTok, fieldTok]
          | none =>
              recordError "expected field name after '.'"
              break
        else if tok.kind == some .varSymbol || tok.kind == some .rightParen ||
           tok.kind == some .rightBracket || tok.kind == some .rightBrace ||
           tok.kind == some .comma || tok.kind == some .pipe ||
           tok.kind == some .fatArrow || tok.kind == some .equals ||
           tok.kind == some .kw_in || tok.kind == some .kw_then ||
           tok.kind == some .kw_else || tok.kind == some .kw_where ||
           tok.kind == some .doubleColon ||
           tok.kind == some .layoutStart || tok.kind == some .layoutSep ||
           tok.kind == some .layoutEnd || tok.kind == some .eof then
          break
        else
          match ← parseExprAtom with
          | some arg =>
              result := GreenNode.mkNode .exprApp #[result, arg]
          | none => break
      return some result
  | none => return none

partial def parseExprInfixWithPrec (minPrec : Nat) : ParserM (Option GreenNode) := do
  match ← parseExprApp with
  | some first => parseExprInfixLoop first minPrec
  | none => return none

where
  parseExprInfixLoop (left : GreenNode) (minPrec : Nat) : ParserM (Option GreenNode) := do
    let mut result := left
    while (← check .varSymbol) || (← check .equals) do
      let tok ← current
      let opText := if tok.kind == some .equals then "=" else tok.text
      let (prec, assoc) := operatorPrecedence opText

      if prec < minPrec then break

      let opTok ← consumeAny

      let nextMinPrec := match assoc with
        | .right => prec
        | .left => prec + 1
        | .none => prec + 1

      match ← parseExprApp with
      | some rightAtom =>
          match ← parseExprInfixLoop rightAtom nextMinPrec with
          | some right =>
              result := GreenNode.mkNode .exprInfix #[result, opTok, right]
          | none =>
              result := GreenNode.mkNode .exprInfix #[result, opTok, rightAtom]
      | none =>
          recordError s!"expected expression after operator '{opText}'"
          break

    return some result

partial def parseExprInfix : ParserM (Option GreenNode) := parseExprInfixWithPrec 0

partial def parseExpr : ParserM (Option GreenNode) := do
  match ← parseExprInfix with
  | some expr =>
      if (← check .doubleColon) then
        let colonTok ← consumeAny
        match ← parseType with
        | some ty =>
            return some (GreenNode.mkNode .exprTypeAnnot #[expr, colonTok, ty])
        | none =>
            recordError "expected type after '::'"
            return some (GreenNode.mkError "missing type annotation" #[expr, colonTok])
      else
        return some expr
  | none => return none

end

end Soma.Syntax.Parse
