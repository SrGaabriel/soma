import Soma.Syntax.Parser
import Soma.Syntax.Parse.Pattern

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

/-- Parse a qualified expression name `foo` or `Foo::bar` -/
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

def checkDot : ParserM Bool := do
  let tok ← current
  return tok.kind == some .varSymbol && tok.text == "."

def tryConsumeDot : ParserM (Option GreenNode) := do
  if (← checkDot) then return some (← consumeAny) else return none

/-- Check if current token is a quantity annotation -/
def checkQuantity : ParserM Bool := do
  let tok ← current
  if tok.kind == some .omega then return true
  if tok.kind == some .number then
    return tok.text == "0" || tok.text == "1"
  return false

/-- Parse a quantity annotation -/
def parseQuantity : ParserM (Option GreenNode) := do
  let tok ← current
  if tok.kind == some .omega then
    let g ← consumeAny
    return some (GreenNode.mkNode .typeQuantity #[g])
  if tok.kind == some .number then
    if tok.text == "0" || tok.text == "1" then
      let g ← consumeAny
      return some (GreenNode.mkNode .typeQuantity #[g])
  return none

mutual

/-- Lookahead -/
partial def checkDoubleBrace : ParserM Bool := do
  let tok ← current
  if tok.kind == some .leftBrace then
    let next ← peekNext
    return next.kind == some .leftBrace
  return false

/-- A single forall binder `a`, `(a : Kind)`, or `{{Constraint}}` -/
partial def parseForallBinder : ParserM (Option GreenNode) := do
  if (← checkDoubleBrace) then
    return ← parseDictBinder
  if (← check .leftParen) then
    let lparen ← consumeAny
    match ← parseLowerIdent with
    | some varTok =>
        let colonTok? ← do
          match ← tryConsume .colon with
          | some tok => pure (some tok)
          | none => tryConsume .doubleColon
        match colonTok? with
        | some colonTok =>
            match ← parseExpr with
            | some kind =>
                match ← tryConsume .rightParen with
                | some rparen =>
                    let varNode := GreenNode.mkNode .typeVar #[varTok]
                    return some (GreenNode.mkNode .tyParamKinded #[lparen, varNode, colonTok, kind, rparen])
                | none =>
                    recordError "expected ')' after kinded type parameter"
                    let varNode := GreenNode.mkNode .typeVar #[varTok]
                    return some (GreenNode.mkNode .tyParamKinded #[lparen, varNode, colonTok, kind])
            | none =>
                recordError "expected type after ':' in type parameter"
                let varNode := GreenNode.mkNode .typeVar #[varTok]
                return some (GreenNode.mkError "missing type" #[lparen, varNode, colonTok])
        | none =>
            recordError "expected ':' in kinded type parameter"
            return some (GreenNode.mkError "missing ':'" #[lparen, varTok])
    | none =>
        recordError "expected type variable name after '(' in forall"
        return some (GreenNode.mkError "missing var name" #[lparen])
  else
    match ← parseLowerIdent with
    | some varTok => return some (GreenNode.mkNode .typeVar #[varTok])
    | none => return none

/-- Parse a `{{...}}` constraint binder (named or anonymous) -/
partial def parseDictBinder : ParserM (Option GreenNode) := do
  if !(← checkDoubleBrace) then return none
  let lbrace1 ← consumeAny
  let lbrace2 ← consumeAny
  let tok ← current
  let next ← peekNext
  if tok.kind == some .lowerIdent && next.kind == some .colon then
    let nameTok ← consumeAny
    let colonTok ← consumeAny
    match ← parseConstraint with
    | some constraintNode =>
      match ← tryConsume .rightBrace with
      | some rbrace1 =>
        match ← tryConsume .rightBrace with
        | some rbrace2 =>
          return some (GreenNode.mkNode .instDictBinder
            #[lbrace1, lbrace2, nameTok, colonTok, constraintNode, rbrace1, rbrace2])
        | none =>
          recordError "expected '}}' to close constraint binder"
          return some (GreenNode.mkError "unclosed constraint binder"
            #[lbrace1, lbrace2, nameTok, colonTok, constraintNode, rbrace1])
      | none =>
        recordError "expected '}}' to close constraint binder"
        return some (GreenNode.mkError "unclosed constraint binder"
          #[lbrace1, lbrace2, nameTok, colonTok, constraintNode])
    | none =>
      recordError "expected constraint after ':' in constraint binder"
      return some (GreenNode.mkError "missing constraint"
        #[lbrace1, lbrace2, nameTok, colonTok])
  else
    match ← parseConstraint with
    | some constraintNode =>
      match ← tryConsume .rightBrace with
      | some rbrace1 =>
        match ← tryConsume .rightBrace with
        | some rbrace2 =>
          return some (GreenNode.mkNode .instDictBinder
            #[lbrace1, lbrace2, constraintNode, rbrace1, rbrace2])
        | none =>
          recordError "expected '}}' to close constraint binder"
          return some (GreenNode.mkError "unclosed constraint binder"
            #[lbrace1, lbrace2, constraintNode, rbrace1])
      | none =>
        recordError "expected '}}' to close constraint binder"
        return some (GreenNode.mkError "unclosed constraint binder"
          #[lbrace1, lbrace2, constraintNode])
    | none =>
      recordError "expected constraint inside `{{...}}`"
      return some (GreenNode.mkError "missing constraint" #[lbrace1, lbrace2])

/-- Parse `forall a b c. body` -/
partial def parseForallExpr : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_forall with
  | some forallTok =>
      let mut vars : Array GreenNode := #[]
      while true do
        match ← parseForallBinder with
        | some binder => vars := vars.push binder
        | none => break

      if vars.isEmpty then
        recordError "expected type variables after 'forall'"

      match ← tryConsumeDot with
      | some dotTok =>
          match ← parseExpr with
          | some body =>
              let varList := GreenNode.mkNode .tyParamList vars
              return some (GreenNode.mkNode .typeForall #[forallTok, varList, dotTok, body])
          | none =>
              recordError "expected expression after 'forall ... .'"
              return some (GreenNode.mkError "incomplete forall" #[forallTok])
      | none =>
          recordError "expected '.' after forall variables"
          match ← parseExpr with
          | some body =>
              let varList := GreenNode.mkNode .tyParamList vars
              return some (GreenNode.mkNode .typeForall #[forallTok, varList, body])
          | none =>
              return some (GreenNode.mkError "incomplete forall" #[forallTok])
  | none => return none

/-- Parse `∀ a b c. body` -/
partial def parseForallSymbolExpr : ParserM (Option GreenNode) := do
  match ← tryConsume .forallSymbol with
  | some forallTok =>
      let mut vars : Array GreenNode := #[]
      while true do
        match ← parseForallBinder with
        | some binder => vars := vars.push binder
        | none => break

      if vars.isEmpty then
        recordError "expected type variables after '∀'"

      match ← tryConsumeDot with
      | some dotTok =>
          match ← parseExpr with
          | some body =>
              let varList := GreenNode.mkNode .tyParamList vars
              return some (GreenNode.mkNode .typeForall #[forallTok, varList, dotTok, body])
          | none =>
              recordError "expected expression after '∀ ... .'"
              return some (GreenNode.mkError "incomplete forall" #[forallTok])
      | none =>
          recordError "expected '.' after ∀ variables"
          match ← parseExpr with
          | some body =>
              let varList := GreenNode.mkNode .tyParamList vars
              return some (GreenNode.mkNode .typeForall #[forallTok, varList, body])
          | none =>
              return some (GreenNode.mkError "incomplete forall" #[forallTok])
  | none => return none

/-- Parse `{{x : A}} -> B` (named instance binder) or `{{A}} -> B` (unnamed) -/
partial def parseImplicitBinderExpr : ParserM (Option GreenNode) := do
  if !(← checkDoubleBrace) then return none

  let lbrace1 ← consumeAny
  let lbrace2 ← consumeAny

  if (← check .rightBrace) then
    recordError "empty implicit parameter"
    let rbrace1 ← consumeAny
    if (← check .rightBrace) then
      let rbrace2 ← consumeAny
      return some (GreenNode.mkError "empty implicit" #[lbrace1, lbrace2, rbrace1, rbrace2])
    return some (GreenNode.mkError "empty implicit" #[lbrace1, lbrace2, rbrace1])

  let tok ← current
  if tok.kind == some .lowerIdent then
    let nameTok ← consumeAny
    if (← check .colon) then
      let colonTok ← consumeAny
      match ← parseExpr with
      | some domainTy =>
          match ← tryConsume .rightBrace with
          | some rbrace1 =>
              match ← tryConsume .rightBrace with
              | some rbrace2 =>
                  if (← check .arrow) then
                    let arrowTok ← consumeAny
                    match ← parseExpr with
                    | some codomainTy =>
                        let binder := GreenNode.mkNode .typePiBinder #[GreenNode.mkNode .typeVar #[nameTok], colonTok, domainTy]
                        return some (GreenNode.mkNode .typeImplicit #[lbrace1, lbrace2, binder, rbrace1, rbrace2, arrowTok, codomainTy])
                    | none =>
                        recordError "expected expression after '->'"
                        return some (GreenNode.mkError "incomplete implicit binder" #[lbrace1, lbrace2, nameTok, colonTok, domainTy, rbrace1, rbrace2, arrowTok])
                  else
                    recordError "implicit parameter must be followed by '->'"
                    let binder := GreenNode.mkNode .typePiBinder #[GreenNode.mkNode .typeVar #[nameTok], colonTok, domainTy]
                    return some (GreenNode.mkNode .typeImplicit #[lbrace1, lbrace2, binder, rbrace1, rbrace2])
              | none =>
                  recordError "expected '}}' after implicit parameter"
                  return some (GreenNode.mkError "unclosed implicit" #[lbrace1, lbrace2, nameTok, colonTok, domainTy, rbrace1])
          | none =>
              recordError "expected '}}' after implicit parameter"
              return some (GreenNode.mkError "unclosed implicit" #[lbrace1, lbrace2, nameTok, colonTok, domainTy])
      | none =>
          recordError "expected expression after ':' in implicit"
          return some (GreenNode.mkError "missing type in implicit" #[lbrace1, lbrace2, nameTok, colonTok])
    else
      let nameExpr := GreenNode.mkNode .exprVar #[nameTok]
      let domain ← parseExprAppContinue nameExpr
      match ← tryConsume .rightBrace with
      | some rbrace1 =>
          match ← tryConsume .rightBrace with
          | some rbrace2 =>
              if (← check .arrow) then
                let arrowTok ← consumeAny
                match ← parseExpr with
                | some codomainTy =>
                    return some (GreenNode.mkNode .typeImplicit #[lbrace1, lbrace2, domain, rbrace1, rbrace2, arrowTok, codomainTy])
                | none =>
                    recordError "expected expression after '->'"
                    return some (GreenNode.mkError "incomplete implicit binder" #[lbrace1, lbrace2, domain, rbrace1, rbrace2, arrowTok])
              else
                recordError "implicit parameter must be followed by '->'"
                return some (GreenNode.mkNode .typeImplicit #[lbrace1, lbrace2, domain, rbrace1, rbrace2])
          | none =>
              recordError "expected '}}' after implicit parameter"
              return some (GreenNode.mkError "unclosed implicit" #[lbrace1, lbrace2, domain, rbrace1])
      | none =>
          recordError "expected '}}' after implicit parameter"
          return some (GreenNode.mkError "unclosed implicit" #[lbrace1, lbrace2, domain])
  else
    match ← parseExpr with
    | some domain =>
        match ← tryConsume .rightBrace with
        | some rbrace1 =>
            match ← tryConsume .rightBrace with
            | some rbrace2 =>
                if (← check .arrow) then
                  let arrowTok ← consumeAny
                  match ← parseExpr with
                  | some codomainTy =>
                      return some (GreenNode.mkNode .typeImplicit #[lbrace1, lbrace2, domain, rbrace1, rbrace2, arrowTok, codomainTy])
                  | none =>
                      recordError "expected expression after '->'"
                      return some (GreenNode.mkError "incomplete implicit binder" #[lbrace1, lbrace2, domain, rbrace1, rbrace2, arrowTok])
                else
                  recordError "implicit parameter must be followed by '->'"
                  return some (GreenNode.mkNode .typeImplicit #[lbrace1, lbrace2, domain, rbrace1, rbrace2])
            | none =>
                recordError "expected '}}' after implicit parameter"
                return some (GreenNode.mkError "unclosed implicit" #[lbrace1, lbrace2, domain, rbrace1])
        | none =>
            recordError "expected '}}' after implicit parameter"
            return some (GreenNode.mkError "unclosed implicit" #[lbrace1, lbrace2, domain])
    | none =>
        recordError "expected constraint inside implicit binder"
        return some (GreenNode.mkError "empty implicit" #[lbrace1, lbrace2])

/-- Parse a variant type case `Foo : T` -/
partial def parseVariantTypeCase : ParserM (Option GreenNode) := do
  match ← parseUpperIdent with
  | some nameTok =>
      let colonTok? ← do
        match ← tryConsume .colon with
        | some tok => pure (some tok)
        | none => tryConsume .doubleColon
      match colonTok? with
      | some colonTok =>
          match ← parseExpr with
          | some ty =>
              return some (GreenNode.mkNode .typeVariantCase #[nameTok, colonTok, ty])
          | none =>
            recordError "expected expression after ':' in variant case"
            return some (GreenNode.mkError "missing case type" #[nameTok, colonTok])
      | none =>
          recordError "expected ':' after case name in variant type"
          return some (GreenNode.mkError "missing ':' in variant case" #[nameTok])
  | none => return none

/-- Parse a variant type `< Ok : Int | Err : String >` (or with row var tail) -/
partial def parseVariantTypeExpr : ParserM (Option GreenNode) := do
  match ← tryConsume .leftAngle with
  | some langle =>
      if (← check .rightAngle) then
        let rangle ← consumeAny
        return some (GreenNode.mkNode .typeVariant #[langle, rangle])

      let mut cases : Array GreenNode := #[]
      match ← parseVariantTypeCase with
      | some case_ => cases := cases.push case_
      | none =>
          match ← parseLowerIdent with
          | some tailVar =>
              let tailNode := GreenNode.mkNode .typeVar #[tailVar]
              match ← tryConsume .rightAngle with
              | some rangle =>
                  return some (GreenNode.mkNode .typeVariant #[langle, tailNode, rangle])
              | none =>
                  recordError "expected '>' after variant type variable"
                  return some (GreenNode.mkError "unclosed variant type" #[langle, tailNode])
          | none =>
              recordError "expected case or type variable in variant type"
              match ← tryConsume .rightAngle with
              | some rangle => return some (GreenNode.mkNode .typeVariant #[langle, rangle])
              | none => return some (GreenNode.mkError "malformed variant type" #[langle])

      while (← check .pipe) do
        let pipeTok ← consumeAny
        cases := cases.push pipeTok
        let tok ← current
        if tok.kind == some .lowerIdent then
          let tailVar ← consumeAny
          let tailNode := GreenNode.mkNode .typeVar #[tailVar]
          match ← tryConsume .rightAngle with
          | some rangle =>
              let children := #[langle] ++ cases ++ #[tailNode, rangle]
              return some (GreenNode.mkNode .typeVariant children)
          | none =>
              recordError "expected '>' after variant type"
              return some (GreenNode.mkError "unclosed variant type" (#[langle] ++ cases ++ #[tailNode]))
        match ← parseVariantTypeCase with
        | some case_ => cases := cases.push case_
        | none =>
            match ← parseLowerIdent with
            | some tailVar =>
                let tailNode := GreenNode.mkNode .typeVar #[tailVar]
                match ← tryConsume .rightAngle with
                | some rangle =>
                    let children := #[langle] ++ cases ++ #[tailNode, rangle]
                    return some (GreenNode.mkNode .typeVariant children)
                | none =>
                    recordError "expected '>' after variant type"
                    return some (GreenNode.mkError "unclosed variant type" (#[langle] ++ cases ++ #[tailNode]))
            | none =>
                recordError "expected case or row variable after '|' in variant type"
                break

      match ← tryConsume .rightAngle with
      | some rangle =>
          let children := #[langle] ++ cases ++ #[rangle]
          return some (GreenNode.mkNode .typeVariant children)
      | none =>
          recordError "expected '>' after variant type"
          return some (GreenNode.mkError "unclosed variant type" (#[langle] ++ cases))
  | none => return none

/-- Parse a record type field `name : Type` -/
partial def parseRecordTypeField : ParserM (Option GreenNode) := do
  match ← parseLowerIdent with
  | some nameTok =>
      let colonTok? ← do
        match ← tryConsume .colon with
        | some tok => pure (some tok)
        | none => tryConsume .doubleColon
      match colonTok? with
      | some colonTok =>
          match ← parseExpr with
          | some ty =>
              return some (GreenNode.mkNode .typeRecordField #[nameTok, colonTok, ty])
          | none =>
            recordError "expected expression after ':' in record type field"
            return some (GreenNode.mkError "missing field type" #[nameTok, colonTok])
      | none =>
          recordError "expected ':' after field name in record type"
          return some (GreenNode.mkError "missing ':' in record field" #[nameTok])
  | none => return none

/-- Parse a parenthesized expression -/
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

      let isBinder ← do
        let tok0 ← current
        let tok1 ← peekNext
        let tok2 ← peekAhead 2
        let qty0 :=
          tok0.kind == some .omega ||
          (tok0.kind == some .number && (tok0.text == "0" || tok0.text == "1"))
        if qty0 && tok1.kind == some .lowerIdent && tok2.kind == some .colon then
          pure true
        else if tok0.kind == some .lowerIdent && tok1.kind == some .colon then
          pure true
        else
          pure false

      if isBinder then
        let quantityOpt ← parseQuantity
        let nameTok ← consumeAny
        let colonTok ← consumeAny
        match ← parseExpr with
        | some domainTy =>
            match ← tryConsume .rightParen with
            | some rparen =>
                if (← check .arrow) then
                  let arrowTok ← consumeAny
                  match ← parseExpr with
                  | some codomainTy =>
                      let binderChildren := match quantityOpt with
                        | some qty => #[qty, GreenNode.mkNode .typeVar #[nameTok], colonTok, domainTy]
                        | none => #[GreenNode.mkNode .typeVar #[nameTok], colonTok, domainTy]
                      let binder := GreenNode.mkNode .typePiBinder binderChildren
                      return some (GreenNode.mkNode .typePi #[lparen, binder, rparen, arrowTok, codomainTy])
                  | none =>
                      recordError "expected expression after '->'"
                      return some (GreenNode.mkError "incomplete Pi" #[lparen, nameTok, colonTok, domainTy, rparen, arrowTok])
                else if (← check .times) then
                  let timesTok ← consumeAny
                  match ← parseExpr with
                  | some sndTy =>
                      let binderChildren := match quantityOpt with
                        | some qty => #[qty, GreenNode.mkNode .typeVar #[nameTok], colonTok, domainTy]
                        | none => #[GreenNode.mkNode .typeVar #[nameTok], colonTok, domainTy]
                      let binder := GreenNode.mkNode .typePiBinder binderChildren
                      return some (GreenNode.mkNode .typeSigma #[lparen, binder, rparen, timesTok, sndTy])
                  | none =>
                      recordError "expected expression after '×'"
                      return some (GreenNode.mkError "incomplete Sigma" #[lparen, nameTok, colonTok, domainTy, rparen, timesTok])
                else
                  let varNode := GreenNode.mkNode .exprVar #[nameTok]
                  let annotTy := GreenNode.mkNode .typeKinded #[varNode, colonTok, domainTy]
                  return some (GreenNode.mkNode .exprParens #[lparen, annotTy, rparen])
            | none =>
                recordError "expected ')' after binder type"
                return some (GreenNode.mkError "unclosed binder" #[lparen, nameTok, colonTok, domainTy])
        | none =>
            recordError "expected expression after ':' in binder"
            return some (GreenNode.mkError "missing type in binder" #[lparen, nameTok, colonTok])
      else
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
            else if (← check .arrow) then
              let arrowTok ← consumeAny
              match ← parseExpr with
              | some right =>
                  match ← tryConsume .rightParen with
                  | some rparen =>
                      let arrowNode := GreenNode.mkNode .typeArrow #[first, arrowTok, right]
                      return some (GreenNode.mkNode .exprParens #[lparen, arrowNode, rparen])
                  | none =>
                      recordError "expected ')' after arrow"
                      return some (GreenNode.mkError "unclosed arrow" #[lparen, first, arrowTok, right])
              | none =>
                  recordError "expected expression after '->'"
                  return some (GreenNode.mkError "incomplete arrow" #[lparen, first, arrowTok])
            else
              match ← tryConsume .rightParen with
              | some rparen =>
                  return some (GreenNode.mkNode .exprParens #[lparen, first, rparen])
              | none =>
                  recordError "unclosed parentheses"
                  return some (GreenNode.mkError "malformed parens" #[lparen, first])
        | none =>
            recordError "expected expression after '('"
            return some (GreenNode.mkError "empty parens" #[lparen])
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

/-- Parse a record value field `name := expr` (or punned `name`) -/
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
          return some (GreenNode.mkNode .recordField #[nameTok])
  | none => return none

/-- Parse a record literal, update or type -/
partial def parseRecordExpr : ParserM (Option GreenNode) := do
  match ← tryConsume .leftBrace with
  | some lbrace =>
      if (← check .rightBrace) then
        let rbrace ← consumeAny
        return some (GreenNode.mkNode .exprRecord #[lbrace, rbrace])

      let tok ← current
      match tok.kind with
      | some .lowerIdent =>
          let nameTok ← consumeAny
          let nextTok ← current
          match nextTok.kind with
          | some .colon =>
              let colonTok ← consumeAny
              match ← parseExpr with
              | some fieldTy =>
                  let firstField := GreenNode.mkNode .typeRecordField #[nameTok, colonTok, fieldTy]
                  let mut fields := #[firstField]
                  while (← check .comma) do
                    let comma ← consumeAny
                    fields := fields.push comma
                    match ← parseRecordTypeField with
                    | some field => fields := fields.push field
                    | none => recordError "expected field after ','"; break
                  let rowTail ← if (← check .pipe) then
                    let pipeTok ← consumeAny
                    match ← parseLowerIdent with
                    | some tailVar =>
                        let tailNode := GreenNode.mkNode .typeVar #[tailVar]
                        pure (some (pipeTok, tailNode))
                    | none =>
                        recordError "expected type variable after '|' in record type"
                        pure none
                  else pure none
                  match ← tryConsume .rightBrace with
                  | some rbrace =>
                      let children := #[lbrace] ++ fields ++
                        (match rowTail with
                         | some (pipe, tail) => #[pipe, tail]
                         | none => #[]) ++
                        #[rbrace]
                      return some (GreenNode.mkNode .typeRecord children)
                  | none =>
                      recordError "expected '}' after record type"
                      return some (GreenNode.mkError "unclosed record type" (#[lbrace] ++ fields))
              | none =>
                  recordError "expected type after ':' in record type field"
                  return some (GreenNode.mkError "missing field type" #[lbrace, nameTok, colonTok])

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
              -- Record update: `{base | field := value}`
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
              recordError "expected ':', ':=', '|', ',' or '}' after field name in record"
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
                match ← parseExpr with
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
  if !(← check .at) then return none
  let nextTok ← peekNext
  match nextTok.kind with
  | some .lowerIdent =>
    let atTok ← consumeAny
    let labelTok ← consumeAny
    return some (GreenNode.mkNode .exprTypeApp #[atTok, labelTok])
  | some .upperIdent | some .leftParen =>
    let atTok ← consumeAny
    match ← parseExprAtom with
    | some typeTok =>
      return some (GreenNode.mkNode .exprTypeApp #[atTok, typeTok])
    | none =>
      recordError "expected type after '@'"
      return some (GreenNode.mkError "incomplete type application" #[atTok])
  | _ => return none

/-- Atoms are unambiguously delimited primary expressions -/
partial def parseExprAtom : ParserM (Option GreenNode) := do
  if let some e ← parseForallSymbolExpr then return some e
  if let some e ← parseForallExpr then return some e
  if let some e ← parseImplicitBinderExpr then return some e
  if let some e ← parseVariantTypeExpr then return some e
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

/-- Continue the application loop starting from an already parsed head -/
partial def parseExprAppContinue (first : GreenNode) : ParserM GreenNode := do
  let parseAtomWithFieldAccesses : ParserM (Option GreenNode) := do
    match ← parseExprAtom with
    | none => return none
    | some atom =>
      let mut result := atom
      while (← current).kind == some .dot do
        let dotTok ← consumeAny
        match ← parseLowerIdent with
        | some fieldTok =>
            result := GreenNode.mkNode .exprFieldAccess #[result, dotTok, fieldTok]
        | none =>
            recordError "expected field name after '.'"
            break
      return some result

  let mut result := first
  while true do
    let tok ← current
    if tok.kind == some .varSymbol || tok.kind == some .rightParen ||
       tok.kind == some .rightBracket || tok.kind == some .rightBrace ||
       tok.kind == some .comma || tok.kind == some .pipe ||
       tok.kind == some .fatArrow || tok.kind == some .equals ||
       tok.kind == some .kw_in || tok.kind == some .kw_then ||
       tok.kind == some .kw_else || tok.kind == some .kw_where ||
       tok.kind == some .doubleColon ||
       tok.kind == some .arrow || tok.kind == some .times ||
       tok.kind == some .colon ||
       tok.kind == some .rightAngle ||
       tok.kind == some .layoutStart || tok.kind == some .layoutSep ||
       tok.kind == some .layoutEnd || tok.kind == some .eof then
      break
    match ← parseAtomWithFieldAccesses with
    | some arg =>
        result := GreenNode.mkNode .exprApp #[result, arg]
    | none => break
  return result

partial def parseExprApp : ParserM (Option GreenNode) := do
  let parseAtomWithFieldAccesses : ParserM (Option GreenNode) := do
    match ← parseExprAtom with
    | none => return none
    | some atom =>
      let mut result := atom
      while (← current).kind == some .dot do
        let dotTok ← consumeAny
        match ← parseLowerIdent with
        | some fieldTok =>
            result := GreenNode.mkNode .exprFieldAccess #[result, dotTok, fieldTok]
        | none =>
            recordError "expected field name after '.'"
            break
      return some result
  match ← parseAtomWithFieldAccesses with
  | some first => some <$> parseExprAppContinue first
  | none => return none

/-- Continue infix parsing from an already-parsed left-hand side -/
partial def parseExprInfixContinue (left : GreenNode) (minPrec : Nat)
    : ParserM GreenNode := do
  let mut result := left
  while (← check .varSymbol) || (← check .equals) do
    let tok ← current
    let opText := if tok.kind == some .equals then "=" else tok.text
    let (prec, assoc) := operatorPrecedence opText
    if prec < minPrec then break
    let opTok ← consumeAny
    let nextMinPrec := match assoc with
      | .right => prec
      | .left  => prec + 1
      | .none  => prec + 1
    match ← parseExprApp with
    | some rightAtom =>
        let right ← parseExprInfixContinue rightAtom nextMinPrec
        result := GreenNode.mkNode .exprInfix #[result, opTok, right]
    | none =>
        recordError s!"expected expression after operator '{opText}'"
        return result
  return result

partial def parseExprInfix : ParserM (Option GreenNode) := do
  match ← parseExprApp with
  | some first => some <$> parseExprInfixContinue first 0
  | none => return none

/-- A right-associative arrow at the top of the term grammar -/
partial def parseExpr : ParserM (Option GreenNode) := do
  match ← parseExprInfix with
  | some left =>
      if (← check .arrow) then
        let arrowTok ← consumeAny
        match ← parseExpr with
        | some right =>
            return some (GreenNode.mkNode .typeArrow #[left, arrowTok, right])
        | none =>
            recordError "expected expression after '->'"
            return some (GreenNode.mkError "incomplete arrow" #[left, arrowTok])
      else if (← check .doubleColon) then
        let colonTok ← consumeAny
        match ← parseExpr with
        | some ty =>
            return some (GreenNode.mkNode .exprTypeAnnot #[left, colonTok, ty])
        | none =>
            recordError "expected expression after '::'"
            return some (GreenNode.mkError "missing type annotation" #[left, colonTok])
      else
        return some left
  | none => return none

/-- A class constraint -/
partial def parseConstraint : ParserM (Option GreenNode) := do
  match ← parseUpperIdent with
  | some first =>
      let mut classNameParts : Array GreenNode := #[first]
      while (← check .doubleColon) do
        let sep ← consumeAny
        match ← parseIdentAny with
        | some next =>
            classNameParts := classNameParts.push sep
            classNameParts := classNameParts.push next
        | none =>
            recordError "expected identifier after '::' in class name"
            classNameParts := classNameParts.push sep
            break
      let className := GreenNode.mkNode .typeCon classNameParts
      let mut args := #[className]
      while true do
        let tok ← current
        if tok.kind == some .comma || tok.kind == some .rightParen ||
           tok.kind == some .rightBrace ||
           tok.kind == some .kw_where ||
           tok.kind == some .layoutStart || tok.kind == some .layoutSep ||
           tok.kind == some .layoutEnd || tok.kind == some .eof then
          break
        match ← parseExprAtom with
        | some arg => args := args.push arg
        | none => break
      return some (GreenNode.mkNode .constraint args)
  | none => return none

partial def parseConstraints : ParserM (Option GreenNode) := do
  if (← check .leftParen) then
    let lparen ← consumeAny
    let constraints ← commaSep parseConstraint
    match ← tryConsume .rightParen with
    | some rparen =>
        return some (GreenNode.mkNode .constraintList (#[lparen] ++ constraints ++ #[rparen]))
    | none =>
        recordError "expected ')' after constraint list"
        return some (GreenNode.mkError "unclosed constraint list" (#[lparen] ++ constraints))
  else
    parseConstraint

/-- A `:: T` signature attached to a let / dff / field -/
partial def parseTypeSignature : ParserM (Option GreenNode) := do
  match ← tryConsume .doubleColon with
  | some colonTok =>
      match ← parseExpr with
      | some ty =>
          return some (GreenNode.mkNode .signature #[colonTok, ty])
      | none =>
          recordError "expected type after '::'"
          return some (GreenNode.mkError "missing type in signature" #[colonTok])
  | none => return none

end

def parseOptionalSignature : ParserM (Option GreenNode) := do
  if (← check .doubleColon) then parseTypeSignature
  else return none

def parseType : ParserM (Option GreenNode) := parseExpr

end Soma.Syntax.Parse
