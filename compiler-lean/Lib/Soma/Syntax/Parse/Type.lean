import Soma.Syntax.Parser

namespace Soma.Syntax.Parse

open ParserM

/-! ## Type Atoms -/

def parseTypeVar : ParserM (Option GreenNode) := do
  match ← parseLowerIdent with
  | some tok => return some (GreenNode.mkNode .typeVar #[tok])
  | none => return none

def parseTypeCon : ParserM (Option GreenNode) := do
  match ← parseUpperIdent with
  | some tok => return some (GreenNode.mkNode .typeCon #[tok])
  | none => return none

def checkDot : ParserM Bool := do
  let tok ← current
  return tok.kind == some .varSymbol && tok.text == "."

def tryConsumeDot : ParserM (Option GreenNode) := do
  if (← checkDot) then return some (← consumeAny) else return none

mutual

/-- Parse an atomic kind: *, %, #, Row, Label, or parenthesized kind -/
partial def parseKindAtom : ParserM (Option GreenNode) := do
  let tok ← current
  -- * (star kind)
  if tok.kind == some .varSymbol && tok.text == "*" then
    let g ← consumeAny
    return some (GreenNode.mkNode .typeCon #[g])
  -- % (row kind)
  if tok.kind == some .varSymbol && tok.text == "%" then
    let g ← consumeAny
    return some (GreenNode.mkNode .typeCon #[g])
  -- # (label kind)
  if tok.kind == some .hash then
    let g ← consumeAny
    return some (GreenNode.mkNode .typeCon #[g])
  -- Named kinds: Row, Label, or other identifiers
  if tok.kind == some .upperIdent then
    let g ← consumeAny
    return some (GreenNode.mkNode .typeCon #[g])
  -- Parenthesized kinds: (* -> *)
  if tok.kind == some .leftParen then
    let lparen ← consumeAny
    match ← parseKind with
    | some inner =>
        match ← tryConsume .rightParen with
        | some rparen =>
            return some (GreenNode.mkNode .typeParens #[lparen, inner, rparen])
        | none =>
            recordError "expected ')' after kind"
            return some inner
    | none =>
        recordError "expected kind after '('"
        return none
  return none

/-- Parse a kind expression, including arrow kinds like * -> * -/
partial def parseKind : ParserM (Option GreenNode) := do
  match ← parseKindAtom with
  | some left =>
      if (← check .arrow) then
        let arrowTok ← consumeAny
        match ← parseKind with
        | some right =>
            return some (GreenNode.mkNode .typeArrow #[left, arrowTok, right])
        | none =>
            recordError "expected kind after '->'"
            return some left
      else
        return some left
  | none => return none

partial def parseParenType : ParserM (Option GreenNode) := do
  match ← tryConsume .leftParen with
  | some lparen =>
      if (← check .rightParen) then
        let rparen ← consumeAny
        return some (GreenNode.mkNode .typeTuple #[lparen, rparen])

      match ← parseType with
      | some first =>
          if (← check .comma) then
            let mut elements := #[first]
            while (← check .comma) do
              let _ ← consumeAny
              match ← parseType with
              | some elem => elements := elements.push elem
              | none => recordError "expected type after ','"; break
            match ← tryConsume .rightParen with
            | some rparen =>
                return some (GreenNode.mkNode .typeTuple (#[lparen] ++ elements ++ #[rparen]))
            | none =>
                recordError "expected ')' after tuple type"
                return some (GreenNode.mkError "unclosed tuple type" (#[lparen] ++ elements))
          else
            match ← tryConsume .rightParen with
            | some rparen =>
                return some (GreenNode.mkNode .typeParens #[lparen, first, rparen])
            | none =>
                recordError "expected ')' or ',' in type"
                return some (GreenNode.mkError "malformed parenthesized type" #[lparen, first])
      | none =>
          recordError "expected type after '('"
          return some (GreenNode.mkError "empty type parentheses" #[lparen])
  | none => return none

/-- Parse a record type field: name :: Type -/
partial def parseRecordTypeField : ParserM (Option GreenNode) := do
  match ← parseLowerIdent with
  | some nameTok =>
      match ← tryConsume .doubleColon with
      | some colonTok =>
          match ← parseType with
          | some ty =>
              return some (GreenNode.mkNode .typeRecordField #[nameTok, colonTok, ty])
          | none =>
              recordError "expected type after '::' in record field"
              return some (GreenNode.mkError "missing field type" #[nameTok, colonTok])
      | none =>
          recordError "expected '::' after field name in record type"
          return some (GreenNode.mkError "missing '::' in record field" #[nameTok])
  | none => return none

/-- Parse a record type: { x :: Int, y :: Bool } or { x :: Int | r } -/
partial def parseRecordType : ParserM (Option GreenNode) := do
  match ← tryConsume .leftBrace with
  | some lbrace =>
      -- Check for empty record type
      if (← check .rightBrace) then
        let rbrace ← consumeAny
        return some (GreenNode.mkNode .typeRecord #[lbrace, rbrace])

      -- Parse first field
      let mut fields : Array GreenNode := #[]
      match ← parseRecordTypeField with
      | some field => fields := fields.push field
      | none =>
          recordError "expected field in record type"
          match ← tryConsume .rightBrace with
          | some rbrace => return some (GreenNode.mkNode .typeRecord #[lbrace, rbrace])
          | none => return some (GreenNode.mkError "malformed record type" #[lbrace])

      -- Parse remaining fields or row variable tail
      while (← check .comma) do
        let _ ← consumeAny
        match ← parseRecordTypeField with
        | some field => fields := fields.push field
        | none => recordError "expected field after ',' in record type"; break

      -- Check for row variable tail: | r
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
  | none => return none

/-- Parse a variant type case: Name :: Type -/
partial def parseVariantTypeCase : ParserM (Option GreenNode) := do
  match ← parseUpperIdent with
  | some nameTok =>
      match ← tryConsume .doubleColon with
      | some colonTok =>
          match ← parseType with
          | some ty =>
              return some (GreenNode.mkNode .typeVariantCase #[nameTok, colonTok, ty])
          | none =>
              recordError "expected type after '::' in variant case"
              return some (GreenNode.mkError "missing case type" #[nameTok, colonTok])
      | none =>
          recordError "expected '::' after case name in variant type"
          return some (GreenNode.mkError "missing '::' in variant case" #[nameTok])
  | none => return none

/-- Parse a variant type: < Ok :: Int | Err :: String > or < Ok :: Int | r > -/
partial def parseVariantType : ParserM (Option GreenNode) := do
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
        let _ ← consumeAny
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
            -- Try as row variable
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

partial def parseListType : ParserM (Option GreenNode) := do
  match ← tryConsume .leftBracket with
  | some lbracket =>
      match ← parseType with
      | some elemType =>
          match ← tryConsume .rightBracket with
          | some rbracket =>
              return some (GreenNode.mkNode .typeList #[lbracket, elemType, rbracket])
          | none =>
              recordError "expected ']' after list type"
              return some (GreenNode.mkError "unclosed list type" #[lbracket, elemType])
      | none =>
          match ← tryConsume .rightBracket with
          | some rbracket =>
              return some (GreenNode.mkNode .typeList #[lbracket, rbracket])
          | none =>
              recordError "expected type or ']' after '['"
              return some (GreenNode.mkError "incomplete list type" #[lbracket])
  | none => return none

/-- Parse a single forall type variable binder -/
partial def parseForallBinder : ParserM (Option GreenNode) := do
  -- Try kinded binder: (name :: Kind) where Kind can be *, %, #, * -> *, etc.
  if (← check .leftParen) then
    let lparen ← consumeAny
    match ← parseLowerIdent with
    | some varTok =>
        match ← tryConsume .doubleColon with
        | some colonTok =>
            -- Use parseKind to handle arrow kinds like * -> *
            match ← parseKind with
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
                recordError "expected kind after '::' in type parameter"
                let varNode := GreenNode.mkNode .typeVar #[varTok]
                return some (GreenNode.mkError "missing kind" #[lparen, varNode, colonTok])
        | none =>
            recordError "expected '::' in kinded type parameter"
            return some (GreenNode.mkError "missing '::'" #[lparen, varTok])
    | none =>
        recordError "expected type variable name after '(' in forall"
        return some (GreenNode.mkError "missing var name" #[lparen])
  else
    match ← parseLowerIdent with
    | some varTok => return some (GreenNode.mkNode .typeVar #[varTok])
    | none => return none

partial def parseForallType : ParserM (Option GreenNode) := do
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
          match ← parseType with
          | some body =>
              let varList := GreenNode.mkNode .tyParamList vars
              return some (GreenNode.mkNode .typeForall #[forallTok, varList, dotTok, body])
          | none =>
              recordError "expected type after 'forall ... .'"
              return some (GreenNode.mkError "incomplete forall type" #[forallTok])
      | none =>
          recordError "expected '.' after forall type variables"
          match ← parseType with
          | some body =>
              let varList := GreenNode.mkNode .tyParamList vars
              return some (GreenNode.mkNode .typeForall #[forallTok, varList, body])
          | none =>
              return some (GreenNode.mkError "incomplete forall type" #[forallTok])
  | none => return none

partial def parseForallSymbolType : ParserM (Option GreenNode) := do
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
          match ← parseType with
          | some body =>
              let varList := GreenNode.mkNode .tyParamList vars
              return some (GreenNode.mkNode .typeForall #[forallTok, varList, dotTok, body])
          | none =>
              recordError "expected type after '∀ ... .'"
              return some (GreenNode.mkError "incomplete forall type" #[forallTok])
      | none =>
          recordError "expected '.' after ∀ type variables"
          match ← parseType with
          | some body =>
              let varList := GreenNode.mkNode .tyParamList vars
              return some (GreenNode.mkNode .typeForall #[forallTok, varList, body])
          | none =>
              return some (GreenNode.mkError "incomplete forall type" #[forallTok])
  | none => return none

partial def parseTypeAtom : ParserM (Option GreenNode) := do
  if let some ty ← parseForallType then return some ty
  if let some ty ← parseForallSymbolType then return some ty
  if let some ty ← parseParenType then return some ty
  if let some ty ← parseListType then return some ty
  if let some ty ← parseRecordType then return some ty
  if let some ty ← parseVariantType then return some ty
  if let some ty ← parseTypeVar then return some ty
  if let some ty ← parseTypeCon then return some ty
  return none

partial def parseTypeApp : ParserM (Option GreenNode) := do
  match ← parseTypeAtom with
  | some first =>
      let mut args := #[first]
      while true do
        let tok ← current
        if tok.kind == some .arrow || tok.kind == some .fatArrow ||
           tok.kind == some .rightParen || tok.kind == some .rightBracket ||
           tok.kind == some .rightBrace || tok.kind == some .comma ||
           tok.kind == some .kw_with || tok.kind == some .kw_where ||
           tok.kind == some .pipe || tok.kind == some .equals ||
           tok.kind == some .layoutStart || tok.kind == some .layoutSep ||
           tok.kind == some .layoutEnd || tok.kind == some .eof then
          break
        match ← parseTypeAtom with
        | some arg => args := args.push arg
        | none => break
      if args.size == 1 then return some first
      else return some (GreenNode.mkNode .typeApp args)
  | none => return none

partial def parseTypeArrow : ParserM (Option GreenNode) := do
  match ← parseTypeApp with
  | some left =>
      if (← check .arrow) then
        let arrowTok ← consumeAny
        match ← parseTypeArrow with
        | some right =>
            return some (GreenNode.mkNode .typeArrow #[left, arrowTok, right])
        | none =>
            recordError "expected type after '->'"
            return some (GreenNode.mkError "incomplete arrow type" #[left, arrowTok])
      else
        return some left
  | none => return none

partial def parseConstraint : ParserM (Option GreenNode) := do
  match ← parseUpperIdent with
  | some classTok =>
      let className := GreenNode.mkNode .typeCon #[classTok]
      let mut args := #[className]
      while true do
        let tok ← current
        if tok.kind == some .comma || tok.kind == some .rightParen ||
           tok.kind == some .kw_where || tok.kind == some .kw_with ||
           tok.kind == some .layoutStart || tok.kind == some .layoutSep ||
           tok.kind == some .layoutEnd || tok.kind == some .eof then
          break
        match ← parseTypeAtom with
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

partial def parseType : ParserM (Option GreenNode) := do
  match ← parseTypeArrow with
  | some ty =>
      if (← check .kw_with) then
        let withTok ← consumeAny
        match ← parseConstraints with
        | some constraints =>
            return some (GreenNode.mkNode .typeConstrained #[ty, withTok, constraints])
        | none =>
            recordError "expected constraints after 'with'"
            return some (GreenNode.mkError "missing constraints" #[ty, withTok])
      else
        return some ty
  | none => return none

end

def parseTypeSignature : ParserM (Option GreenNode) := do
  match ← tryConsume .doubleColon with
  | some colonTok =>
      match ← parseType with
      | some ty =>
          return some (GreenNode.mkNode .signature #[colonTok, ty])
      | none =>
          recordError "expected type after '::'"
          return some (GreenNode.mkError "missing type in signature" #[colonTok])
  | none => return none

def parseOptionalSignature : ParserM (Option GreenNode) := do
  if (← check .doubleColon) then parseTypeSignature
  else return none

end Soma.Syntax.Parse
