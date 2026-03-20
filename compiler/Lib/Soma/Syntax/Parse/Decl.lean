import Soma.Syntax.Parser
import Soma.Syntax.Parse.Pattern
import Soma.Syntax.Parse.Type
import Soma.Syntax.Parse.Expr

namespace Soma.Syntax.Parse

open ParserM

def parseAttribute : ParserM (Option GreenNode) := do
  match ← tryConsume .at with
  | some atTok =>
      match ← tryConsume .leftBracket with
      | some lbracket =>
          match ← parseLowerIdent with
          | some nameTok =>
              let argNode ← do
                let tok ← current
                match tok.kind with
                | some (.string _) =>
                    let strTok ← consumeAny
                    pure (some strTok)
                | _ => pure none
              match ← tryConsume .rightBracket with
              | some rbracket =>
                  let children := match argNode with
                    | some arg => #[atTok, lbracket, nameTok, arg, rbracket]
                    | none => #[atTok, lbracket, nameTok, rbracket]
                  return some (GreenNode.mkNode .attribute children)
              | none =>
                  recordError "expected ']' after attribute"
                  return some (GreenNode.mkError "unclosed attribute" #[atTok, lbracket, nameTok])
          | none =>
              recordError "expected attribute name"
              return some (GreenNode.mkError "missing attribute name" #[atTok, lbracket])
      | none =>
          recordError "expected '[' after '@'"
          return some (GreenNode.mkError "malformed attribute" #[atTok])
  | none => return none

def parseAttributes : ParserM (Array GreenNode) := do
  let mut attrs : Array GreenNode := #[]
  while (← check .at) do
    match ← parseAttribute with
    | some attr => attrs := attrs.push attr
    | none => break
  return attrs

/-- Check if attributes contain @[intrinsic] or @[extern] which allow bodiless declarations -/
def hasBodyProvidingAttr (attrs : Array GreenNode) : Bool :=
  let isBodyName (txt : String) : Bool := txt == "intrinsic" || txt == "extern"
  let hasBodyNameInChild (n : GreenNode) : Bool :=
    match n with
    | .token _ txt => isBodyName txt
    | .node _ children _ => children.any fun gc =>
        match gc with
        | .token _ txt => isBodyName txt
        | _ => false
    | .error _ children _ => children.any fun gc =>
        match gc with
        | .token _ txt => isBodyName txt
        | _ => false
    | .missing _ => false
  attrs.any fun attr =>
    attr.syntaxKind? == some .attribute && attr.children.any hasBodyNameInChild

partial def parseDefClause : ParserM (Option GreenNode) := do
  match ← tryConsume .pipe with
  | some pipeTok =>
      let mut children : Array GreenNode := #[pipeTok]
      let mut patternCount := 0

      match ← parsePattern with
      | some pat =>
          children := children.push pat
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
          children := children.push commaTok
          match ← parsePattern with
          | some pat =>
              children := children.push pat
              patternCount := patternCount + 1
          | none =>
              recordError "expected pattern after ','"
              return some (GreenNode.mkError "missing pattern after ','" children)
        else
          recordError "expected ',' between multiple patterns"
          return some (GreenNode.mkError "missing ',' between patterns" children)

      if patternCount == 0 then
        recordError "expected pattern after '|'"
        return some (GreenNode.mkError "missing pattern" #[pipeTok])

      let tok ← current
      if tok.kind == some .fatArrow then
        let arrowTok ← consumeAny
        match ← inLayout parseExpr with
        | some body =>
            return some (GreenNode.mkNode .defClause (children ++ #[arrowTok, body]))
        | none =>
            recordError "expected expression after '=>'"
            return some (GreenNode.mkError "missing clause body" children)
      else
        recordError "expected '=>' after patterns"
        return some (GreenNode.mkError "missing '=>'" children)
  | none => return none

def parseDefBinder : ParserM (Option GreenNode) := do
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
            return some (GreenNode.mkNode .field #[lparen, nameTok, colonTok, ty, rparen])
          | none =>
            recordError "expected ')' after function binder"
            return some (GreenNode.mkError "unclosed function binder" #[lparen, nameTok, colonTok, ty])
        | none =>
          recordError "expected type after ':' in function binder"
          return some (GreenNode.mkError "missing function binder type" #[lparen, nameTok, colonTok])
      else
        recordError "expected ':' in function binder"
        return some (GreenNode.mkError "missing ':' in function binder" #[lparen, nameTok])
    | none =>
      recordError "expected binder name after '('"
      return some (GreenNode.mkError "missing function binder name" #[lparen])
  else if (← check .leftBrace) then
    let lbrace ← consumeAny
    match ← parseLowerIdent with
    | some nameTok =>
      if (← check .colon) then
        let colonTok ← consumeAny
        match ← parseType with
        | some ty =>
          match ← tryConsume .rightBrace with
          | some rbrace =>
            return some (GreenNode.mkNode .field #[lbrace, nameTok, colonTok, ty, rbrace])
          | none =>
            recordError "expected '}' after function binder"
            return some (GreenNode.mkError "unclosed function binder" #[lbrace, nameTok, colonTok, ty])
        | none =>
          recordError "expected type after ':' in function binder"
          return some (GreenNode.mkError "missing function binder type" #[lbrace, nameTok, colonTok])
      else
        recordError "expected ':' in function binder"
        return some (GreenNode.mkError "missing ':' in function binder" #[lbrace, nameTok])
    | none =>
      recordError "expected binder name after '{'"
      return some (GreenNode.mkError "missing function binder name" #[lbrace])
  else
    return none

partial def parseDefDecl (attrs : Array GreenNode) : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_def with
  | some defTok =>
      let nameNode ← if (← check .leftBrace) then do
        match ← parseOperatorName with
        | some op => pure op
        | none =>
            recordError "expected operator name"
            pure (GreenNode.mkError "missing name" #[defTok])
      else
        match ← parseIdent with
        | some nameTok => pure (GreenNode.mkNode .name #[nameTok])
        | none =>
            recordError "expected function name after 'def'"
            pure (.missing .name)

      let binders ← many parseDefBinder
      let params := if binders.isEmpty then none else some (GreenNode.mkNode .paramList binders)

      let signature ← if (← check .colon) then do
        let colonTok ← consumeAny
        match ← parseType with
        | some ty => pure (some (GreenNode.mkNode .signature #[colonTok, ty]))
        | none => recordError "expected type after ':'"; pure none
      else pure none

      if (← check .equals) then
        let eqTok ← consumeAny
        match ← inLayout parseExpr with
        | some body =>
            let children := attrs ++ #[defTok, nameNode] ++
              (match params with | some p => #[p] | none => #[]) ++
              (match signature with | some s => #[s] | none => #[]) ++
              #[eqTok, body]
            return some (GreenNode.mkNode .declDef children)
        | none =>
            recordError "expected expression after '='"
            return some (GreenNode.mkError "missing definition body" (attrs ++ #[defTok, nameNode]))

      else if (← checkNextRelevant .pipe) then
        let clauses ← layoutSepBy parseDefClause

        if clauses.isEmpty then
          recordError "expected definition clauses"

        let children := attrs ++ #[defTok, nameNode] ++
          (match params with | some p => #[p] | none => #[]) ++
          (match signature with | some s => #[s] | none => #[]) ++
          clauses
        return some (GreenNode.mkNode .declDef children)

      else
        -- Bodiless declaration: only allowed with @[intrinsic] or @[extern]
        if signature.isSome && hasBodyProvidingAttr attrs then
          let children := attrs ++ #[defTok, nameNode, signature.get!]
          return some (GreenNode.mkNode .declDef children)
        else if signature.isSome then
          recordError "bodiless def requires @[intrinsic] or @[extern] attribute"
          return some (GreenNode.mkError "missing body" (attrs ++ #[defTok, nameNode, signature.get!]))
        else
          recordError "expected '=', '|', or ':' after function declaration"
          return some (GreenNode.mkError "incomplete definition" (attrs ++ #[defTok, nameNode]))
  | none => return none

def parseConstructorField : ParserM (Option GreenNode) := do
  match ← parseLowerIdent with
  | some nameTok =>
      let colonTok? ← do
        match ← tryConsume .colon with
        | some tok => pure (some tok)
        | none => tryConsume .doubleColon
      match colonTok? with
      | some colonTok =>
          match ← parseType with
          | some ty => return some (GreenNode.mkNode .field #[nameTok, colonTok, ty])
          | none =>
              recordError "expected type after ':'"
              return some (GreenNode.mkError "missing field type" #[nameTok, colonTok])
      | none =>
          -- Wrap the identifier as a type variable
          let tyNode := GreenNode.mkNode .typeVar #[nameTok]
          return some (GreenNode.mkNode .field #[tyNode])
  | none =>
      -- Try parsing an anonymous type field
      match ← parseType with
      | some ty => return some (GreenNode.mkNode .field #[ty])
      | none => return none

def parseConstructorBinder : ParserM (Option GreenNode) := do
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
            return some (GreenNode.mkNode .field #[lparen, nameTok, colonTok, ty, rparen])
          | none =>
            recordError "expected ')' after constructor binder"
            return some (GreenNode.mkError "unclosed constructor binder" #[lparen, nameTok, colonTok, ty])
        | none =>
          recordError "expected type after ':' in constructor binder"
          return some (GreenNode.mkError "missing constructor binder type" #[lparen, nameTok, colonTok])
      else
        recordError "expected ':' in constructor binder"
        return some (GreenNode.mkError "missing ':' in constructor binder" #[lparen, nameTok])
    | none =>
      recordError "expected binder name in constructor binder"
      return some (GreenNode.mkError "missing constructor binder name" #[lparen])
  else if (← check .leftBrace) then
    let lbrace ← consumeAny
    match ← parseLowerIdent with
    | some nameTok =>
      if (← check .colon) then
        let colonTok ← consumeAny
        match ← parseType with
        | some ty =>
          match ← tryConsume .rightBrace with
          | some rbrace =>
            return some (GreenNode.mkNode .field #[lbrace, nameTok, colonTok, ty, rbrace])
          | none =>
            recordError "expected '}' after constructor binder"
            return some (GreenNode.mkError "unclosed constructor binder" #[lbrace, nameTok, colonTok, ty])
        | none =>
          recordError "expected type after ':' in constructor binder"
          return some (GreenNode.mkError "missing constructor binder type" #[lbrace, nameTok, colonTok])
      else
        recordError "expected ':' in constructor binder"
        return some (GreenNode.mkError "missing ':' in constructor binder" #[lbrace, nameTok])
    | none =>
      recordError "expected binder name in constructor binder"
      return some (GreenNode.mkError "missing constructor binder name" #[lbrace])
  else
    return none

def parseDataConstructor : ParserM (Option GreenNode) := do
  let attrs ← parseAttributes
  if !attrs.isEmpty then
    let _ ← tryLayoutSep
  match ← tryConsume .pipe with
  | some pipeTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          -- Check for indexed constructor syntax: | Cons : Type
          if (← check .colon) then
            let colonTok ← consumeAny
            match ← parseType with
            | some ty =>
                return some (GreenNode.mkNode .constructorSig (attrs ++ #[pipeTok, nameTok, colonTok, ty]))
            | none =>
                recordError "expected type after ':' in constructor"
                return some (GreenNode.mkError "missing constructor type" (attrs ++ #[pipeTok, nameTok, colonTok]))
          else
            -- Lean-style constructor binders: | Err (a : Type) (b : Nat)
            let fields ← many parseConstructorBinder
            -- Check for optional return type annotation after binders
            if (← check .colon) then
              let colonTok ← consumeAny
              match ← parseType with
              | some ty =>
                return some (GreenNode.mkNode .constructorSig (attrs ++ #[pipeTok, nameTok] ++ fields ++ #[colonTok, ty]))
              | none =>
                recordError "expected type after ':' in constructor"
                return some (GreenNode.mkError "missing constructor type" (attrs ++ #[pipeTok, nameTok] ++ fields ++ #[colonTok]))
            else
              return some (GreenNode.mkNode .constructor (attrs ++ #[pipeTok, nameTok] ++ fields))
      | none =>
          recordError "expected constructor name after '|'"
          return some (GreenNode.mkError "missing constructor name" (attrs ++ #[pipeTok]))
  | none =>
      if attrs.isEmpty then return none
      recordError "expected '|' after constructor attributes"
      return some (GreenNode.mkError "missing '|' after attributes" attrs)

def parseTypeParams : ParserM (Array GreenNode) := do
  let mut params : Array GreenNode := #[]
  while true do
    -- Try parenthesized annotated parameter: (a : Type)
    if (← check .leftParen) then
      let lparen ← consumeAny
      match ← parseLowerIdent with
      | some nameTok =>
        if (← check .colon) then
          let colonTok ← consumeAny
          match ← parseType with
          | some typeTy =>
            match ← tryConsume .rightParen with
            | some rparen =>
              -- Build kinded type parameter: (a : Type)
              let paramNode := GreenNode.mkNode .tyParamKinded #[lparen, nameTok, colonTok, typeTy, rparen]
              params := params.push paramNode
            | none =>
              recordError "expected ')' after type annotation"
              break
          | none =>
            recordError "expected type after ':'"
            break
        else
          recordError "expected ':' after parameter name in annotation"
          break
      | none =>
        recordError "expected parameter name after '('"
        break
    else
      -- Try simple identifier parameter
      match ← parseLowerIdent with
      | some tok => params := params.push (GreenNode.mkNode .typeVar #[tok])
      | none => break
  return params

def parseInductiveBinders : ParserM (Array GreenNode) := do
  let mut params : Array GreenNode := #[]
  while true do
    if (← check .leftBrace) then
      let lbrace ← consumeAny
      match ← parseLowerIdent with
      | some nameTok =>
        if (← check .colon) then
          let colonTok ← consumeAny
          match ← parseType with
          | some typeTy =>
            match ← tryConsume .rightBrace with
            | some rbrace =>
              let paramNode := GreenNode.mkNode .tyParamKinded #[lbrace, nameTok, colonTok, typeTy, rbrace]
              params := params.push paramNode
            | none =>
              recordError "expected '}' after binder"
              break
          | none =>
            recordError "expected type after ':' in binder"
            break
        else
          recordError "expected ':' in implicit binder"
          break
      | none =>
        recordError "expected binder name after '{'"
        break
    else if (← check .leftParen) then
      let lparen ← consumeAny
      match ← parseLowerIdent with
      | some nameTok =>
        if (← check .colon) then
          let colonTok ← consumeAny
          match ← parseType with
          | some typeTy =>
            match ← tryConsume .rightParen with
            | some rparen =>
              let paramNode := GreenNode.mkNode .tyParamKinded #[lparen, nameTok, colonTok, typeTy, rparen]
              params := params.push paramNode
            | none =>
              recordError "expected ')' after binder"
              break
          | none =>
            recordError "expected type after ':' in binder"
            break
        else
          recordError "expected ':' in explicit binder"
          break
      | none =>
        recordError "expected binder name after '('"
        break
    else
      break
  return params

def parseInductiveDecl (attrs : Array GreenNode) : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_inductive with
  | some inductiveTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          let params ← parseInductiveBinders
          let paramList := if params.isEmpty then none
            else some (GreenNode.mkNode .tyParamList params)

          let kindAnnot ← if (← check .colon) then do
            let colonTok ← consumeAny
            match ← parseType with
            | some kindTy => pure (some (GreenNode.mkNode .signature #[colonTok, kindTy]))
            | none => recordError "expected type after ':'"; pure none
          else pure none

          -- Lean-style inductives require 'where' before constructors
          let whereTok ← tryConsume .kw_where
          if whereTok.isNone then
            recordError "expected 'where' in inductive declaration"
            let children := attrs ++ #[inductiveTok, nameTok] ++
              (match paramList with | some p => #[p] | none => #[]) ++
              (match kindAnnot with | some k => #[k] | none => #[])
            return some (GreenNode.mkError "missing 'where'" children)

          let constructors ← layoutSepBy parseDataConstructor

          -- Bodiless inductive: only allowed with @[intrinsic]
          if constructors.isEmpty && !hasBodyProvidingAttr attrs then
            recordError "bodiless inductive requires @[intrinsic] attribute"
            let children := attrs ++ #[inductiveTok, nameTok] ++
              (match paramList with | some p => #[p] | none => #[]) ++
              (match kindAnnot with | some k => #[k] | none => #[])
            return some (GreenNode.mkError "missing constructors" children)

          let children := attrs ++ #[inductiveTok, nameTok] ++
            (match paramList with | some p => #[p] | none => #[]) ++
            (match kindAnnot with | some k => #[k] | none => #[]) ++
            (match whereTok with | some w => #[w] | none => #[]) ++
            constructors
          return some (GreenNode.mkNode .declInductive children)
      | none =>
          recordError "expected type name after 'inductive'"
          return some (GreenNode.mkError "missing type name" #[inductiveTok])
  | none => return none

def parseStructDecl (attrs : Array GreenNode) : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_struct with
  | some recordTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          let params ← parseInductiveBinders
          let paramList := if params.isEmpty then #[]
            else #[GreenNode.mkNode .tyParamList params]
          match ← tryConsume .kw_where with
          | some whereTok =>
              let fields ← layoutSepBy parseConstructorField
              let children := attrs ++ #[recordTok, nameTok] ++ paramList ++ #[whereTok] ++ fields
              return some (GreenNode.mkNode .declStruct children)
          | none =>
              -- Bodiless record: only allowed with @[intrinsic]
              if hasBodyProvidingAttr attrs then
                let children := attrs ++ #[recordTok, nameTok] ++ paramList
                return some (GreenNode.mkNode .declStruct children)
              recordError "expected 'where' in record declaration"
              return some (GreenNode.mkError "missing 'where'" (attrs ++ #[recordTok, nameTok] ++ paramList))
      | none =>
          recordError "expected record name after 'record'"
          return some (GreenNode.mkError "missing record name" #[recordTok])
  | none => return none

def parseTraitMethod : ParserM (Option GreenNode) := do
  while (← check .layoutSep) do advance
  let nameNode? ←
    if (← check .leftBrace) then
      parseOperatorName
    else
      match ← parseIdent with
      | some nameTok => pure (some (GreenNode.mkNode .name #[nameTok]))
      | none => pure none

  match nameNode? with
  | some nameNode =>
      if (← check .colon) then
        let colonTok ← consumeAny
        match ← parseType with
        | some ty =>
            let sig := GreenNode.mkNode .signature #[colonTok, ty]
            return some (GreenNode.mkNode .traitMethod #[nameNode, sig])
        | none =>
            recordError "expected type after ':' in trait method"
            return some (GreenNode.mkError "missing method signature" #[nameNode, colonTok])
      else
        recordError "expected ':' and type in trait method"
        return some (GreenNode.mkError "missing method signature" #[nameNode])
  | none => return none

def parseTraitDecl (attrs : Array GreenNode) : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_trait with
  | some traitTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          -- Parse type parameters
          let mut params : Array GreenNode := #[]
          while true do
            match ← parseForallBinder with
            | some binder =>
                if binder.syntaxKind? == some .typeVar then
                  recordError "class type parameters require explicit kind annotation, e.g., '(a : Type)'"
                params := params.push binder
            | none => break

          let constraints ← if (← check .kw_with) then do
            let withTok ← consumeAny
            match ← parseConstraints with
            | some cs => pure (some (GreenNode.mkNode .constraintList #[withTok, cs]))
            | none => pure none
          else pure none

          match ← tryConsume .kw_where with
          | some whereTok =>
              let methods ← layoutSepBy parseTraitMethod

              let paramList := if params.isEmpty then #[]
                else #[GreenNode.mkNode .tyParamList params]
              let children := attrs ++ #[traitTok, nameTok] ++ paramList ++
                (match constraints with | some c => #[c] | none => #[]) ++
                #[whereTok] ++ methods
              return some (GreenNode.mkNode .declTrait children)
          | none =>
              recordError "expected 'where' in trait declaration"
              return some (GreenNode.mkError "missing 'where'" #[traitTok, nameTok])
      | none =>
          recordError "expected trait name after 'trait'"
          return some (GreenNode.mkError "missing trait name" #[traitTok])
  | none => return none

def parseInstanceDecl (attrs : Array GreenNode) : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_instance with
  | some instanceTok =>
      let instanceName ← do
        let tok ← current
        let next ← peekNext
        if (tok.kind == some .lowerIdent) &&
           (next.kind == some .colon || next.kind == some .leftBrace) then
          let nameTok ← consumeAny
          pure (some nameTok)
        else
          pure none

      let mut binders : Array GreenNode := #[]
      let mut parsing := true
      while parsing do
        if (← checkDoubleBrace) then
          -- Parse {{d : ClassName args}} or {{ClassName args}}
          let lbrace1 ← consumeAny
          let lbrace2 ← consumeAny
          -- Check for named dict: lowerIdent followed by `:`
          let dictNode ← do
            let tok ← current
            let next ← peekNext
            if tok.kind == some .lowerIdent && next.kind == some .colon then
              -- Named: {{d : Display a}}
              let nameTok ← consumeAny
              let colonTok ← consumeAny
              match ← parseConstraint with
              | some constraintNode =>
                match ← tryConsume .rightBrace with
                | some rbrace1 =>
                  match ← tryConsume .rightBrace with
                  | some rbrace2 =>
                    pure (GreenNode.mkNode .instDictBinder
                      #[lbrace1, lbrace2, nameTok, colonTok, constraintNode, rbrace1, rbrace2])
                  | none =>
                    recordError "expected '}}' after instance dict binder"
                    pure (GreenNode.mkError "unclosed dict binder"
                      #[lbrace1, lbrace2, nameTok, colonTok, constraintNode, rbrace1])
                | none =>
                  recordError "expected '}}' after instance dict binder"
                  pure (GreenNode.mkError "unclosed dict binder"
                    #[lbrace1, lbrace2, nameTok, colonTok, constraintNode])
              | none =>
                recordError "expected constraint after ':' in instance dict binder"
                pure (GreenNode.mkError "missing constraint"
                  #[lbrace1, lbrace2, nameTok, colonTok])
            else
              -- Unnamed: {{Display a}}
              match ← parseConstraint with
              | some constraintNode =>
                match ← tryConsume .rightBrace with
                | some rbrace1 =>
                  match ← tryConsume .rightBrace with
                  | some rbrace2 =>
                    pure (GreenNode.mkNode .instDictBinder
                      #[lbrace1, lbrace2, constraintNode, rbrace1, rbrace2])
                  | none =>
                    recordError "expected '}}' after instance dict binder"
                    pure (GreenNode.mkError "unclosed dict binder"
                      #[lbrace1, lbrace2, constraintNode, rbrace1])
                | none =>
                  recordError "expected '}}' after instance dict binder"
                  pure (GreenNode.mkError "unclosed dict binder"
                    #[lbrace1, lbrace2, constraintNode])
              | none =>
                recordError "expected constraint in instance dict binder"
                pure (GreenNode.mkError "missing constraint" #[lbrace1, lbrace2])
          binders := binders.push dictNode
        else if (← check .leftBrace) then
          -- Parse {a : Type} — implicit type variable binder
          let lbrace ← consumeAny
          match ← parseLowerIdent with
          | some nameTok =>
            if (← check .colon) then
              let colonTok ← consumeAny
              match ← parseType with
              | some kindTy =>
                match ← tryConsume .rightBrace with
                | some rbrace =>
                  let binderNode := GreenNode.mkNode .instTypeVarBinder
                    #[lbrace, nameTok, colonTok, kindTy, rbrace]
                  binders := binders.push binderNode
                | none =>
                  recordError "expected '}' after type variable binder"
                  parsing := false
              | none =>
                recordError "expected type after ':' in binder"
                parsing := false
            else
              recordError "expected ':' in implicit type binder"
              parsing := false
          | none =>
            recordError "expected binder name after '{'"
            parsing := false
        else
          parsing := false

      -- Step 3: Expect `:` then trait application (constraint)
      let colonTok ← tryConsume .colon
      let traitApp ← match ← parseConstraint with
        | some trait => pure trait
        | none =>
          recordError "expected trait application after ':'"
          pure (GreenNode.mkError "missing trait" #[])

      -- Step 4: Optional `where` and method definitions
      let whereTok ← tryConsume .kw_where

      let parseInstanceMethod : ParserM (Option GreenNode) := do
        let attrs ← parseAttributes
        let _ ← tryLayoutSep
        parseDefDecl attrs

      let methods ← layoutSepBy parseInstanceMethod

      -- Bodiless instance: only allowed with @[intrinsic]
      if methods.isEmpty && whereTok.isNone && !hasBodyProvidingAttr attrs then
        recordError "bodiless instance requires @[intrinsic] attribute"
        let children := attrs ++ #[instanceTok] ++
          (match instanceName with | some n => #[n] | none => #[]) ++
          binders ++
          (match colonTok with | some c => #[c] | none => #[]) ++
          #[traitApp]
        return some (GreenNode.mkError "missing methods" children)

      let children := attrs ++ #[instanceTok] ++
        (match instanceName with | some n => #[n] | none => #[]) ++
        binders ++
        (match colonTok with | some c => #[c] | none => #[]) ++
        #[traitApp] ++
        (match whereTok with | some w => #[w] | none => #[]) ++
        methods
      return some (GreenNode.mkNode .declInstance children)
  | none => return none

def parseImportPath : ParserM (Option GreenNode) := do
  let mut segments : Array GreenNode := #[]
  match ← parseLowerIdent with
  | some first =>
      segments := segments.push first
      while (← check .doubleColon) do
        let next ← peekNext
        match next.kind with
        | some .lowerIdent | some .upperIdent =>
          let colonTok ← consumeAny
          segments := segments.push colonTok
          match ← parseLowerIdent with
          | some seg => segments := segments.push seg
          | none => recordError "expected path segment after '::'"; break
        | _ => break
      return some (GreenNode.mkNode .importPath segments)
  | none => return none

def parseImportItem : ParserM (Option GreenNode) := do
  if (← check .lowerIdent) || (← check .upperIdent) then
    let tok ← consumeAny
    return some (GreenNode.mkNode .name #[tok])
  else if (← check .varSymbol) then
    let tok ← consumeAny
    return some (GreenNode.mkNode .operatorName #[tok])
  else
    return none

def parseImportItems : ParserM (Option GreenNode) := do
  if !(← check .leftBrace) then return none
  let (lbrace, items, rbrace) ← delimitedSepBy .leftBrace .rightBrace .comma parseImportItem .importItems
  return some (GreenNode.mkNode .importItems (#[lbrace] ++ items ++ #[rbrace]))

/-- Parse `use` or `pub use` declaration -/
def parseUseDecl (pubTok : Option GreenNode := none) : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_use with
  | some useTok =>
      let toks := match pubTok with | some p => #[p, useTok] | none => #[useTok]
      match ← parseImportPath with
      | some path =>
          if (← check .doubleColon) then
            let colonTok ← consumeAny
            match ← parseImportItems with
            | some items =>
                return some (GreenNode.mkNode .declUse (toks ++ #[path, colonTok, items]))
            | none =>
                recordError "expected '{' after '::'"
                return some (GreenNode.mkError "missing import items" (toks ++ #[path, colonTok]))
          else
            return some (GreenNode.mkNode .declUse (toks ++ #[path]))
      | none =>
          recordError "expected import path after 'use'"
          return some (GreenNode.mkError "missing import path" toks)
  | none => return none

def parseAbbrevDecl : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_abbrev with
  | some abbrevTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          -- Parse optional type parameters
          let params ← parseTypeParams

          match ← tryConsume .equals with
          | some eqTok =>
              match ← parseType with
              | some ty =>
                  let paramList := if params.isEmpty then #[]
                    else #[GreenNode.mkNode .tyParamList params]
                  let children := #[abbrevTok, nameTok] ++ paramList ++ #[eqTok, ty]
                  return some (GreenNode.mkNode .declAbbrev children)
              | none =>
                  recordError "expected type after '='"
                  return some (GreenNode.mkError "missing type" #[abbrevTok, nameTok, eqTok])
          | none =>
              recordError "expected '=' in abbreviation declaration"
              return some (GreenNode.mkError "missing '='" #[abbrevTok, nameTok])
      | none =>
          recordError "expected type name after 'abbrev'"
          return some (GreenNode.mkError "missing type name" #[abbrevTok])
  | none => return none

partial def parseDecl : ParserM (Option GreenNode) := do
  let attrs ← parseAttributes

  if (← check .kw_def) then parseDefDecl attrs
  else if (← check .kw_inductive) then parseInductiveDecl attrs
  else if (← check .kw_struct) then parseStructDecl attrs
  else if (← check .kw_trait) then parseTraitDecl attrs
  else if (← check .kw_instance) then parseInstanceDecl attrs
  else if (← check .kw_use) then parseUseDecl
  else if (← check .kw_pub) then do
    let pubTok ← consumeAny
    if (← check .kw_use) then parseUseDecl (some pubTok)
    else
      recordError "expected 'use' after 'pub'"
      return some (GreenNode.mkError "expected 'use' after 'pub'" #[pubTok])
  else if (← check .kw_abbrev) then parseAbbrevDecl
  else return none

def parseSourceFile : ParserM GreenNode := do
  let mut decls : Array GreenNode := #[]

  while (← checkAny #[.layoutStart, .layoutSep, .layoutEnd]) do advance

  while !(← atEnd) do
    match ← parseDecl with
    | some decl => decls := decls.push decl
    | none =>
        let tok ← current
        if tok.kind == some .eof then
          -- Consume the EOF token to include its trailing trivia in the tree
          let eofNode ← consumeAny
          decls := decls.push eofNode
          break
        else if tok.kind == some .layoutEnd || tok.kind == some .layoutSep || tok.kind == some .layoutStart then advance
        else
          recordError s!"unexpected token: {tok.kind.map (·.describe) |>.getD "unknown"}"
          let skipped ← skipToSync
          if !skipped.isEmpty then
            decls := decls.push (GreenNode.mkError "unexpected tokens" skipped)

  return GreenNode.mkNode .sourceFile decls

end Soma.Syntax.Parse

namespace Soma.Syntax

/-- Parse source code into a green tree -/
def parseGreen (tokens : Array GreenNode) (source : SourceFile) : GreenNode × Diagnostics :=
  parseGreenWith Parse.parseSourceFile tokens source

/-- Full parsing pipeline: lex + parse -/
def parse (source : SourceFile) : GreenNode × Diagnostics :=
  parseWith Parse.parseSourceFile source

/-- Parse and wrap in a red tree with stable NodeIds -/
def parseToTree (source : SourceFile) : ParsedTree × Diagnostics :=
  parseToTreeWith Parse.parseSourceFile source

/-- Reparse with an old tree, preserving NodeIds where possible -/
def reparseToTree (oldTree : ParsedTree) (source : SourceFile) : ParsedTree × Diagnostics :=
  reparseToTreeWith Parse.parseSourceFile oldTree source

end Soma.Syntax
