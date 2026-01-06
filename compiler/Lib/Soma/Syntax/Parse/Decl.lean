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
              match ← tryConsume .rightBracket with
              | some rbracket =>
                  return some (GreenNode.mkNode .attribute #[atTok, lbracket, nameTok, rbracket])
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
  attrs.any fun attr =>
    -- Attribute structure: @[name] -> children are [@, [, name, ]]
    -- The name token is at index 2
    if attr.syntaxKind? == some .attribute then
      let children := attr.children
      if h : 2 < children.size then
        match children[2].text? with
        | some "intrinsic" => true
        | some "extern" => true
        | _ => false
      else false
    else false

partial def parseDefClause : ParserM (Option GreenNode) := do
  match ← tryConsume .pipe with
  | some pipeTok =>
      let mut patterns : Array GreenNode := #[]
      while true do
        match ← parsePattern with
        | some pat => patterns := patterns.push pat
        | none => break
        let tok ← current
        if tok.kind == some .fatArrow || tok.kind == some .equals then break

      if patterns.isEmpty then
        recordError "expected pattern after '|'"
        return some (GreenNode.mkError "missing pattern" #[pipeTok])

      let tok ← current
      if tok.kind == some .fatArrow || tok.kind == some .equals then
        let arrowTok ← consumeAny
        match ← inLayout parseExpr with
        | some body =>
            return some (GreenNode.mkNode .defClause (#[pipeTok] ++ patterns ++ #[arrowTok, body]))
        | none =>
            recordError "expected expression after '=>'"
            return some (GreenNode.mkError "missing clause body" (#[pipeTok] ++ patterns))
      else
        recordError "expected '=>' after patterns"
        return some (GreenNode.mkError "missing '=>'" (#[pipeTok] ++ patterns))
  | none => return none

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

      let params ← if (← check .leftParen) then do
        let lparen ← consumeAny
        let mut paramNodes : Array GreenNode := #[]
        if !(← check .rightParen) then
          repeat do
            match ← parseLowerIdent with
            | some nameTok =>
                match ← tryConsume .colon with
                | some colonTok =>
                    match ← parseType with
                    | some ty =>
                        paramNodes := paramNodes.push (GreenNode.mkNode .field #[nameTok, colonTok, ty])
                    | none =>
                        recordError "expected type after ':'"
                        paramNodes := paramNodes.push (GreenNode.mkError "missing type" #[nameTok, colonTok])
                | none =>
                    paramNodes := paramNodes.push (GreenNode.mkNode .patVar #[nameTok])
            | none =>
                recordError "expected parameter name"
                break
            if !(← check .comma) then break
            let comma ← consumeAny
            paramNodes := paramNodes.push comma
        match ← tryConsume .rightParen with
        | some rparen =>
            pure (some (GreenNode.mkNode .paramList (#[lparen] ++ paramNodes ++ #[rparen])))
        | none =>
            recordError "unclosed parameter list"
            pure (some (GreenNode.mkError "unclosed parameters" (#[lparen] ++ paramNodes)))
      else pure none

      let returnType ← if (← check .arrow) then do
        let arrowTok ← consumeAny
        match ← parseType with
        | some ty => pure (some (GreenNode.mkNode .signature #[arrowTok, ty]))
        | none => recordError "expected return type after '->'"; pure none
      else pure none

      let signature ← if (← check .doubleColon) then parseTypeSignature else pure none

      if (← check .equals) then
        let eqTok ← consumeAny
        match ← inLayout parseExpr with
        | some body =>
            let children := attrs ++ #[defTok, nameNode] ++
              (match params with | some p => #[p] | none => #[]) ++
              (match returnType with | some r => #[r] | none => #[]) ++
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
          (match returnType with | some r => #[r] | none => #[]) ++
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
          recordError "expected '=', '|', or '::' after function name"
          return some (GreenNode.mkError "incomplete definition" (attrs ++ #[defTok, nameNode]))
  | none => return none

def parseConstructorField : ParserM (Option GreenNode) := do
  match ← parseLowerIdent with
  | some nameTok =>
      match ← tryConsume .doubleColon with
      | some colonTok =>
          match ← parseType with
          | some ty => return some (GreenNode.mkNode .field #[nameTok, colonTok, ty])
          | none =>
              recordError "expected type after '::'"
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

def parseDataConstructor : ParserM (Option GreenNode) := do
  match ← tryConsume .pipe with
  | some pipeTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          -- Check for indexed constructor syntax: | Cons :: Type
          if (← check .doubleColon) then
            let colonTok ← consumeAny
            match ← parseType with
            | some ty =>
                return some (GreenNode.mkNode .constructorSig #[pipeTok, nameTok, colonTok, ty])
            | none =>
                recordError "expected type after '::' in constructor"
                return some (GreenNode.mkError "missing constructor type" #[pipeTok, nameTok, colonTok])
          else
            -- Check if fields are in a layout block (record-style with named fields)
            -- or inline (positional style like `| Just a b`)
            let fields ← if (← check .layoutStart) then
              -- Record-style: fields separated by layoutSep
              layoutSepBy parseConstructorField
            else
              -- Positional style: fields on same line
              many parseConstructorField
            return some (GreenNode.mkNode .constructor (#[pipeTok, nameTok] ++ fields))
      | none =>
          recordError "expected constructor name after '|'"
          return some (GreenNode.mkError "missing constructor name" #[pipeTok])
  | none => return none

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

def parseDataDecl (attrs : Array GreenNode) : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_data with
  | some dataTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          let params ← parseTypeParams
          let paramList := if params.isEmpty then none
            else some (GreenNode.mkNode .tyParamList params)

          let kindAnnot ← if (← check .doubleColon) then do
            let colonTok ← consumeAny
            match ← parseKind with
            | some kindTy => pure (some (GreenNode.mkNode .signature #[colonTok, kindTy]))
            | none => recordError "expected kind after '::'"; pure none
          else pure none

          -- Check for 'where' keyword (indexed data types)
          let whereTok ← tryConsume .kw_where

          let constructors ← layoutSepBy parseDataConstructor

          -- Bodiless data: only allowed with @[intrinsic]
          if constructors.isEmpty && !hasBodyProvidingAttr attrs then
            recordError "bodiless data requires @[intrinsic] attribute"
            let children := attrs ++ #[dataTok, nameTok] ++
              (match paramList with | some p => #[p] | none => #[]) ++
              (match kindAnnot with | some k => #[k] | none => #[])
            return some (GreenNode.mkError "missing constructors" children)

          let children := attrs ++ #[dataTok, nameTok] ++
            (match paramList with | some p => #[p] | none => #[]) ++
            (match kindAnnot with | some k => #[k] | none => #[]) ++
            (match whereTok with | some w => #[w] | none => #[]) ++
            constructors
          return some (GreenNode.mkNode .declData children)
      | none =>
          recordError "expected type name after 'data'"
          return some (GreenNode.mkError "missing type name" #[dataTok])
  | none => return none

def parseStructDecl : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_struct with
  | some structTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          let params ← parseTypeParams
          match ← tryConsume .equals with
          | some eqTok =>
              match ← parseUpperIdent with
              | some conTok =>
                  -- Parse fields: either layout block (indented) or inline
                  let fields ← if (← check .layoutStart) then
                    layoutSepBy parseConstructorField
                  else
                    -- Positional style on same line
                    many parseConstructorField
                  let paramList := if params.isEmpty then #[]
                    else #[GreenNode.mkNode .tyParamList params]
                  let children := #[structTok, nameTok] ++ paramList ++ #[eqTok, conTok] ++ fields
                  return some (GreenNode.mkNode .declStruct children)
              | none =>
                  recordError "expected constructor name after '='"
                  return some (GreenNode.mkError "missing constructor" #[structTok, nameTok, eqTok])
          | none =>
              recordError "expected '=' in struct declaration"
              return some (GreenNode.mkError "missing '='" #[structTok, nameTok])
      | none =>
          recordError "expected struct name after 'struct'"
          return some (GreenNode.mkError "missing struct name" #[structTok])
  | none => return none

def parseTraitMethod : ParserM (Option GreenNode) := do
  while (← check .layoutSep) do advance
  match ← tryConsume .kw_def with
  | some defTok =>
      let nameNode ← if (← check .leftBrace) then
        match ← parseOperatorName with
        | some op => pure op
        | none => pure (GreenNode.mkError "missing name" #[defTok])
      else
        match ← parseIdent with
        | some nameTok => pure (GreenNode.mkNode .name #[nameTok])
        | none => pure (.missing .name)

      match ← parseTypeSignature with
      | some sig => return some (GreenNode.mkNode .traitMethod #[defTok, nameNode, sig])
      | none =>
          recordError "expected '::' and type in trait method"
          return some (GreenNode.mkError "missing method signature" #[defTok, nameNode])
  | none => return none

def parseTraitDecl : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_trait with
  | some traitTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          -- Parse type parameters, supporting both simple vars and kinded vars like (f :: * -> *)
          let mut params : Array GreenNode := #[]
          while true do
            match ← parseForallBinder with
            | some binder => params := params.push binder
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
              let children := #[traitTok, nameTok] ++ paramList ++
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
      -- Check for named instance: `instance myName : TraitName Type where ...`
      -- vs unnamed instance: `instance TraitName Type where ...`
      -- We look ahead to see if we have `lowerIdent :` pattern
      let (instanceName, traitApp) ← do
        -- Try to parse an identifier followed by colon (named instance)
        match ← parseLowerIdent with
        | some nameTok =>
            match ← tryConsume .colon with
            | some colonTok =>
                -- Named instance: `instance myName : TraitName ...`
                let nameNode := GreenNode.mkNode .name #[nameTok, colonTok]
                match ← parseConstraint with
                | some trait => pure (some nameNode, trait)
                | none =>
                    recordError "expected trait application after ':'"
                    pure (some nameNode, GreenNode.mkError "missing trait" #[])
            | none =>
                -- No colon - this identifier is actually the start of the trait name
                -- Need to build the constraint from this token + rest
                let className := GreenNode.mkNode .typeCon #[nameTok]
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
                pure (none, GreenNode.mkNode .constraint args)
        | none =>
            -- Try upper ident for unnamed instance starting with UpperCase trait name
            match ← parseConstraint with
            | some trait => pure (none, trait)
            | none =>
                recordError "expected trait application after 'instance'"
                pure (none, GreenNode.mkError "missing trait" #[])

      let constraints ← if (← check .kw_with) then do
        let withTok ← consumeAny
        match ← parseConstraints with
        | some cs => pure (some (GreenNode.mkNode .constraintList #[withTok, cs]))
        | none => pure none
      else pure none

      let whereTok ← tryConsume .kw_where

      let parseInstanceMethod : ParserM (Option GreenNode) := do
        let attrs ← parseAttributes
        -- Skip layoutSep between attributes and def (when attribute is on separate line)
        let _ ← tryLayoutSep
        parseDefDecl attrs

      let methods ← layoutSepBy parseInstanceMethod

      -- Bodiless instance: only allowed with @[intrinsic]
      if methods.isEmpty && whereTok.isNone && !hasBodyProvidingAttr attrs then
        recordError "bodiless instance requires @[intrinsic] attribute"
        let children := attrs ++ #[instanceTok] ++
          (match instanceName with | some n => #[n] | none => #[]) ++
          #[traitApp] ++
          (match constraints with | some c => #[c] | none => #[])
        return some (GreenNode.mkError "missing methods" children)

      let children := attrs ++ #[instanceTok] ++
        (match instanceName with | some n => #[n] | none => #[]) ++
        #[traitApp] ++
        (match constraints with | some c => #[c] | none => #[]) ++
        (match whereTok with | some w => #[w] | none => #[]) ++
        methods
      return some (GreenNode.mkNode .declInstance children)
  | none => return none

def parseImportPath : ParserM (Option GreenNode) := do
  let mut segments : Array GreenNode := #[]
  match ← parseLowerIdent with
  | some first =>
      segments := segments.push first
      while (← check .slash) do
        let slashTok ← consumeAny
        segments := segments.push slashTok
        match ← parseLowerIdent with
        | some seg => segments := segments.push seg
        | none => recordError "expected path segment after '/'"; break
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

def parseUseDecl : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_use with
  | some useTok =>
      match ← parseImportPath with
      | some path =>
          if (← checkDot) then
            let dotTok ← consumeAny
            match ← parseImportItems with
            | some items =>
                return some (GreenNode.mkNode .declUse #[useTok, path, dotTok, items])
            | none =>
                recordError "expected '{' after '.'"
                return some (GreenNode.mkError "missing import items" #[useTok, path, dotTok])
          else
            return some (GreenNode.mkNode .declUse #[useTok, path])
      | none =>
          recordError "expected import path after 'use'"
          return some (GreenNode.mkError "missing import path" #[useTok])
  | none => return none

def parseExportDecl : ParserM (Option GreenNode) := do
  match ← tryConsume .kw_export with
  | some exportTok =>
      match ← parseImportItems with
      | some items =>
          return some (GreenNode.mkNode .declExport #[exportTok, items])
      | none =>
          recordError "expected '{' after 'export'"
          return some (GreenNode.mkError "missing export items" #[exportTok])
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
  else if (← check .kw_data) then parseDataDecl attrs
  else if (← check .kw_struct) then parseStructDecl
  else if (← check .kw_trait) then parseTraitDecl
  else if (← check .kw_instance) then parseInstanceDecl attrs
  else if (← check .kw_use) then parseUseDecl
  else if (← check .kw_export) then parseExportDecl
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
