import Soma.Syntax.Parser
import Soma.Syntax.Parse.Pattern
import Soma.Syntax.Parse.Type
import Soma.Syntax.Parse.Expr

namespace Soma.Syntax.Parse

open ParserM

/-- Parse a single attribute: @[name] or @[name args] -/
def parseAttribute : ParserM (Option SyntaxNode) := do
  match ← tryConsume .at with
  | some atTok =>
      match ← tryConsume .leftBracket with
      | some lbracket =>
          match ← parseLowerIdent with
          | some nameTok =>
              -- Could have arguments, but for now just parse the name
              match ← tryConsume .rightBracket with
              | some rbracket =>
                  let span := Span.merge atTok.span rbracket.span
                  return some (mkNodeSpan .attribute #[mkToken atTok, mkToken lbracket, mkToken nameTok, mkToken rbracket] span)
              | none =>
                  recordError "expected ']' after attribute"
                  return some (mkError atTok.span "unclosed attribute" #[mkToken atTok, mkToken lbracket, mkToken nameTok])
          | none =>
              recordError "expected attribute name"
              return some (mkError atTok.span "missing attribute name" #[mkToken atTok, mkToken lbracket])
      | none =>
          recordError "expected '[' after '@'"
          return some (mkError atTok.span "malformed attribute" #[mkToken atTok])
  | none => return none

/-- Parse a list of attributes -/
def parseAttributes : ParserM (Array SyntaxNode) := do
  let mut attrs : Array SyntaxNode := #[]
  while (← check .at) do
    match ← parseAttribute with
    | some attr => attrs := attrs.push attr
    | none => break
  return attrs

/-! ## Definition Clauses -/

/-- Parse a definition clause: | pat1 pat2 => body -/
partial def parseDefClause : ParserM (Option SyntaxNode) := do
  match ← tryConsume .pipe with
  | some pipeTok =>
      -- Parse patterns
      let mut patterns : Array SyntaxNode := #[]
      while true do
        match ← parsePattern with
        | some pat => patterns := patterns.push pat
        | none => break
        let tok ← current
        if tok.kind == .fatArrow || tok.kind == .equals then break

      if patterns.isEmpty then
        recordError "expected pattern after '|'"
        return some (mkError pipeTok.span "missing pattern" #[mkToken pipeTok])

      -- Expect => or =
      let arrowTok ← current
      if arrowTok.kind == .fatArrow || arrowTok.kind == .equals then
        advance
        -- Handle layout block for multi-line clause bodies
        -- The body might start on the next line with a layoutStart token
        let _ ← tryLayoutStart
        skipLayoutSep
        match ← parseExpr with
        | some body =>
            let _ ← tryLayoutEnd
            let span := Span.merge pipeTok.span body.span
            return some (mkNodeSpan .defClause (#[mkToken pipeTok] ++ patterns ++ #[mkToken arrowTok, body]) span)
        | none =>
            let _ ← tryLayoutEnd
            recordError "expected expression after '=>'"
            let lastPat := patterns[patterns.size - 1]!
            return some (mkError (Span.merge pipeTok.span lastPat.span) "missing clause body" (#[mkToken pipeTok] ++ patterns))
      else
        recordError "expected '=>' after patterns"
        let lastPat := patterns[patterns.size - 1]!
        return some (mkError (Span.merge pipeTok.span lastPat.span) "missing '=>'" (#[mkToken pipeTok] ++ patterns))

  | none => return none

/--
Parse a def declaration:
  def name :: Type
  def name(params) -> RetType = body
  def name :: Type | pat => body | pat => body
  def name | pat => body
-/
partial def parseDefDecl (attrs : Array SyntaxNode) : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_def with
  | some defTok =>
      -- Parse name (could be operator in braces)
      let nameNode ← if (← check .leftBrace) then do
        match ← parseOperatorName with
        | some op => pure op
        | none =>
            recordError "expected operator name"
            pure (mkError defTok.span "missing name" #[mkToken defTok])
      else
        match ← parseIdent with
        | some nameTok => pure (mkNodeSpan .name #[mkToken nameTok] nameTok.span)
        | none =>
            recordError "expected function name after 'def'"
            pure (mkMissing .name (← currentLoc))

      -- Check for inline parameters: def foo(x: Int, y: String) -> RetType
      let params ← if (← check .leftParen) then do
        let lparen ← consumeAny
        let mut paramNodes : Array SyntaxNode := #[]
        -- Parse comma-separated typed parameters
        if !(← check .rightParen) then
          repeat do
            match ← parseLowerIdent with
            | some nameTok =>
                match ← tryConsume .colon with
                | some colonTok =>
                    match ← parseType with
                    | some ty =>
                        let span := Span.merge nameTok.span ty.span
                        paramNodes := paramNodes.push (mkNodeSpan .field #[mkToken nameTok, mkToken colonTok, ty] span)
                    | none =>
                        recordError "expected type after ':'"
                        paramNodes := paramNodes.push (mkError nameTok.span "missing type" #[mkToken nameTok, mkToken colonTok])
                | none =>
                    -- Parameter without type annotation
                    paramNodes := paramNodes.push (mkNodeSpan .patVar #[mkToken nameTok] nameTok.span)
            | none =>
                recordError "expected parameter name"
                break
            if !(← check .comma) then break
            advance -- consume comma
        match ← tryConsume .rightParen with
        | some rparen =>
            let span := Span.merge lparen.span rparen.span
            pure (some (mkNodeSpan .paramList (#[mkToken lparen] ++ paramNodes ++ #[mkToken rparen]) span))
        | none =>
            recordRichError "unclosed parameter list"
              (← current).span
              (secondary := #[(lparen.span, "opening '(' is here")])
              (help := "add ')' to close the parameter list")
            pure (some (mkError lparen.span "unclosed parameters" (#[mkToken lparen] ++ paramNodes)))
      else
        pure none

      -- Check for return type annotation: -> Type
      let returnType ← if (← check .arrow) then do
        let arrowTok ← consumeAny
        match ← parseType with
        | some ty =>
            let span := Span.merge arrowTok.span ty.span
            pure (some (mkNodeSpan .signature #[mkToken arrowTok, ty] span))
        | none =>
            recordError "expected return type after '->'"
            pure none
      else
        pure none

      -- Check for type signature: :: Type
      let signature ← if (← check .doubleColon) then
        parseTypeSignature
      else
        pure none

      -- Now either = expr or | clauses
      skipLayoutSep
      let _ ← tryLayoutStart

      if (← check .equals) then
        -- Single body: def name = expr
        let eqTok ← consumeAny
        match ← parseExpr with
        | some body =>
            let _ ← tryLayoutEnd
            let span := Span.merge defTok.span body.span
            let children := attrs ++ #[mkToken defTok, nameNode] ++
              (match params with | some p => #[p] | none => #[]) ++
              (match returnType with | some r => #[r] | none => #[]) ++
              (match signature with | some s => #[s] | none => #[]) ++
              #[mkToken eqTok, body]
            return some (mkNodeSpan .declDef children span)
        | none =>
            let _ ← tryLayoutEnd
            let curTok ← current
            recordRichError "expected expression after '='"
              curTok.span
              (secondary := #[(eqTok.span, "'=' is here")])
              (notes := #["the right-hand side of a definition must be an expression"])
              (help := "provide an expression, e.g., `def foo = 42`")
            return some (mkError defTok.span "missing definition body" (attrs ++ #[mkToken defTok, nameNode]))

      else if (← check .pipe) then
        -- Pattern clauses: def name | pat => body
        let mut clauses : Array SyntaxNode := #[]
        while true do
          skipLayoutSep
          match ← parseDefClause with
          | some clause => clauses := clauses.push clause
          | none => break

        let _ ← tryLayoutEnd

        if clauses.isEmpty then
          recordError "expected definition clauses"

        let lastSpan := if clauses.isEmpty then nameNode.span else clauses[clauses.size - 1]!.span
        let span := Span.merge defTok.span lastSpan
        let children := attrs ++ #[mkToken defTok, nameNode] ++
          (match params with | some p => #[p] | none => #[]) ++
          (match returnType with | some r => #[r] | none => #[]) ++
          (match signature with | some s => #[s] | none => #[]) ++
          clauses
        return some (mkNodeSpan .declDef children span)

      else
        let _ ← tryLayoutEnd
        -- Just a signature declaration: def name :: Type
        if signature.isSome then
          let span := Span.merge defTok.span signature.get!.span
          let children := attrs ++ #[mkToken defTok, nameNode, signature.get!]
          return some (mkNodeSpan .declDef children span)
        else
          recordError "expected '=', '|', or '::' after function name"
          return some (mkError defTok.span "incomplete definition" (attrs ++ #[mkToken defTok, nameNode]))

  | none => return none

/-- Parse a constructor field: name :: Type -/
def parseConstructorField : ParserM (Option SyntaxNode) := do
  match ← parseLowerIdent with
  | some nameTok =>
      match ← tryConsume .doubleColon with
      | some colonTok =>
          match ← parseType with
          | some ty =>
              let span := Span.merge nameTok.span ty.span
              return some (mkNodeSpan .field #[mkToken nameTok, mkToken colonTok, ty] span)
          | none =>
              recordError "expected type after '::'"
              return some (mkError nameTok.span "missing field type" #[mkToken nameTok, mkToken colonTok])
      | none =>
          -- Field without explicit name (positional)
          return none
  | none => return none

/-- Parse a data constructor: | ConName field1 :: T1 field2 :: T2 -/
def parseDataConstructor : ParserM (Option SyntaxNode) := do
  match ← tryConsume .pipe with
  | some pipeTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          -- Parse fields
          let _ ← tryLayoutStart
          let mut fields : Array SyntaxNode := #[]
          while true do
            skipLayoutSep
            match ← parseConstructorField with
            | some field => fields := fields.push field
            | none => break
          let _ ← tryLayoutEnd

          let lastSpan := if fields.isEmpty then nameTok.span else fields[fields.size - 1]!.span
          let span := Span.merge pipeTok.span lastSpan
          return some (mkNodeSpan .constructor (#[mkToken pipeTok, mkToken nameTok] ++ fields) span)
      | none =>
          recordError "expected constructor name after '|'"
          return some (mkError pipeTok.span "missing constructor name" #[mkToken pipeTok])
  | none => return none

/-- Parse type parameters: a b c -/
def parseTypeParams : ParserM (Array SyntaxNode) := do
  let mut params : Array SyntaxNode := #[]
  while true do
    match ← parseLowerIdent with
    | some tok =>
        params := params.push (mkNodeSpan .typeVar #[mkToken tok] tok.span)
    | none => break
  return params

/--
Parse a data declaration:
  data Option a
    | Some value :: a
    | None
-/
def parseDataDecl : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_data with
  | some dataTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          -- Parse type parameters
          let params ← parseTypeParams
          let paramList := if params.isEmpty then
            none
          else
            some (mkNodeSpan .tyParamList params (Span.merge params[0]!.span params[params.size-1]!.span))

          -- Parse constructors
          skipLayoutSep
          let _ ← tryLayoutStart
          let mut constructors : Array SyntaxNode := #[]
          while true do
            skipLayoutSep
            match ← parseDataConstructor with
            | some con => constructors := constructors.push con
            | none => break
          let _ ← tryLayoutEnd

          let lastSpan := if constructors.isEmpty then
            (match paramList with | some p => p.span | none => nameTok.span)
          else
            constructors[constructors.size - 1]!.span
          let span := Span.merge dataTok.span lastSpan
          let children := #[mkToken dataTok, mkToken nameTok] ++
            (match paramList with | some p => #[p] | none => #[]) ++
            constructors
          return some (mkNodeSpan .declData children span)
      | none =>
          recordError "expected type name after 'data'"
          return some (mkError dataTok.span "missing type name" #[mkToken dataTok])
  | none => return none

/-! ## Struct Declarations -/

/--
Parse a struct declaration:
  struct Path = Path String
-/
def parseStructDecl : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_struct with
  | some structTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          -- Parse type parameters
          let params ← parseTypeParams

          -- Expect =
          match ← tryConsume .equals with
          | some eqTok =>
              -- Parse constructor name
              match ← parseUpperIdent with
              | some conTok =>
                  -- Parse fields (types without names, or name :: type)
                  let mut fields : Array SyntaxNode := #[]
                  while true do
                    -- Try named field first
                    match ← parseConstructorField with
                    | some field => fields := fields.push field
                    | none =>
                        -- Try positional type
                        match ← parseTypeAtom with
                        | some ty => fields := fields.push ty
                        | none => break

                  let lastSpan := if fields.isEmpty then conTok.span else fields[fields.size - 1]!.span
                  let span := Span.merge structTok.span lastSpan
                  let paramList := if params.isEmpty then #[]
                    else #[mkNodeSpan .tyParamList params (Span.merge params[0]!.span params[params.size-1]!.span)]
                  let children := #[mkToken structTok, mkToken nameTok] ++
                    paramList ++
                    #[mkToken eqTok, mkToken conTok] ++
                    fields
                  return some (mkNodeSpan .declStruct children span)
              | none =>
                  recordError "expected constructor name after '='"
                  return some (mkError structTok.span "missing constructor" #[mkToken structTok, mkToken nameTok, mkToken eqTok])
          | none =>
              recordError "expected '=' in struct declaration"
              return some (mkError structTok.span "missing '='" #[mkToken structTok, mkToken nameTok])
      | none =>
          recordError "expected struct name after 'struct'"
          return some (mkError structTok.span "missing struct name" #[mkToken structTok])
  | none => return none

/-- Parse a trait method signature: def name :: Type -/
def parseTraitMethod : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_def with
  | some defTok =>
      -- Parse name
      let nameNode ← if (← check .leftBrace) then
        match ← parseOperatorName with
        | some op => pure op
        | none => pure (mkError defTok.span "missing name" #[mkToken defTok])
      else
        match ← parseIdent with
        | some nameTok => pure (mkNodeSpan .name #[mkToken nameTok] nameTok.span)
        | none => pure (mkMissing .name (← currentLoc))

      -- Expect :: Type
      match ← parseTypeSignature with
      | some sig =>
          let span := Span.merge defTok.span sig.span
          return some (mkNodeSpan .traitMethod #[mkToken defTok, nameNode, sig] span)
      | none =>
          recordError "expected '::' and type in trait method"
          return some (mkError defTok.span "missing method signature" #[mkToken defTok, nameNode])
  | none => return none

/--
Parse a trait declaration:
  trait Functor f where
    def fmap :: (a -> b) -> f a -> f b
-/
def parseTraitDecl : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_trait with
  | some traitTok =>
      match ← parseUpperIdent with
      | some nameTok =>
          -- Parse type parameters
          let params ← parseTypeParams

          -- Optional 'with' constraints
          let constraints ← if (← check .kw_with) then do
            let withTok ← consumeAny
            match ← parseConstraints with
            | some cs => pure (some (mkNodeSpan .constraintList #[mkToken withTok, cs] (Span.merge withTok.span cs.span)))
            | none => pure none
          else
            pure none

          -- Expect 'where'
          match ← tryConsume .kw_where with
          | some whereTok =>
              -- Parse methods
              let _ ← tryLayoutStart
              let mut methods : Array SyntaxNode := #[]
              while true do
                skipLayoutSep
                match ← parseTraitMethod with
                | some m => methods := methods.push m
                | none => break
              let _ ← tryLayoutEnd

              let lastSpan := if methods.isEmpty then whereTok.span else methods[methods.size - 1]!.span
              let span := Span.merge traitTok.span lastSpan
              let paramList := if params.isEmpty then #[]
                else #[mkNodeSpan .tyParamList params (Span.merge params[0]!.span params[params.size-1]!.span)]
              let children := #[mkToken traitTok, mkToken nameTok] ++
                paramList ++
                (match constraints with | some c => #[c] | none => #[]) ++
                #[mkToken whereTok] ++
                methods
              return some (mkNodeSpan .declTrait children span)
          | none =>
              recordError "expected 'where' in trait declaration"
              return some (mkError traitTok.span "missing 'where'" #[mkToken traitTok, mkToken nameTok])
      | none =>
          recordError "expected trait name after 'trait'"
          return some (mkError traitTok.span "missing trait name" #[mkToken traitTok])
  | none => return none

/--
Parse an instance declaration:
  instance Display (Option a) with (Display a) where
    def display | (Some v) => ...
-/
def parseInstanceDecl : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_instance with
  | some instanceTok =>
      -- Parse the trait application (constraint)
      match ← parseConstraint with
      | some traitApp =>
          -- Optional 'with' constraints
          let constraints ← if (← check .kw_with) then do
            let withTok ← consumeAny
            match ← parseConstraints with
            | some cs => pure (some (mkNodeSpan .constraintList #[mkToken withTok, cs] (Span.merge withTok.span cs.span)))
            | none => pure none
          else
            pure none

          -- Optional 'where' (might be implicit with layout)
          let whereTok ← tryConsume .kw_where

          -- Parse methods (same as def declarations)
          let _ ← tryLayoutStart
          let mut methods : Array SyntaxNode := #[]
          while true do
            skipLayoutSep
            let attrs ← parseAttributes
            match ← parseDefDecl attrs with
            | some m => methods := methods.push m
            | none => break
          let _ ← tryLayoutEnd

          let lastSpan := if methods.isEmpty then
            (match whereTok with | some w => w.span | none => traitApp.span)
          else
            methods[methods.size - 1]!.span
          let span := Span.merge instanceTok.span lastSpan
          let children := #[mkToken instanceTok, traitApp] ++
            (match constraints with | some c => #[c] | none => #[]) ++
            (match whereTok with | some w => #[mkToken w] | none => #[]) ++
            methods
          return some (mkNodeSpan .declInstance children span)
      | none =>
          recordError "expected trait application after 'instance'"
          return some (mkError instanceTok.span "missing trait" #[mkToken instanceTok])
  | none => return none

/-- Parse an import path: base/core -/
def parseImportPath : ParserM (Option SyntaxNode) := do
  let mut segments : Array SyntaxNode := #[]
  match ← parseLowerIdent with
  | some first =>
      segments := segments.push (mkToken first)
      while (← check .slash) do
        let slashTok ← consumeAny
        segments := segments.push (mkToken slashTok)
        match ← parseLowerIdent with
        | some seg => segments := segments.push (mkToken seg)
        | none =>
            recordError "expected path segment after '/'"
            break
      let span := Span.merge segments[0]!.span segments[segments.size - 1]!.span
      return some (mkNodeSpan .importPath segments span)
  | none => return none

/-- Parse import items: {Item1, Item2, ...} -/
def parseImportItems : ParserM (Option SyntaxNode) := do
  match ← tryConsume .leftBrace with
  | some lbrace =>
      let mut items : Array SyntaxNode := #[]
      if !(← check .rightBrace) then
        repeat do
          -- Items can be identifiers or operators
          if (← check .lowerIdent) || (← check .upperIdent) then
            let tok ← consumeAny
            items := items.push (mkNodeSpan .name #[mkToken tok] tok.span)
          else if (← check .varSymbol) then
            let tok ← consumeAny
            items := items.push (mkNodeSpan .operatorName #[mkToken tok] tok.span)
          else
            recordError "expected import item"
            break
          if !(← check .comma) then break
          advance -- consume comma

      match ← tryConsume .rightBrace with
      | some rbrace =>
          let span := Span.merge lbrace.span rbrace.span
          return some (mkNodeSpan .importItems (#[mkToken lbrace] ++ items ++ #[mkToken rbrace]) span)
      | none =>
          recordError "expected '}' after import items"
          let lastSpan := if items.isEmpty then lbrace.span else items[items.size - 1]!.span
          return some (mkError (Span.merge lbrace.span lastSpan) "unclosed import" (#[mkToken lbrace] ++ items))
  | none => return none

/--
Parse a use declaration:
  use base/core.{Option, Some, None}
-/
def parseUseDecl : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_use with
  | some useTok =>
      match ← parseImportPath with
      | some path =>
          -- Expect .{items}
          if (← checkDot) then
            let dotTok ← consumeAny
            match ← parseImportItems with
            | some items =>
                let span := Span.merge useTok.span items.span
                return some (mkNodeSpan .declUse #[mkToken useTok, path, mkToken dotTok, items] span)
            | none =>
                recordError "expected '{' after '.'"
                return some (mkError useTok.span "missing import items" #[mkToken useTok, path, mkToken dotTok])
          else
            -- Import entire module
            let span := Span.merge useTok.span path.span
            return some (mkNodeSpan .declUse #[mkToken useTok, path] span)
      | none =>
          recordError "expected import path after 'use'"
          return some (mkError useTok.span "missing import path" #[mkToken useTok])
  | none => return none

/--
Parse an export declaration:
  export { Item1, Item2, ... }
-/
def parseExportDecl : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_export with
  | some exportTok =>
      match ← parseImportItems with
      | some items =>
          let span := Span.merge exportTok.span items.span
          return some (mkNodeSpan .declExport #[mkToken exportTok, items] span)
      | none =>
          recordError "expected '{' after 'export'"
          return some (mkError exportTok.span "missing export items" #[mkToken exportTok])
  | none => return none

/-! ## Intrinsic Declarations -/

/--
Parse an intrinsic declaration:
  intrinsic def println :: a -> IO () with (Display a)
  intrinsic data IO :: * -> *
-/
partial def parseIntrinsicDecl (attrs : Array SyntaxNode) : ParserM (Option SyntaxNode) := do
  match ← tryConsume .kw_intrinsic with
  | some intrinsicTok =>
      -- Parse the inner declaration
      let inner ← if (← check .kw_def) then
        parseDefDecl attrs
      else if (← check .kw_data) then
        parseDataDecl
      else
        recordError "expected 'def' or 'data' after 'intrinsic'"
        pure none

      match inner with
      | some decl =>
          let span := Span.merge intrinsicTok.span decl.span
          return some (mkNodeSpan .declIntrinsic #[mkToken intrinsicTok, decl] span)
      | none =>
          return some (mkError intrinsicTok.span "missing intrinsic body" #[mkToken intrinsicTok])
  | none => return none

/-! ## Top-Level Parsing -/

/-- Parse a single declaration -/
partial def parseDecl : ParserM (Option SyntaxNode) := do
  skipLayoutSep
  let attrs ← parseAttributes

  -- Try each declaration type
  if (← check .kw_intrinsic) then
    parseIntrinsicDecl attrs
  else if (← check .kw_def) then
    parseDefDecl attrs
  else if (← check .kw_data) then
    parseDataDecl
  else if (← check .kw_struct) then
    parseStructDecl
  else if (← check .kw_trait) then
    parseTraitDecl
  else if (← check .kw_instance) then
    parseInstanceDecl
  else if (← check .kw_use) then
    parseUseDecl
  else if (← check .kw_export) then
    parseExportDecl
  else
    return none

/-- Parse a complete source file -/
def parseSourceFile : ParserM SyntaxNode := do
  let startLoc ← currentLoc
  let mut decls : Array SyntaxNode := #[]

  while !(← atEnd) do
    skipLayoutSep
    skipLayout
    if (← atEnd) then break

    match ← parseDecl with
    | some decl => decls := decls.push decl
    | none =>
        -- Unknown token - skip and try to recover
        let tok ← current
        if tok.kind != .eof then
          recordError s!"unexpected token: {tok.kind.describe}"
          let skipped ← skipToSync
          if !skipped.isEmpty then
            let span := Span.merge skipped[0]!.span skipped[skipped.size - 1]!.span
            decls := decls.push (mkError span "unexpected tokens" skipped)
        else
          break

  let endLoc ← currentLoc
  let span := { start := startLoc, stop := endLoc }
  return mkNodeSpan .sourceFile decls span

end Soma.Syntax.Parse
