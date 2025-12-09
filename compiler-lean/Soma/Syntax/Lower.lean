import Soma.Syntax.Source
import Soma.Syntax.Diagnostic
import Soma.Syntax.SyntaxKind
import Soma.Syntax.SyntaxNode
import Soma.Syntax.Ast

namespace Soma.Syntax

/-- Lowering state - accumulates diagnostics -/
structure LowerState where
  diagnostics : Diagnostics := #[]

/-- Lowering monad - can fail with a message, accumulates diagnostics -/
abbrev LowerM := StateT LowerState (Except String)

/-- Run the lowering monad -/
def LowerM.run' (m : LowerM α) : Except String α × Diagnostics :=
  match m.run {} with
  | .ok (result, state) => (.ok result, state.diagnostics)
  | .error msg => (.error msg, #[])

/-- Record a diagnostic -/
def recordDiag (d : Diagnostic) : LowerM Unit :=
  modify fun s => { s with diagnostics := s.diagnostics.push d }

/-- Record an error and continue -/
def lowerError (msg : String) (span : Span) : LowerM Unit :=
  recordDiag (Diagnostic.error msg span)

/-- Fail lowering with an error -/
def lowerFail (msg : String) : LowerM α :=
  throw msg

/-- Get token text from a syntax node -/
def getTokenText (node : SyntaxNode) : LowerM String :=
  match node.tokenText? with
  | some text => pure text
  | none => lowerFail s!"expected token, got {repr node}"

/-- Get the first child of a node -/
def firstChild (node : SyntaxNode) : LowerM SyntaxNode :=
  match node.child? 0 with
  | some c => pure c
  | none => lowerFail "expected at least one child"

/-- Filter non-token children (actual syntax nodes) -/
def syntaxChildren (node : SyntaxNode) : Array SyntaxNode :=
  node.children.filter fun c =>
    match c with
    | .token _ => false
    | _ => true

/-- Get children of a specific kind -/
def childrenOfKind (node : SyntaxNode) (kind : SyntaxKind) : Array SyntaxNode :=
  node.children.filter fun c => c.kind? == some kind

mutual

/-- Lower a CST pattern to AST Pattern -/
partial def lowerPattern (node : SyntaxNode) : LowerM Pattern := do
  match node with
  | .token tok =>
      match tok.kind with
      | .lowerIdent => pure (.var ⟨tok.text, tok.span⟩)
      | .underscore => pure (.wildcard tok.span)
      | .number => pure (.lit (.int tok.text.toInt! tok.span))
      | .string s => pure (.lit (.string s tok.span))
      | .true_ => pure (.lit (.bool true tok.span))
      | .false_ => pure (.lit (.bool false tok.span))
      | _ =>
          lowerError s!"unexpected token in pattern: {tok.kind}" tok.span
          pure (.wildcard tok.span)

  | .node kind _children span =>
      match kind with
      | .patVar =>
          let text ← getTokenText (← firstChild node)
          pure (.var ⟨text, span⟩)

      | .patWildcard =>
          pure (.wildcard span)

      | .patLit =>
          let child ← firstChild node
          match child with
          | .token tok =>
              match tok.kind with
              | .number => pure (.lit (.int tok.text.toInt! span))
              | .string s => pure (.lit (.string s span))
              | .true_ => pure (.lit (.bool true span))
              | .false_ => pure (.lit (.bool false span))
              | _ =>
                  lowerError s!"unexpected literal kind: {tok.kind}" span
                  pure (.wildcard span)
          | _ =>
              lowerError "expected literal token" span
              pure (.wildcard span)

      | .patCon =>
          let syntaxKids := syntaxChildren node
          if syntaxKids.isEmpty then
            lowerError "constructor pattern missing name" span
            pure (.wildcard span)
          else
            let nameTok ← firstChild syntaxKids[0]!
            let name ← getTokenText nameTok
            let args ← syntaxKids[1:].toArray.mapM lowerPattern
            pure (.con ⟨name, syntaxKids[0]!.span⟩ args span)

      | .patTuple =>
          let syntaxKids := syntaxChildren node
          let elems ← syntaxKids.mapM lowerPattern
          pure (.tuple elems span)

      | .patList =>
          let syntaxKids := syntaxChildren node
          let elems ← syntaxKids.mapM lowerPattern
          pure (.list elems span)

      | .patCons =>
          let syntaxKids := syntaxChildren node
          if syntaxKids.size >= 2 then
            let head ← lowerPattern syntaxKids[0]!
            let tail ← lowerPattern syntaxKids[1]!
            pure (.cons head tail span)
          else
            lowerError "cons pattern requires head and tail" span
            pure (.wildcard span)

      | .patParens =>
          let syntaxKids := syntaxChildren node
          if syntaxKids.isEmpty then
            pure (.tuple #[] span)
          else
            let inner ← lowerPattern syntaxKids[0]!
            pure (.parens inner span)

      | .patTyped =>
          let syntaxKids := syntaxChildren node
          if syntaxKids.size >= 2 then
            let pat ← lowerPattern syntaxKids[0]!
            let ty ← lowerTypeExpr syntaxKids[1]!
            pure (.typed pat ty span)
          else if syntaxKids.size == 1 then
            -- Just the pattern, no type (error recovery)
            lowerPattern syntaxKids[0]!
          else
            lowerError "typed pattern missing pattern and type" span
            pure (.wildcard span)

      | .name =>
          let text ← getTokenText (← firstChild node)
          if text.length > 0 && (text.get ⟨0⟩).isUpper then
            pure (.con ⟨text, span⟩ #[] span)
          else
            pure (.var ⟨text, span⟩)

      | _ =>
          lowerError s!"unexpected pattern kind: {kind}" span
          pure (.wildcard span)

  | .error span msg _ =>
      lowerError msg span
      pure (.wildcard span)

  | .missing expected loc =>
      lowerError s!"missing {expected}" (Span.point loc)
      pure (.wildcard (Span.point loc))

/-- Lower a CST type to AST TypeExpr -/
partial def lowerTypeExpr (node : SyntaxNode) : LowerM TypeExpr := do
  match node with
  | .token tok =>
      match tok.kind with
      | .lowerIdent => pure (.var ⟨tok.text, tok.span⟩)
      | .upperIdent => pure (.con ⟨tok.text, tok.span⟩)
      | _ =>
          lowerError s!"unexpected token in type: {tok.kind}" tok.span
          pure (.var ⟨"_error", tok.span⟩)

  | .node kind _children span =>
      match kind with
      | .typeVar =>
          let text ← getTokenText (← firstChild node)
          pure (.var ⟨text, span⟩)

      | .typeCon =>
          let text ← getTokenText (← firstChild node)
          pure (.con ⟨text, span⟩)

      | .typeApp =>
          let syntaxKids := syntaxChildren node
          if syntaxKids.isEmpty then
            lowerError "empty type application" span
            pure (.var ⟨"_error", span⟩)
          else
            let mut result ← lowerTypeExpr syntaxKids[0]!
            for arg in syntaxKids[1:] do
              let argTy ← lowerTypeExpr arg
              result := .app result argTy (Span.merge result.span argTy.span)
            pure result

      | .typeArrow =>
          let syntaxKids := syntaxChildren node
          if syntaxKids.size >= 2 then
            let from_ ← lowerTypeExpr syntaxKids[0]!
            let to ← lowerTypeExpr syntaxKids[1]!
            pure (.arrow from_ to span)
          else
            lowerError "arrow type requires two arguments" span
            pure (.var ⟨"_error", span⟩)

      | .typeTuple =>
          let syntaxKids := syntaxChildren node
          let elems ← syntaxKids.mapM lowerTypeExpr
          pure (.tuple elems span)

      | .typeList =>
          let syntaxKids := syntaxChildren node
          if syntaxKids.isEmpty then
            lowerError "list type requires element type" span
            pure (.var ⟨"_error", span⟩)
          else
            let elem ← lowerTypeExpr syntaxKids[0]!
            pure (.list elem span)

      | .typeForall =>
          let varNodes := childrenOfKind node .typeVar
          let bodyNodes := syntaxChildren node |>.filter fun c =>
            c.kind? != some .typeVar && c.kind? != some .tyParamList
          let vars ← varNodes.mapM fun v => do
            let text ← getTokenText (← firstChild v)
            pure ⟨text, v.span⟩
          if bodyNodes.isEmpty then
            lowerError "forall type requires body" span
            pure (.var ⟨"_error", span⟩)
          else
            let body ← lowerTypeExpr bodyNodes[0]!
            pure (.forall_ vars body span)

      | .typeConstrained =>
          let syntaxKids := syntaxChildren node
          let bodyNodes := syntaxKids.filter fun c =>
            c.kind? != some .constraintList && c.kind? != some .constraint
          let constraintNodes := childrenOfKind node .constraintList ++
                                  childrenOfKind node .constraint
          let constraints ← constraintNodes.mapM fun cn => do
            let c ← lowerConstraint cn
            pure (c.className, c.args, c.span)
          if bodyNodes.isEmpty then
            lowerError "constrained type requires body" span
            pure (.var ⟨"_error", span⟩)
          else
            let body ← lowerTypeExpr bodyNodes[0]!
            pure (.constrained constraints body span)

      | .typeParens =>
          let syntaxKids := syntaxChildren node
          if syntaxKids.isEmpty then
            pure (.tuple #[] span)
          else
            let inner ← lowerTypeExpr syntaxKids[0]!
            pure (.parens inner span)

      | .signature =>
          let syntaxKids := syntaxChildren node
          if syntaxKids.isEmpty then
            lowerError "signature missing type" span
            pure (.var ⟨"_error", span⟩)
          else
            lowerTypeExpr syntaxKids[0]!

      | _ =>
          lowerError s!"unexpected type kind: {kind}" span
          pure (.var ⟨"_error", span⟩)

  | .error span msg _ =>
      lowerError msg span
      pure (.var ⟨"_error", span⟩)

  | .missing expected loc =>
      lowerError s!"missing {expected}" (Span.point loc)
      pure (.var ⟨"_error", Span.point loc⟩)

/-- Lower a constraint node -/
partial def lowerConstraint (node : SyntaxNode) : LowerM Constraint := do
  match node with
  | .node .constraint _children span =>
      -- A constraint looks like: ClassName arg1 arg2 ...
      -- The children include the class name (typeCon or token) and type arguments
      let syntaxKids := syntaxChildren node
      if syntaxKids.isEmpty then
        -- Try to get the class name from token children
        let tokenKids := node.children.filter fun c =>
          match c with
          | .token tok => tok.kind == .upperIdent
          | _ => false
        if tokenKids.isEmpty then
          lowerError "empty constraint" span
          pure ⟨⟨"_error", span⟩, #[], span⟩
        else
          match tokenKids[0]! with
          | .token tok => pure ⟨⟨tok.text, tok.span⟩, #[], span⟩
          | _ => pure ⟨⟨"_error", span⟩, #[], span⟩
      else
        let classNode := syntaxKids[0]!
        let className ← match classNode with
        | .node .typeCon _ _ =>
            let text ← getTokenText (← firstChild classNode)
            pure ⟨text, classNode.span⟩
        | .token tok => pure ⟨tok.text, tok.span⟩
        | _ =>
            lowerError "expected class name in constraint" classNode.span
            pure ⟨"_error", classNode.span⟩
        let args ← syntaxKids[1:].toArray.mapM lowerTypeExpr
        pure ⟨className, args, span⟩

  | .node .constraintList _children span =>
      -- A constraint list can contain nested constraints or another constraint list
      let constraintNodes := childrenOfKind node .constraint
      if !constraintNodes.isEmpty then
        lowerConstraint constraintNodes[0]!
      else
        -- Check for nested constraint list (e.g., from parsing "(Semigroup a)")
        let nestedLists := childrenOfKind node .constraintList
        if !nestedLists.isEmpty then
          lowerConstraint nestedLists[0]!
        else
          -- Try to find constraint info from syntax children directly
          let syntaxKids := syntaxChildren node
          if syntaxKids.isEmpty then
            lowerError "empty constraint list" span
            pure ⟨⟨"_error", span⟩, #[], span⟩
          else
            -- The constraint list might directly contain type nodes
            lowerConstraint syntaxKids[0]!

  | .node kind _children span =>
      -- Could be a type application used as constraint: Show a
      if kind == .typeApp || kind == .typeCon || kind == .typeVar then
        let syntaxKids := syntaxChildren node
        if syntaxKids.isEmpty then
          -- Just a type constructor like Show
          match node with
          | .node .typeCon _ _ =>
              let text ← getTokenText (← firstChild node)
              pure ⟨⟨text, span⟩, #[], span⟩
          | _ =>
              lowerError "expected constraint" span
              pure ⟨⟨"_error", span⟩, #[], span⟩
        else
          let classNode := syntaxKids[0]!
          let className ← match classNode with
          | .node .typeCon _ _ =>
              let text ← getTokenText (← firstChild classNode)
              pure ⟨text, classNode.span⟩
          | .token tok => pure ⟨tok.text, tok.span⟩
          | _ =>
              let text ← getTokenText (← firstChild classNode)
              pure ⟨text, classNode.span⟩
          let args ← syntaxKids[1:].toArray.mapM lowerTypeExpr
          pure ⟨className, args, span⟩
      else
        lowerError s!"unexpected constraint node kind: {kind}" span
        pure ⟨⟨"_error", span⟩, #[], span⟩

  | .token tok =>
      -- A single token could be a class name like "Show"
      if tok.kind == .upperIdent then
        pure ⟨⟨tok.text, tok.span⟩, #[], tok.span⟩
      else
        lowerError s!"unexpected token in constraint: {tok.kind}" tok.span
        pure ⟨⟨"_error", tok.span⟩, #[], tok.span⟩

  | _ =>
      lowerError s!"unexpected constraint node" node.span
      pure ⟨⟨"_error", node.span⟩, #[], node.span⟩

end  -- end mutual block for lowerPattern, lowerTypeExpr, lowerConstraint

/-- Lower a data constructor -/
partial def lowerDataCon (node : SyntaxNode) : LowerM DataCon := do
  match node with
  | .node .constructor _ span =>
      let nameNodes := node.children.filterMap fun c =>
        match c with
        | .token tok => if tok.kind == .upperIdent then some tok else none
        | _ => none
      let name := if nameNodes.isEmpty then ⟨"_Con", span⟩
        else ⟨nameNodes[0]!.text, nameNodes[0]!.span⟩

      let fieldNodes := childrenOfKind node .field
      let fields ← fieldNodes.mapM fun f => do
        let fKids := syntaxChildren f
        if fKids.size >= 2 then
          let fname ← getTokenText (← firstChild fKids[0]!)
          let ftype ← lowerTypeExpr fKids[1]!
          pure (some ⟨fname, fKids[0]!.span⟩, ftype)
        else if fKids.size == 1 then
          let ftype ← lowerTypeExpr fKids[0]!
          pure (none, ftype)
        else
          pure (none, .var ⟨"_", f.span⟩)

      pure ⟨name, fields, span⟩
  | _ =>
      lowerError "expected constructor" node.span
      pure ⟨⟨"_Con", node.span⟩, #[], node.span⟩

/-- Lower a struct field -/
partial def lowerStructField (node : SyntaxNode) : LowerM StructField := do
  let fKids := syntaxChildren node
  if fKids.size >= 2 then
    let fname ← getTokenText (← firstChild fKids[0]!)
    let ftype ← lowerTypeExpr fKids[1]!
    pure ⟨⟨fname, fKids[0]!.span⟩, ftype, node.span⟩
  else
    lowerError "struct field missing name or type" node.span
    pure ⟨⟨"_", node.span⟩, .var ⟨"_", node.span⟩, node.span⟩


/-- Lower a token to an expression -/
def lowerExprToken (tok : Token) : LowerM Expr := do
  match tok.kind with
  | .lowerIdent => pure (.var ⟨tok.text, tok.span⟩)
  | .upperIdent => pure (.var ⟨tok.text, tok.span⟩)
  | .number => pure (.lit (.int tok.text.toInt! tok.span))
  | .string s => pure (.lit (.string s tok.span))
  | .true_ => pure (.lit (.bool true tok.span))
  | .false_ => pure (.lit (.bool false tok.span))
  | _ =>
      lowerError s!"unexpected token in expression: {tok.kind}" tok.span
      pure (.var ⟨"_error", tok.span⟩)

/-- Lower lambda parameters -/
def lowerLambdaParams (paramNodes : Array SyntaxNode) : LowerM (Array (Name × Option TypeExpr)) := do
  paramNodes.mapM fun p => do
    match p.kind? with
    | some .paramList =>
        let fields := childrenOfKind p .field
        let vars := childrenOfKind p .patVar
        if !fields.isEmpty then
          let f := fields[0]!
          let fKids := syntaxChildren f
          if fKids.size >= 2 then
            let name ← getTokenText (← firstChild fKids[0]!)
            let ty ← lowerTypeExpr fKids[1]!
            pure (⟨name, fKids[0]!.span⟩, some ty)
          else if fKids.size >= 1 then
            let name ← getTokenText (← firstChild fKids[0]!)
            pure (⟨name, fKids[0]!.span⟩, none)
          else
            pure (⟨"_", p.span⟩, none)
        else if !vars.isEmpty then
          let v := vars[0]!
          let name ← getTokenText (← firstChild v)
          pure (⟨name, v.span⟩, none)
        else
          pure (⟨"_", p.span⟩, none)
    | some .patVar =>
        let name ← getTokenText (← firstChild p)
        pure (⟨name, p.span⟩, none)
    | _ =>
        pure (⟨"_", p.span⟩, none)

/-! ## Expression Case Handlers (parameterized) -/

-- Each handler takes lowerE as a parameter, making them non-recursive defs

def lowerExprApp (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (span : Span) : LowerM Expr := do
  let syntaxKids := syntaxChildren node
  if syntaxKids.size < 2 then
    lowerError "application requires function and argument" span
    pure (.var ⟨"_error", span⟩)
  else
    let fn ← lowerE syntaxKids[0]!
    let arg ← lowerE syntaxKids[1]!
    pure (.app fn arg span)

def lowerExprInfix (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (children : Array SyntaxNode) (span : Span) : LowerM Expr := do
  let syntaxKids := syntaxChildren node
  let opNode := children.find? fun c =>
    match c with
    | .token tok => tok.kind == .varSymbol
    | _ => false
  match opNode with
  | some (.token opTok) =>
      if syntaxKids.size >= 2 then
        let left ← lowerE syntaxKids[0]!
        let right ← lowerE syntaxKids[1]!
        pure (.infix ⟨opTok.text, opTok.span⟩ left right span)
      else
        lowerError "infix expression requires two operands" span
        pure (.var ⟨"_error", span⟩)
  | _ =>
      lowerError "infix expression missing operator" span
      pure (.var ⟨"_error", span⟩)

def lowerExprLambda (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (span : Span) : LowerM Expr := do
  let paramNodes := childrenOfKind node .paramList ++ childrenOfKind node .patVar
  let bodyNodes := syntaxChildren node |>.filter fun c =>
    c.kind? != some .paramList && c.kind? != some .patVar
  let params ← lowerLambdaParams paramNodes
  if bodyNodes.isEmpty then
    lowerError "lambda missing body" span
    pure (.var ⟨"_error", span⟩)
  else
    let body ← lowerE bodyNodes[0]!
    pure (.lambda params body span)

def lowerExprLet (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (span : Span) : LowerM Expr := do
  let syntaxKids := syntaxChildren node
  if syntaxKids.size >= 2 then
    let nameOrPat := syntaxKids[0]!
    let name ← match nameOrPat.kind? with
    | some .name | some .patVar =>
        let text ← getTokenText (← firstChild nameOrPat)
        pure ⟨text, nameOrPat.span⟩
    | _ =>
        pure ⟨"_", nameOrPat.span⟩

    let sigNodes := childrenOfKind node .signature
    let sig ← if sigNodes.isEmpty then pure none
      else some <$> lowerTypeExpr sigNodes[0]!

    let valueIdx := if sigNodes.isEmpty then 1 else 2
    if h : valueIdx < syntaxKids.size then
      let value ← lowerE syntaxKids[valueIdx]
      let bodyIdx := valueIdx + 1
      if h2 : bodyIdx < syntaxKids.size then
        let body ← lowerE syntaxKids[bodyIdx]
        pure (.let_ name sig value body span)
      else
        lowerError "let missing body" span
        pure (.let_ name sig value (.var ⟨"_error", span⟩) span)
    else
      lowerError "let missing value" span
      pure (.var ⟨"_error", span⟩)
  else
    lowerError "let expression incomplete" span
    pure (.var ⟨"_error", span⟩)

def lowerExprIf (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (span : Span) : LowerM Expr := do
  let syntaxKids := syntaxChildren node
  if syntaxKids.size >= 3 then
    let cond ← lowerE syntaxKids[0]!
    let then_ ← lowerE syntaxKids[1]!
    let else_ ← lowerE syntaxKids[2]!
    pure (.if_ cond then_ else_ span)
  else
    lowerError "if expression incomplete" span
    pure (.var ⟨"_error", span⟩)

/-- Lower a match arm, using the provided expression lowering function -/
def lowerMatchArmWith (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) : LowerM MatchArm := do
  match node with
  | .node .matchArm _children span =>
      let patNodes := childrenOfKind node .patVar ++
                      childrenOfKind node .patCon ++
                      childrenOfKind node .patLit ++
                      childrenOfKind node .patWildcard ++
                      childrenOfKind node .patTuple ++
                      childrenOfKind node .patList ++
                      childrenOfKind node .patCons ++
                      childrenOfKind node .name
      let guardNodes := childrenOfKind node .matchGuard
      let bodyNodes := syntaxChildren node |>.filter fun c =>
        match c.kind? with
        | some k => !k.isPattern && k != .matchGuard && k != .name
        | none => true

      let patterns ← patNodes.mapM lowerPattern
      let guard ← if guardNodes.isEmpty then pure none
        else
          let g := guardNodes[0]!
          let gKids := syntaxChildren g
          if gKids.isEmpty then pure none
          else some <$> lowerE gKids[0]!

      if bodyNodes.isEmpty then
        lowerError "match arm missing body" span
        pure (.mk patterns guard (.var ⟨"_error", span⟩) span)
      else
        let body ← lowerE bodyNodes[0]!
        pure (.mk patterns guard body span)

  | _ =>
      lowerError "expected match arm" node.span
      pure (.mk #[] none (.var ⟨"_error", node.span⟩) node.span)

def lowerExprCase (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (span : Span) : LowerM Expr := do
  let syntaxKids := syntaxChildren node
  let armNodes := childrenOfKind node .matchArm
  let scrutNodes := syntaxKids.filter fun c => c.kind? != some .matchArm
  let scrutinees ← scrutNodes.mapM lowerE
  let arms ← armNodes.mapM (lowerMatchArmWith lowerE)
  pure (.case scrutinees arms span)

def lowerExprTuple (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (span : Span) : LowerM Expr := do
  let syntaxKids := syntaxChildren node
  let elems ← syntaxKids.mapM lowerE
  pure (.tuple elems span)

def lowerExprList (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (span : Span) : LowerM Expr := do
  let syntaxKids := syntaxChildren node
  let elems ← syntaxKids.mapM lowerE
  pure (.list elems span)

def lowerExprParens (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (span : Span) : LowerM Expr := do
  let syntaxKids := syntaxChildren node
  if syntaxKids.isEmpty then
    pure (.tuple #[] span)
  else
    let inner ← lowerE syntaxKids[0]!
    pure (.parens inner span)

def lowerExprTypeAnnot (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (span : Span) : LowerM Expr := do
  let syntaxKids := syntaxChildren node
  if syntaxKids.size >= 2 then
    let expr ← lowerE syntaxKids[0]!
    let ty ← lowerTypeExpr syntaxKids[1]!
    pure (.typeAnnot expr ty span)
  else
    lowerError "type annotation incomplete" span
    pure (.var ⟨"_error", span⟩)

def lowerExprCompose (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (span : Span) : LowerM Expr := do
  let syntaxKids := syntaxChildren node
  if syntaxKids.isEmpty then
    lowerError "compose block empty" span
    pure (.var ⟨"_error", span⟩)
  else if syntaxKids.size == 1 then
    -- Single statement - just lower it directly
    let body ← lowerE syntaxKids[0]!
    pure (.compose body span)
  else
    -- Multiple statements - chain them together
    -- For compose, this creates nested structure: compose { stmt1; stmt2; stmt3 }
    -- The semantic interpretation is up to later passes
    let stmts ← syntaxKids.mapM lowerE
    -- Create a tuple to hold all statements (or we could chain lets)
    -- For now, we'll wrap the sequence in a compose node
    -- The first n-1 statements should be let bindings or discarded expressions
    -- The last statement is the result
    let body := stmts[stmts.size - 1]!
    -- Build nested lets for earlier statements if they are let expressions
    -- Iterate backwards from (stmts.size - 2) down to 0
    let initStmts := stmts[:stmts.size - 1].toArray.reverse
    let mut result : Expr := body
    for stmt in initStmts do
      match stmt with
      | .let_ name ty val _ stmtSpan =>
          -- Chain the let: let name = val in <rest>
          result := Expr.let_ name ty val result stmtSpan
      | other =>
          -- For non-let expressions, we need to sequence them
          -- Create a synthetic let with underscore name
          result := Expr.let_ ⟨"_", other.span⟩ none other result other.span
    pure (.compose result span)

def lowerExprBind (lowerE : SyntaxNode → LowerM Expr) (node : SyntaxNode) (span : Span) : LowerM Expr := do
  let syntaxKids := syntaxChildren node
  if syntaxKids.isEmpty then
    lowerError "bind block empty" span
    pure (.var ⟨"_error", span⟩)
  else if syntaxKids.size == 1 then
    -- Single statement - just lower it directly
    let body ← lowerE syntaxKids[0]!
    pure (.bind body span)
  else
    -- Multiple statements - chain them together
    let stmts ← syntaxKids.mapM lowerE
    let body := stmts[stmts.size - 1]!
    let initStmts := stmts[:stmts.size - 1].toArray.reverse
    let mut result : Expr := body
    for stmt in initStmts do
      match stmt with
      | .let_ name ty val _ stmtSpan =>
          result := Expr.let_ name ty val result stmtSpan
      | other =>
          result := Expr.let_ ⟨"_", other.span⟩ none other result other.span
    pure (.bind result span)

/-! ## Expression Lowering (now just a small dispatch table) -/

partial def lowerExpr (node : SyntaxNode) : LowerM Expr := do
  match node with
  | .token tok => lowerExprToken tok

  | .node kind children span =>
      match kind with
      | .exprVar =>
          let text ← getTokenText (← firstChild node)
          pure (.var ⟨text, span⟩)
      | .exprLit =>
          lowerExpr (← firstChild node)
      | .exprApp => lowerExprApp lowerExpr node span
      | .exprInfix => lowerExprInfix lowerExpr node children span
      | .exprLambda => lowerExprLambda lowerExpr node span
      | .exprLet => lowerExprLet lowerExpr node span
      | .exprIf => lowerExprIf lowerExpr node span
      | .exprCase => lowerExprCase lowerExpr node span
      | .exprTuple => lowerExprTuple lowerExpr node span
      | .exprList => lowerExprList lowerExpr node span
      | .exprParens => lowerExprParens lowerExpr node span
      | .exprTypeAnnot => lowerExprTypeAnnot lowerExpr node span
      | .exprCompose => lowerExprCompose lowerExpr node span
      | .exprBind => lowerExprBind lowerExpr node span
      | .name =>
          let text ← getTokenText (← firstChild node)
          pure (.var ⟨text, span⟩)
      | _ =>
          lowerError s!"unexpected expression kind: {kind}" span
          pure (.var ⟨"_error", span⟩)

  | .error span msg _ =>
      lowerError msg span
      pure (.var ⟨"_error", span⟩)

  | .missing expected loc =>
      lowerError s!"missing {expected}" (Span.point loc)
      pure (.var ⟨"_error", Span.point loc⟩)

/-! ## Definition Clause Lowering -/

-- lowerDefClause calls lowerExpr (one-way), not mutually recursive
partial def lowerDefClause (node : SyntaxNode) : LowerM DefClause := do
  let patNodes := syntaxChildren node |>.filter fun c =>
    match c.kind? with
    | some k => k.isPattern || k == .name
    | none => false
  let guardNodes := childrenOfKind node .matchGuard
  let bodyNodes := syntaxChildren node |>.filter fun c =>
    match c.kind? with
    | some k => !k.isPattern && k != .matchGuard && k != .name
    | none => true

  let patterns ← patNodes.mapM lowerPattern
  let guard ← if guardNodes.isEmpty then pure none
    else
      let g := guardNodes[0]!
      let gKids := syntaxChildren g
      if gKids.isEmpty then pure none
      else some <$> lowerExpr gKids[0]!

  if bodyNodes.isEmpty then
    lowerError "definition clause missing body" node.span
    pure ⟨patterns, guard, .var ⟨"_error", node.span⟩, node.span⟩
  else
    let body ← lowerExpr bodyNodes[0]!
    pure ⟨patterns, guard, body, node.span⟩

/-! ## Declaration Lowering -/

-- lowerDecl is self-recursive (instance methods, intrinsic wrappers)
-- but not mutually recursive with the expression-level functions above.
partial def lowerDecl (node : SyntaxNode) : LowerM Decl := do
  match node with
  | .node kind _children span =>
      match kind with
      | .declDef =>
          let attrNodes := childrenOfKind node .attribute
          let attrs ← attrNodes.mapM fun a => do
            let nameNodes := childrenOfKind a .name
            if nameNodes.isEmpty then
              pure ⟨⟨"unknown", a.span⟩, #[], a.span⟩
            else
              let text ← getTokenText (← firstChild nameNodes[0]!)
              pure ⟨⟨text, nameNodes[0]!.span⟩, #[], a.span⟩

          let nameNodes := childrenOfKind node .name
          let opNameNodes := childrenOfKind node .operatorName
          let name ← if !nameNodes.isEmpty then
            let text ← getTokenText (← firstChild nameNodes[0]!)
            pure ⟨text, nameNodes[0]!.span⟩
          else if !opNameNodes.isEmpty then
            -- Operator name: { <op> } - get the operator token (second child)
            let opNode := opNameNodes[0]!
            let opTokens := opNode.children.filter fun c =>
              match c with
              | .token tok => tok.kind == .varSymbol
              | _ => false
            if opTokens.isEmpty then
              lowerError "operator name missing operator" opNode.span
              pure ⟨"_error", opNode.span⟩
            else
              match opTokens[0]! with
              | .token tok => pure ⟨tok.text, opNode.span⟩
              | _ => pure ⟨"_error", opNode.span⟩
          else
            lowerError "definition missing name" span
            pure ⟨"_error", span⟩

          let sigNodes := childrenOfKind node .signature
          let sig ← if sigNodes.isEmpty then pure none
            else some <$> lowerTypeExpr sigNodes[0]!

          let clauseNodes := childrenOfKind node .defClause
          let clauses ← clauseNodes.mapM lowerDefClause

          if clauses.isEmpty then
            let bodyNodes := syntaxChildren node |>.filter fun c =>
              c.kind? != some .name && c.kind? != some .operatorName &&
              c.kind? != some .signature && c.kind? != some .attribute &&
              c.kind? != some .paramList
            if bodyNodes.isEmpty then
              pure (.def_ attrs name sig #[] span)
            else
              let body ← lowerExpr bodyNodes[0]!
              let clause : DefClause := ⟨#[], none, body, body.span⟩
              pure (.def_ attrs name sig #[clause] span)
          else
            pure (.def_ attrs name sig clauses span)

      | .declData =>
          -- Look in ALL children (including tokens) for the type name
          let nameNodes := node.children.filter fun c =>
            match c with
            | .token tok => tok.kind == .upperIdent
            | .node .typeCon _ _ => true
            | _ => false
          let name ← if nameNodes.isEmpty then
            lowerError "data type missing name" span
            pure ⟨"_Error", span⟩
          else
            match nameNodes[0]! with
            | .token tok => pure ⟨tok.text, tok.span⟩
            | other =>
                let text ← getTokenText (← firstChild other)
                pure ⟨text, other.span⟩

          let paramNodes := childrenOfKind node .tyParamList
          let params ← if paramNodes.isEmpty then pure #[]
            else
              let plist := paramNodes[0]!
              let varNodes := childrenOfKind plist .typeVar
              varNodes.mapM fun v => do
                let text ← getTokenText (← firstChild v)
                pure ⟨text, v.span⟩

          let conNodes := childrenOfKind node .constructor
          let cons ← conNodes.mapM lowerDataCon

          pure (.data name params cons span)

      | .declStruct =>
          let syntaxKids := syntaxChildren node
          let nameNodes := syntaxKids.filter fun c =>
            match c with
            | .token tok => tok.kind == .upperIdent
            | _ => false
          if nameNodes.size < 2 then
            lowerError "struct missing name or constructor" span
            pure (.struct ⟨"_Error", span⟩ #[] ⟨"_Con", span⟩ #[] span)
          else
            let name ← getTokenText nameNodes[0]!
            let conName ← getTokenText nameNodes[1]!
            let fieldNodes := childrenOfKind node .field
            let fields ← fieldNodes.mapM lowerStructField
            pure (.struct ⟨name, nameNodes[0]!.span⟩ #[] ⟨conName, nameNodes[1]!.span⟩ fields span)

      | .declTrait =>
          -- Look in ALL children (including tokens) for the trait name
          let nameNodes := node.children.filter fun c =>
            match c with
            | .token tok => tok.kind == .upperIdent
            | _ => false
          let name ← if nameNodes.isEmpty then
            pure ⟨"_Error", span⟩
          else
            match nameNodes[0]! with
            | .token tok => pure ⟨tok.text, tok.span⟩
            | other =>
                let text ← getTokenText other
                pure ⟨text, other.span⟩

          let paramNodes := childrenOfKind node .tyParamList
          let params ← if paramNodes.isEmpty then pure #[]
            else
              let plist := paramNodes[0]!
              let varNodes := childrenOfKind plist .typeVar
              varNodes.mapM fun v => do
                let text ← getTokenText (← firstChild v)
                pure ⟨text, v.span⟩

          let constraintNodes := childrenOfKind node .constraintList
          let constraints ← constraintNodes.mapM lowerConstraint

          let methodNodes := childrenOfKind node .traitMethod
          let methods ← methodNodes.mapM fun m => do
            let nameN := childrenOfKind m .name
            let opNameN := childrenOfKind m .operatorName
            let sigN := childrenOfKind m .signature
            let mname ← if !nameN.isEmpty then
                let text ← getTokenText (← firstChild nameN[0]!)
                pure ⟨text, nameN[0]!.span⟩
              else if !opNameN.isEmpty then
                -- Operator name: { <op> }
                let opNode := opNameN[0]!
                let opTokens := opNode.children.filter fun c =>
                  match c with
                  | .token tok => tok.kind == .varSymbol
                  | _ => false
                if opTokens.isEmpty then pure ⟨"_", m.span⟩
                else
                  match opTokens[0]! with
                  | .token tok => pure ⟨tok.text, opNode.span⟩
                  | _ => pure ⟨"_", m.span⟩
              else pure ⟨"_", m.span⟩
            let mtype ← if sigN.isEmpty then pure (.var ⟨"_", m.span⟩)
              else lowerTypeExpr sigN[0]!
            pure ⟨mname, mtype, m.span⟩

          pure (.trait name params constraints methods span)

      | .declInstance =>
          let constraintNodes := childrenOfKind node .constraint
          let (traitName, args) ← if constraintNodes.isEmpty then
            pure (⟨"_Error", span⟩, #[])
          else
            let c ← lowerConstraint constraintNodes[0]!
            pure (c.className, c.args)

          let superNodes := childrenOfKind node .constraintList
          let constraints ← superNodes.mapM lowerConstraint

          let methodNodes := childrenOfKind node .declDef
          let methods ← methodNodes.mapM lowerDecl

          pure (.instance_ traitName args constraints methods span)

      | .declUse =>
          let pathNodes := childrenOfKind node .importPath
          let itemNodes := childrenOfKind node .importItems

          let path ← if pathNodes.isEmpty then
            pure ⟨#[], "_error", span⟩
          else
            let segments := pathNodes[0]!.children.filterMap fun c =>
              match c with
              | .token tok => if tok.kind != .slash then some tok.text else none
              | _ => none
            if segments.isEmpty then
              pure ⟨#[], "_error", span⟩
            else
              let pathArr := segments[0:segments.size-1].toArray
              let name := segments[segments.size-1]!
              pure ⟨pathArr, name, pathNodes[0]!.span⟩

          let items ← if itemNodes.isEmpty then pure #[]
            else
              let ilist := itemNodes[0]!
              let names := childrenOfKind ilist .name ++ childrenOfKind ilist .operatorName
              names.mapM fun n => do
                let text ← getTokenText (← firstChild n)
                pure ⟨text, n.span⟩

          pure (.use path items span)

      | .declExport =>
          let itemNodes := childrenOfKind node .importItems ++ childrenOfKind node .exportItems
          let items ← if itemNodes.isEmpty then pure #[]
            else
              let ilist := itemNodes[0]!
              let names := childrenOfKind ilist .name ++ childrenOfKind ilist .operatorName
              names.mapM fun n => do
                let text ← getTokenText (← firstChild n)
                pure ⟨text, n.span⟩

          pure (.export_ items span)

      | .declIntrinsic =>
          let innerNodes := syntaxChildren node
          if innerNodes.isEmpty then
            lowerError "intrinsic missing declaration" span
            pure (.intrinsic (.export_ #[] span) span)
          else
            let inner ← lowerDecl innerNodes[0]!
            pure (.intrinsic inner span)

      | _ =>
          lowerError s!"unexpected declaration kind: {kind}" span
          pure (.export_ #[] span)

  | .error span msg _ =>
      lowerError msg span
      pure (.export_ #[] span)

  | .missing expected loc =>
      lowerError s!"missing {expected}" (Span.point loc)
      pure (.export_ #[] (Span.point loc))

  | .token tok =>
      lowerError s!"unexpected token at declaration level: {tok.kind}" tok.span
      pure (.export_ #[] tok.span)

-- lowerModule is not recursive at all, just calls lowerDecl
def lowerModule (node : SyntaxNode) (moduleName : String) : LowerM Module := do
  match node with
  | .node .sourceFile children span =>
      let decls ← children.filterMapM fun c => do
        match c with
        | .error span msg _ =>
            lowerError msg span
            pure none
        | .missing expected loc =>
            lowerError s!"missing {expected}" (Span.point loc)
            pure none
        | _ =>
            some <$> lowerDecl c
      pure ⟨moduleName, decls, span⟩

  | _ =>
      lowerError "expected source file" node.span
      pure ⟨moduleName, #[], node.span⟩

/--
Lower a CST to an AST.
Returns the AST (if successful) and all diagnostics.
-/
def lower (cst : SyntaxNode) (moduleName : String := "Main") : Option Module × Diagnostics :=
  let (result, diagnostics) := (lowerModule cst moduleName).run'
  match result with
  | .ok mod => (some mod, diagnostics)
  | .error _ => (none, diagnostics)

end Soma.Syntax
