namespace Soma.Syntax


inductive SyntaxKind where
  -- Source File
  | sourceFile        -- Root node containing all declarations
  -- Declarations
  | declDef           -- Function/value definition
  | declData          -- Data type definition
  | declStruct        -- Struct definition
  | declTrait         -- Trait definition
  | declInstance      -- Instance definition
  | declUse           -- Import declaration
  | declExport        -- Export declaration
  | declIntrinsic     -- Intrinsic declaration
  -- Definition Components
  | signature         -- Type signature
  | defClause         -- Pattern matching clause
  | constructor       -- Data constructor
  | field             -- Struct/constructor field
  | traitMethod       -- Method in trait
  | instanceMethod    -- Method implementation in instance
  -- Expressions
  | exprVar           -- Variable reference
  | exprLit           -- Literal
  | exprApp           -- Function application
  | exprInfix         -- Infix operator
  | exprLambda        -- Lambda expression
  | exprLet           -- Let binding
  | exprIf            -- Conditional
  | exprCase          -- Case expression
  | exprMatch         -- Pattern match in def
  | exprTuple         -- Tuple
  | exprList          -- List literal
  | exprRecord        -- Record literal { x = 1, y = 2 }
  | exprRecordUpdate  -- Record update { r | x = 3 }
  | recordField       -- Record field: name = expr
  | exprFieldAccess   -- Field access (expr.field)
  | exprProjection    -- Projection function (Type.field)
  | exprParens        -- Parenthesized
  | exprCompose       -- Compose block
  | exprBind          -- Bind block
  | composeLetStmt    -- Let statement in compose block (no 'in')
  | exprSection       -- Operator section
  | exprTypeAnnot     -- Type annotation
  | exprTypeApp       -- Explicit type application (@Type or @label)
  -- Patterns
  | patVar            -- Variable pattern
  | patWildcard       -- Wildcard
  | patLit            -- Literal pattern
  | patCon            -- Constructor pattern
  | patTuple          -- Tuple pattern
  | patList           -- List pattern
  | patCons           -- Cons pattern
  | patAs             -- As pattern
  | patParens         -- Parenthesized
  | patTyped          -- Typed pattern
  -- Types
  | typeVar           -- Type variable
  | typeCon           -- Type constructor
  | typeApp           -- Type application
  | typeArrow         -- Function type
  | typeTuple         -- Tuple type
  | typeList          -- List type
  | typeForall        -- Universal type
  | typeConstrained   -- Constrained type
  | typeParens        -- Parenthesized type
  | typeKinded        -- Kind annotation
  | typeRecord        -- Record type { x :: Int, y :: Bool }
  | typeRecordField   -- Record type field: name :: Type
  -- Type Constraints
  | constraint        -- Single constraint
  | constraintList    -- Multiple constraints
  -- Auxiliary Nodes
  | paramList         -- Parameter list
  | argList           -- Argument list in application
  | tyParamList       -- Type parameter list
  | tyParamKinded     -- Kinded type parameter: (r :: Row)
  | matchArm          -- Case arm
  | matchGuard        -- Guard in match
  | importPath        -- Import path
  | importItems       -- Import item list
  | exportItems       -- Export item list
  | attribute         -- Attribute
  | attributeList     -- Multiple attributes
  -- Operators
  | operator          -- An operator symbol
  -- Trivia (for lossless representation)
  | whitespace        -- Spaces, tabs
  | newline           -- Newline character(s)
  | comment           -- Line or block comment
  -- Names
  | name              -- Simple name
  | qualifiedName     -- Qualified name
  | operatorName      -- Operator as name
  -- Token with leading trivia (for accurate span tracking)
  | triviaToken       -- Wrapper: [trivia..., token]
  deriving Repr, BEq, Hashable, Inhabited

/-- Human-readable description of a syntax kind -/
def SyntaxKind.describe : SyntaxKind → String
  | .sourceFile => "source file"
  | .declDef => "definition"
  | .declData => "data type"
  | .declStruct => "struct"
  | .declTrait => "trait"
  | .declInstance => "instance"
  | .declUse => "import"
  | .declExport => "export"
  | .declIntrinsic => "intrinsic"
  | .signature => "type signature"
  | .defClause => "definition clause"
  | .constructor => "constructor"
  | .field => "field"
  | .traitMethod => "trait method"
  | .instanceMethod => "instance method"
  | .exprVar => "variable"
  | .exprLit => "literal"
  | .exprApp => "application"
  | .exprInfix => "infix expression"
  | .exprLambda => "lambda"
  | .exprLet => "let expression"
  | .exprIf => "if expression"
  | .exprCase => "case expression"
  | .exprMatch => "pattern match"
  | .exprTuple => "tuple"
  | .exprList => "list"
  | .exprRecord => "record"
  | .exprRecordUpdate => "record update"
  | .recordField => "record field"
  | .exprFieldAccess => "field access"
  | .exprProjection => "projection"
  | .exprParens => "parenthesized expression"
  | .exprCompose => "compose block"
  | .exprBind => "bind block"
  | .composeLetStmt => "compose let statement"
  | .exprSection => "operator section"
  | .exprTypeAnnot => "type annotation"
  | .exprTypeApp => "type application"
  | .patVar => "variable pattern"
  | .patWildcard => "wildcard pattern"
  | .patLit => "literal pattern"
  | .patCon => "constructor pattern"
  | .patTuple => "tuple pattern"
  | .patList => "list pattern"
  | .patCons => "cons pattern"
  | .patAs => "as pattern"
  | .patParens => "parenthesized pattern"
  | .patTyped => "typed pattern"
  | .typeVar => "type variable"
  | .typeCon => "type constructor"
  | .typeApp => "type application"
  | .typeArrow => "function type"
  | .typeTuple => "tuple type"
  | .typeList => "list type"
  | .typeForall => "universal type"
  | .typeConstrained => "constrained type"
  | .typeParens => "parenthesized type"
  | .typeKinded => "kinded type"
  | .typeRecord => "record type"
  | .typeRecordField => "record type field"
  | .constraint => "constraint"
  | .constraintList => "constraint list"
  | .paramList => "parameter list"
  | .argList => "argument list"
  | .tyParamList => "type parameter list"
  | .tyParamKinded => "kinded type parameter"
  | .matchArm => "match arm"
  | .matchGuard => "match guard"
  | .importPath => "import path"
  | .importItems => "import items"
  | .exportItems => "export items"
  | .attribute => "attribute"
  | .attributeList => "attribute list"
  | .operator => "operator"
  | .whitespace => "whitespace"
  | .newline => "newline"
  | .comment => "comment"
  | .name => "name"
  | .qualifiedName => "qualified name"
  | .operatorName => "operator name"
  | .triviaToken => "token with trivia"

instance : ToString SyntaxKind where
  toString := SyntaxKind.describe

/-- Check if a syntax kind represents a declaration -/
def SyntaxKind.isDecl : SyntaxKind → Bool
  | .declDef | .declData | .declStruct | .declTrait
  | .declInstance | .declUse | .declExport | .declIntrinsic => true
  | _ => false

/-- Check if a syntax kind represents an expression -/
def SyntaxKind.isExpr : SyntaxKind → Bool
  | .exprVar | .exprLit | .exprApp | .exprInfix | .exprLambda
  | .exprLet | .exprIf | .exprCase | .exprMatch | .exprTuple
  | .exprList | .exprRecord | .exprFieldAccess | .exprProjection | .exprParens
  | .exprCompose | .exprBind | .exprSection | .exprTypeAnnot | .exprTypeApp => true
  | _ => false

/-- Check if a syntax kind represents a pattern -/
def SyntaxKind.isPattern : SyntaxKind → Bool
  | .patVar | .patWildcard | .patLit | .patCon | .patTuple
  | .patList | .patCons | .patAs | .patParens | .patTyped => true
  | _ => false

/-- Check if a syntax kind represents a type -/
def SyntaxKind.isType : SyntaxKind → Bool
  | .typeVar | .typeCon | .typeApp | .typeArrow | .typeTuple
  | .typeList | .typeForall | .typeConstrained | .typeParens | .typeKinded
  | .typeRecord | .typeRecordField => true
  | _ => false

/-- Check if a syntax kind represents trivia -/
def SyntaxKind.isTrivia : SyntaxKind → Bool
  | .whitespace | .newline | .comment => true
  | _ => false

end Soma.Syntax
