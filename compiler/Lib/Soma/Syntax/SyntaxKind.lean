namespace Soma.Syntax

inductive SyntaxKind where
  -- Source File
  | sourceFile        -- Root node containing all declarations
  -- Declarations
  | declDef           -- Function/value definition (may have no body if @[intrinsic] or @[extern])
  | declTheorem       -- Proof declaration
  | declInductive     -- Inductive type definition (may have no constructors if @[intrinsic])
  | declStruct        -- Struct definition
  | declTrait         -- Trait definition
  | declInstance      -- Instance definition (may have no methods if @[intrinsic])
  | declUse           -- Import declaration (use / pub use)
  | declAbbrev        -- Type abbreviation
  -- Definition Components
  | signature         -- Type signature
  | defClause         -- Pattern matching clause
  | constructor       -- Data constructor (simple: | Cons a (List a))
  | constructorSig    -- Data constructor with return type (indexed: | Cons :: a -> Vec n a -> Vec (n+1) a)
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
  | composeLetStmt    -- Let statement in compose block: let x = expr
  | composeBindStmt   -- Bind statement in compose block: bind x <- expr
  | exprSection       -- Operator section
  | exprTypeAnnot     -- Type annotation
  | exprTypeApp       -- Explicit type application (@Type or @label)
  | exprVariant       -- Variant injection (.Ok value)
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
  | patVariant        -- Variant pattern (.Ok x)
  -- Types
  | typeVar           -- Type variable
  | typeCon           -- Type constructor
  | typeApp           -- Type application
  | typeArrow         -- Function type
  | typeTuple         -- Tuple type
  | typeList          -- List type
  | typeForall        -- Universal type
  | typeParens        -- Parenthesized type
  | typeKinded        -- Kind annotation
  | typeRecord        -- Record type { x :: Int, y :: Bool }
  | typeRecordField   -- Record type field: name :: Type
  | typeVariant       -- Variant type < Ok :: Int | Err :: String >
  | typeVariantCase   -- Variant type case: Name :: Type
  -- Dependent Types (Phase 7)
  | typePi            -- Dependent function type: (x : A) -> B
  | typeSigma         -- Dependent pair type: (x : A) × B
  | typeImplicit      -- Implicit parameter type: {x : A} -> B
  | typePiBinder      -- Binder in Pi type: (q x : A) or (x : A)
  | typeQuantity      -- Quantity annotation: 0, 1, or ω
  -- Type Constraints
  | constraint        -- Single constraint
  | constraintList    -- Multiple constraints
  -- Instance Binders
  | instTypeVarBinder -- Implicit type var binder on instance: {a : Type}
  | instDictBinder    -- Instance dict binder on instance: {{d : Display a}} or {{Display a}}
  -- Auxiliary Nodes
  | paramList         -- Parameter list
  | argList           -- Argument list in application
  | tyParamList       -- Type parameter list
  | tyParamKinded     -- Kinded type parameter: (r :: Row)
  | matchArm          -- Case arm
  | matchGuard        -- Guard in match
  | importPath        -- Import path
  | importItems       -- Import item list
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
  | .declTheorem => "theorem"
  | .declInductive => "inductive type"
  | .declStruct => "struct"
  | .declTrait => "class"
  | .declInstance => "instance"
  | .declUse => "import"
  | .declAbbrev => "abbreviation"
  | .signature => "type signature"
  | .defClause => "definition clause"
  | .constructor => "constructor"
  | .constructorSig => "constructor with signature"
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
  | .composeLetStmt => "compose let statement"
  | .composeBindStmt => "compose bind statement"
  | .exprSection => "operator section"
  | .exprTypeAnnot => "type annotation"
  | .exprTypeApp => "type application"
  | .exprVariant => "variant injection"
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
  | .patVariant => "variant pattern"
  | .typeVar => "type variable"
  | .typeCon => "type constructor"
  | .typeApp => "type application"
  | .typeArrow => "function type"
  | .typeTuple => "tuple type"
  | .typeList => "list type"
  | .typeForall => "universal type"
  | .typeParens => "parenthesized type"
  | .typeKinded => "kinded type"
  | .typeRecord => "record type"
  | .typeRecordField => "record type field"
  | .typeVariant => "variant type"
  | .typeVariantCase => "variant type case"
  | .typePi => "dependent function type"
  | .typeSigma => "dependent pair type"
  | .typeImplicit => "implicit parameter type"
  | .typePiBinder => "pi type binder"
  | .typeQuantity => "quantity annotation"
  | .constraint => "constraint"
  | .constraintList => "constraint list"
  | .instTypeVarBinder => "instance type variable binder"
  | .instDictBinder => "instance dictionary binder"
  | .paramList => "parameter list"
  | .argList => "argument list"
  | .tyParamList => "type parameter list"
  | .tyParamKinded => "kinded type parameter"
  | .matchArm => "match arm"
  | .matchGuard => "match guard"
  | .importPath => "import path"
  | .importItems => "import items"
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
  | .declDef | .declTheorem | .declInductive | .declStruct | .declTrait
  | .declInstance | .declUse | .declAbbrev => true
  | _ => false

/-- Check if a syntax kind represents an expression -/
def SyntaxKind.isExpr : SyntaxKind → Bool
  | .exprVar | .exprLit | .exprApp | .exprInfix | .exprLambda
  | .exprLet | .exprIf | .exprCase | .exprMatch | .exprTuple
  | .exprList | .exprRecord | .exprFieldAccess | .exprProjection | .exprParens
  | .exprCompose | .exprSection | .exprTypeAnnot | .exprTypeApp
  | .exprVariant => true
  | _ => false

/-- Check if a syntax kind represents a pattern -/
def SyntaxKind.isPattern : SyntaxKind → Bool
  | .patVar | .patWildcard | .patLit | .patCon | .patTuple
  | .patList | .patCons | .patAs | .patParens | .patTyped
  | .patVariant => true
  | _ => false

/-- Check if a syntax kind represents a type -/
def SyntaxKind.isType : SyntaxKind → Bool
  | .typeVar | .typeCon | .typeApp | .typeArrow | .typeTuple
  | .typeList | .typeForall | .typeParens | .typeKinded
  | .typeRecord | .typeRecordField | .typeVariant | .typeVariantCase
  | .typePi | .typeSigma | .typeImplicit | .typePiBinder | .typeQuantity => true
  | _ => false

def SyntaxKind.isTerm (k : SyntaxKind) : Bool :=
  k.isType || k.isExpr || k == .name || k == .signature

/-- Check if a syntax kind represents trivia -/
def SyntaxKind.isTrivia : SyntaxKind → Bool
  | .whitespace | .newline | .comment => true
  | _ => false

end Soma.Syntax
