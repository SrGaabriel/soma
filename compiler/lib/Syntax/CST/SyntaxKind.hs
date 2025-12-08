{- HLINT ignore "Use camelCase" -}
module Syntax.CST.SyntaxKind (
    SyntaxKind (..),
    NodeKind (..),
    TriviaKind (..),
    isTrivia,
    isToken,
    isNode,
    isKeyword,
    isOperator,
    isLiteral,
    isError,
    tokenKind,
    nodeKind,
    TokenKind (..),
) where

import Data.Hashable (Hashable (..))
import Lexing.Lexer (TokenKind (..))

data SyntaxKind
    = SK_Token !TokenKind
    | SK_Node !NodeKind
    | SK_Trivia !TriviaKind
    | SK_Error
    deriving (Eq, Ord, Show)

instance Hashable SyntaxKind where
    hashWithSalt s (SK_Token tk) = hashWithSalt s (0 :: Int, show tk)
    hashWithSalt s (SK_Node nk) = hashWithSalt s (1 :: Int, fromEnum nk)
    hashWithSalt s (SK_Trivia tk) = hashWithSalt s (2 :: Int, fromEnum tk)
    hashWithSalt s SK_Error = hashWithSalt s (3 :: Int)

data TriviaKind
    = TriviaWhitespace
    | TriviaNewline
    | TriviaComment
    | TriviaDocComment
    deriving (Eq, Ord, Show, Enum, Bounded)

data NodeKind
    = -- Top-level
      NK_SOURCE_FILE
    | NK_MODULE_DECL
    | -- Imports
      NK_IMPORT_DECL
    | NK_IMPORT_LIST
    | NK_IMPORT_ITEM
    | -- Definitions
      NK_BINDING_DEF
    | NK_TYPE_SIGNATURE
    | NK_DATA_DEF
    | NK_DATA_CONSTRUCTOR
    | NK_CONSTRUCTOR_FIELD
    | NK_TRAIT_DEF
    | NK_TRAIT_METHOD
    | NK_INSTANCE_DEF
    | NK_INSTANCE_METHOD
    | NK_INTRINSIC_DEF
    | NK_INTRINSIC_DATA
    | -- Patterns
      NK_PATTERN
    | NK_PATTERN_VAR
    | NK_PATTERN_CONSTRUCTOR
    | NK_PATTERN_LITERAL
    | NK_PATTERN_WILDCARD
    | NK_PATTERN_AS
    | NK_PATTERN_TUPLE
    | NK_PATTERN_LIST
    | NK_PATTERN_CONS
    | -- Types
      NK_TYPE
    | NK_TYPE_VAR
    | NK_TYPE_CONSTRUCTOR
    | NK_TYPE_APP
    | NK_TYPE_ARROW
    | NK_TYPE_TUPLE
    | NK_TYPE_LIST
    | NK_TYPE_PARENS
    | NK_CONSTRAINT
    | NK_CONSTRAINT_LIST
    | NK_FORALL
    | -- Expressions
      NK_EXPR
    | NK_EXPR_VAR
    | NK_EXPR_CONSTRUCTOR
    | NK_EXPR_LITERAL
    | NK_EXPR_APP
    | NK_EXPR_LAMBDA
    | NK_EXPR_LET
    | NK_EXPR_IF
    | NK_EXPR_MATCH
    | NK_MATCH_ARM
    | NK_EXPR_TUPLE
    | NK_EXPR_LIST
    | NK_EXPR_PARENS
    | NK_EXPR_BLOCK
    | NK_EXPR_COMPOSE
    | NK_COMPOSE_STMT
    | NK_COMPOSE_BIND
    | NK_COMPOSE_LET
    | -- Misc
      NK_PARAM_LIST
    | NK_PARAM
    | NK_ARG_LIST
    | NK_NAME
    | NK_QUALIFIED_NAME
    | -- Error recovery node
      NK_ERROR
    deriving (Eq, Ord, Show, Enum, Bounded)

tokenKind :: TokenKind -> SyntaxKind
tokenKind = SK_Token

nodeKind :: NodeKind -> SyntaxKind
nodeKind = SK_Node

isTrivia :: SyntaxKind -> Bool
isTrivia (SK_Trivia _) = True
isTrivia _ = False

isToken :: SyntaxKind -> Bool
isToken (SK_Token _) = True
isToken (SK_Trivia _) = True
isToken SK_Error = True
isToken _ = False

isNode :: SyntaxKind -> Bool
isNode (SK_Node _) = True
isNode _ = False

isKeyword :: SyntaxKind -> Bool
isKeyword (SK_Token tk) = tk `elem` keywordTokens
  where
    keywordTokens =
        [ TokenDef
        , TokenData
        , TokenTrait
        , TokenInstance
        , TokenWhere
        , TokenWith
        , TokenImport
        , TokenIntrinsic
        , TokenIf
        , TokenThen
        , TokenElse
        , TokenLet
        , TokenIn
        , TokenCase
        , TokenStruct
        , TokenCompose
        , TokenBind
        , TokenForall
        , TokenTrue
        , TokenFalse
        ]
isKeyword _ = False

isOperator :: SyntaxKind -> Bool
isOperator (SK_Token TokenVarSymbol) = True
isOperator _ = False

isLiteral :: SyntaxKind -> Bool
isLiteral (SK_Token TokenNumber) = True
isLiteral (SK_Token (TokenString _)) = True
isLiteral _ = False

isError :: SyntaxKind -> Bool
isError SK_Error = True
isError (SK_Node NK_ERROR) = True
isError _ = False
