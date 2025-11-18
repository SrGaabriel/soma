module Parsing.Bindings where

import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens)
import Parsing.Parser (Parser, consume)
import Parsing.Types (parseQualifiedType)
import Syntax.Tree (Expr (..))
import Parsing.Atoms (parseExpression)

parseBinding :: Bool -> Parser Expr
parseBinding isTopLevel = do
    defToken <- consume TokenDef
    name <- tokenValue <$> consume TokenLowerIdentifier
    _ <- consume TokenReturns
    bindType <- parseQualifiedType
    eqTok <- consume TokenEquals
    expr <- parseExpression
    pure
        $ ExprBindingDef
            { bindingName = name
            , bindingType = bindType
            , bindingIsImpl = isTopLevel
            , bindingBody = expr
            , bindingSpan = spanningTokens defToken eqTok
            }
