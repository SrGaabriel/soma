module Parsing.Bindings where

import Parsing.Parser (Parser, consume)
import Syntax.Tree (Expr (..))
import Lexing.Lexer (TokenKind(..), spanningTokens, Token (..))
import Typing.Types (QualifiedType(Forall), intType)

parseBinding :: Bool -> Parser Expr
parseBinding isTopLevel = do
    defToken <- consume TokenDef
    name <- tokenValue <$> consume TokenLowerIdentifier
    _ <- consume TokenReturns
    bindingTyp <- consume TokenUpperIdentifier
    pure
        $ ExprBindingDef
            { bindingName = name
            , bindingType = Forall [] [] intType
            , bindingIsImpl = isTopLevel -- TODO: review this
            , bindingBody = ExprRoot []
            , bindingSpan = spanningTokens defToken bindingTyp
            }
