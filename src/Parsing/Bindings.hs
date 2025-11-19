{-# LANGUAGE BangPatterns #-}
module Parsing.Bindings where

import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens)
import Parsing.Parser (Parser, consume, parseOptionallyInLayout)
import Parsing.Types (parseQualifiedType)
import Syntax.Tree (Expr (..))
import Parsing.Atoms (parseExpression)
import qualified Debug.Trace as Debug

parseBinding :: Bool -> Parser Expr
parseBinding isTopLevel = do
    defToken <- consume TokenDef
    let !_ = Debug.trace ("about to parse binding name")
    name <- tokenValue <$> consume TokenLowerIdentifier
    let !_ = Debug.trace ("about to parse binding returns")
    _ <- consume TokenReturns
    let !_ = Debug.trace ("about to parse binding type")
    bindType <- parseQualifiedType
    let !_ = Debug.trace ("about to parse binding body")
    eqTok <- consume TokenEquals
    let !_ = Debug.trace ("whew")
    expr <- parseOptionallyInLayout parseExpression
    let !_ = Debug.trace ("done")
    pure
        $ ExprBindingDef
            { bindingName = name
            , bindingType = bindType
            , bindingIsImpl = isTopLevel
            , bindingBody = expr
            , bindingSpan = spanningTokens defToken eqTok
            }
