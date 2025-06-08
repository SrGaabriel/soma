module Parsing.Bindings where

import Parsing.Parser (Parser, consume, optional, parseFluidSequence)
import Syntax.Tree (Expr (ExprFunctionDef, ExprConstantDef))
import Typing.Types (Type (..))
import Lexing.Lexer (Token(..), TokenKind (..), spanningTokens)
import Parsing.Types (parseType)
import Typing.Currying (uncurryFunction)
import Control.Monad.Error.Class (MonadError(throwError))
import Parsing.Errors (ParsingError(FunctionArgumentLengthMismatch))
import Parsing.Atoms (parseExpression)

parseBinding :: Parser Expr
parseBinding = do
    nameToken <- consume TokenIdentifier
    let name = tokenValue nameToken
    leftParenthesisArgStart <- optional $ consume TokenLeftParen
    argNames <-
        case leftParenthesisArgStart of
            Just _ -> do
                parseFluidSequence TokenRightParen (consume TokenIdentifier)
                    <* consume TokenRightParen
            Nothing -> do
                parseFluidSequence TokenReturns (consume TokenIdentifier)
            <* consume TokenReturns

    bindType <- parseType

    case bindType of
        TArrow arg ret | argNames /= [] -> do
            let (argTypes, returnType) = uncurryFunction arg ret
            argMappings <- ensureSameLengthMap argNames argTypes
            equals <- consume TokenEquals
            _ <- optional $ consume TokenNewline
            body <- parseExpression
            let spanning = spanningTokens nameToken equals
            pure $ ExprFunctionDef name argMappings returnType body spanning
        _ -> do
            equals <- consume TokenEquals
            _ <- optional $ consume TokenNewline
            body <- parseExpression
            let spanning = spanningTokens nameToken equals
            pure $ ExprConstantDef name bindType body spanning

ensureSameLengthMap :: [Token] -> [Type] -> Parser [(String, Type)]
ensureSameLengthMap names types
    | length names == length types = pure $ zip (map tokenValue names ++ replicate (length types - length names) "_") types
    | otherwise = throwError $ FunctionArgumentLengthMismatch (last names)