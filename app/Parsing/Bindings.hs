module Parsing.Bindings where

import Control.Monad.Error.Class (MonadError (throwError))
import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens)
import Parsing.Atoms (parseExpression)
import Parsing.Errors (ParsingError (FunctionArgumentLengthMismatch))
import Parsing.Parser (Parser, consume, optional, parseFluidSequence)
import Parsing.Types (parseType)
import Syntax.Tree (Expr (ExprConstantDef, ExprFunctionDef))
import Typing.Currying (uncurryFunction)
import Typing.Types (Type (..), extractFunc, isFunc)

parseBinding :: Parser Expr
parseBinding = do
    nameToken <- consume TokenLowerIdentifier
    let name = tokenValue nameToken
    leftParenthesisArgStart <- optional $ consume TokenLeftParen
    argNames <-
        case leftParenthesisArgStart of
            Just _ -> do
                parseFluidSequence TokenRightParen (consume TokenLowerIdentifier)
                    <* consume TokenRightParen
            Nothing -> do
                parseFluidSequence TokenReturns (consume TokenLowerIdentifier)
            <* consume TokenReturns

    bindType <- parseType

    if isFunc bindType && argNames /= []
        then do
            let funcT = extractFunc bindType
            let (argTypes, returnType) = uncurryFunction funcT
            argMappings <- ensureSameLengthMap argNames argTypes
            equals <- consume TokenEquals
            _ <- optional $ consume TokenNewline
            body <- parseExpression
            let spanning = spanningTokens nameToken equals
            pure $ ExprFunctionDef name argMappings returnType body spanning
        else
            if argNames /= []
                then throwError $ FunctionArgumentLengthMismatch (last argNames)
                else do
                    equals <- consume TokenEquals
                    _ <- optional $ consume TokenNewline
                    body <- parseExpression
                    let spanning = spanningTokens nameToken equals
                    pure $ ExprConstantDef name bindType body spanning

ensureSameLengthMap :: [Token] -> [Type] -> Parser [(String, Type)]
ensureSameLengthMap names types
    | length names == length types = pure $ zip (map tokenValue names ++ replicate (length types - length names) "_") types
    | otherwise = throwError $ FunctionArgumentLengthMismatch (last names)
