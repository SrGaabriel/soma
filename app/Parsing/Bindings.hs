module Parsing.Bindings where

import Control.Monad.Error.Class (MonadError (throwError))
import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens)
import Parsing.Atoms (parseExpression)
import Parsing.Errors (ParsingError (FunctionArgumentLengthMismatch, InvalidFunctionBody))
import Parsing.Parser (Parser, consume, consumeRelevant, next, optional, parseFuncName, parseSequence, peekRelevant)
import Parsing.Patterns (parsePipePatternArms)
import Parsing.Types (parseQualifiedType, parseType)
import Syntax.Tree (Expr (..), exprSpan)
import Typing.Currying (curryFunction, uncurryQualified)
import Typing.Types (QualifiedType (..), Type (..))

parseBinding :: Bool -> Parser Expr
parseBinding isTopLevel = do
    defToken <- consume TokenDef
    name <- parseFuncName
    leftParenthesisArgStart <- optional $ consume TokenLeftParen

    case leftParenthesisArgStart of
        Just _ -> do
            params <-
                parseSequence TokenComma TokenRightParen parseImperativeBindingParam
                    <* consume TokenRightParen
            let (toks, types) = unzip params
            mappings <- ensureSameLengthMap toks types
            _ <- consume TokenRightArrow
            returnType <- parseType
            let bindingTyp = curryFunction types returnType
            let bindingTypeS = Forall [] [] bindingTyp -- todo: support constraints in this def
            eqTok <- consumeRelevant TokenEquals
            body <- parseExpression
            let argNames = Prelude.map Prelude.fst mappings
            let defBody = ExprLambda argNames body (exprSpan body)
            pure $ ExprBindingDef name bindingTypeS defBody isTopLevel (spanningTokens defToken eqTok)
        Nothing -> do
            _ <- consumeRelevant TokenReturns
            bindingTyp <- parseQualifiedType
            inc <- peekRelevant
            case tokenKind inc of
                TokenEquals -> do
                    _ <- next
                    body <- parseExpression
                    pure $ ExprBindingDef name bindingTyp body isTopLevel (spanningTokens defToken inc)
                TokenPipe -> do
                    arms <- parsePipePatternArms
                    let (args, _ret) = uncurryQualified bindingTyp
                    let defBody = ExprDerivedPatternMatch args arms
                    pure $ ExprBindingDef name bindingTyp defBody isTopLevel (spanningTokens defToken inc)
                _ -> throwError $ InvalidFunctionBody inc

parseImperativeBindingParam :: Parser (Token, Type)
parseImperativeBindingParam = do
    nameToken <- consume TokenLowerIdentifier
    _ <- consume TokenColon
    typ <- parseType
    pure (nameToken, typ)

ensureSameLengthMap :: [Token] -> [Type] -> Parser [(String, Type)]
ensureSameLengthMap names types
    | length names == length types = pure $ zip (map tokenValue names ++ replicate (length types - length names) "_") types
    | otherwise = throwError $ FunctionArgumentLengthMismatch (last names)
