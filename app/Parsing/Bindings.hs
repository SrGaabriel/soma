{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
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
            impParams <-
                parseSequence TokenComma TokenRightParen parseImperativeBindingParam
                    <* consume TokenRightParen

            case impParams of
                [] -> throwError $ FunctionArgumentLengthMismatch defToken
                xs  | all isSimplyTyped xs -> do
                        let params = Prelude.map (\(SimplyTypedParam (tok, typ)) -> (tok, typ)) xs
                        let (toks, types) = unzip params
                        mappings <- ensureSameLengthMap toks types
                        _ <- consume TokenRightArrow
                        returnType <- parseType
                        let bindingTyp = curryFunction types returnType
                        let bindingTypeS = Forall [] [] bindingTyp
                        eqTok <- consumeRelevant TokenEquals
                        body <- parseExpression
                        let argNames = Prelude.map Prelude.fst mappings
                        let defBody = ExprLambda argNames body (exprSpan body)
                        pure $ ExprBindingDef name bindingTypeS defBody isTopLevel (spanningTokens defToken eqTok)
                    | not (any isSimplyTyped xs) -> do
                        let paramToks = Prelude.map (\(UntypedParam tok) -> tok) xs
                        let paramNames = map tokenValue paramToks
                        _ <- consume TokenReturns
                        bindingTyp <- parseQualifiedType
                        eqTok <- consumeRelevant TokenEquals
                        body <- parseExpression
                        let defBody = ExprLambda paramNames body (exprSpan body)
                        pure $ ExprBindingDef name bindingTyp defBody isTopLevel (spanningTokens defToken eqTok)
                    | otherwise -> throwError $ FunctionArgumentLengthMismatch defToken
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
                    let (args, _ret) = uncurryQualified bindingTyp
                    arms <- parsePipePatternArms args
                    let defBody = ExprDerivedPatternMatch args arms
                    pure $ ExprBindingDef name bindingTyp defBody isTopLevel (spanningTokens defToken inc)
                _ -> throwError $ InvalidFunctionBody inc

parseImperativeBindingParam :: Parser ImperativeFuncParam
parseImperativeBindingParam = do
    nameToken <- consume TokenLowerIdentifier
    inc <- peekRelevant
    case tokenKind inc of
        TokenColon -> do
            _ <- next
            typ <- parseType
            pure $ SimplyTypedParam (nameToken, typ)
        _ -> do
            pure $ UntypedParam nameToken

ensureSameLengthMap :: [Token] -> [b] -> Parser [(String, b)]
ensureSameLengthMap names types
    | length names == length types = pure $ zip (map tokenValue names ++ replicate (length types - length names) "_") types
    | otherwise = throwError $ FunctionArgumentLengthMismatch (last names)

data ImperativeFuncParam = SimplyTypedParam (Token, Type) | UntypedParam Token
    deriving (Show, Eq)

isSimplyTyped :: ImperativeFuncParam -> Bool
isSimplyTyped (SimplyTypedParam _) = True
isSimplyTyped (UntypedParam _) = False