{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
module Parsing.Atoms where

import Parsing.Parser (Parser, peek, next, consume, parseSequence, parseCommaSeparatedUntil, parseIndentedBlock, someAccepting, optional, consumeRelevant)
import Syntax.Tree (Expr (..))
import Parsing.Errors (ParsingError(..))
import Lexing.Lexer (TokenKind(..), Token (..), tokenSpan)
import Control.Monad.Error.Class (MonadError(throwError))
import Lexing.Position (Span(Span))
import Syntax.Ops (BinaryOp(..))
import qualified Debug.Trace as Debug
import Control.Monad (when)

parseExpression :: Parser Expr
parseExpression = parseNumericExpression

parseNumericExpression :: Parser Expr
parseNumericExpression = parseBinaryOp parseTerm [TokenPlus, TokenMinus]

parseTerm :: Parser Expr
parseTerm = parseBinaryOp parseApplication [TokenAsterisk, TokenSlash]

parseApplication :: Parser Expr
parseApplication = do
    atoms <-
        someAccepting
            parseAtom
            ( \err -> case err of
                NotAnExpression _ -> True
                ExpectedAnExpression _ -> True
                _ -> False
            )
    if atoms == []
        then do
            inc <- peek
            throwError $ ExpectedAnExpression inc
        else pure $ foldl2 (\f arg -> ExprApp f arg) atoms
  where
    foldl2 _ [] = error "foldl2: empty list"
    foldl2 _ [x] = x
    foldl2 f (x : xs) = foldl f x xs

parseAtom :: Parser Expr
parseAtom = do
    token <- peek
    case tokenKind token of
        TokenNumber -> do
            numToken <- next
            pure $ ExprNum (read $ tokenValue numToken) (tokenSpan numToken)
        TokenLeftParen -> do
            lparen <- consume TokenLeftParen
            inc <- peek
            case tokenKind inc of
                TokenLambda -> do
                    _ <- next
                    nameToks <- parseSequence TokenDot TokenRightArrow (consume TokenIdentifier)
                    let names = map tokenValue nameToks
                    _ <- consume TokenRightArrow
                    body <- parseExpression
                    rparen <- consume TokenRightParen
                    pure $ ExprLambda names body (Span (tokenPos lparen) (tokenPos rparen))
                _ -> do
                    contents <- parseCommaSeparatedUntil TokenRightParen parseExpression
                    rb <- consume TokenRightParen
                    let spanning = Span (tokenPos lparen) (tokenPos rb)
                    case contents of
                        (first : []) -> pure first
                        _ -> pure $ ExprTuple contents spanning
        TokenLeftBracket -> do
            lbracket <- consume TokenLeftBracket
            contents <- parseCommaSeparatedUntil TokenRightBracket parseExpression
            rbracket <- consume TokenRightBracket
            let spanning = Span (tokenPos lbracket) (tokenPos rbracket)
            pure $ ExprArray contents spanning
        TokenIdentifier -> do
            idToken <- next
            pure $ ExprVar (tokenValue idToken) (tokenSpan idToken)
        TokenString -> do
            stringToken <- next
            pure $ ExprStr (tokenValue stringToken) (tokenSpan stringToken)
        TokenLet -> parseLetExpression
        TokenDollar -> do
            _dollar <- next
            parseExpression
        TokenDo -> do
            doToken <- next
            let indent = tokenIndent doToken
            block <- parseIndentedBlock indent parseExpression
            pure $ ExprBlock block (tokenSpan doToken)
        TokenTrue -> do
            trueToken <- next
            pure $ ExprBool True (tokenSpan trueToken)
        TokenFalse -> do
            falseToken <- next
            pure $ ExprBool False (tokenSpan falseToken)
        _ -> throwError $ NotAnExpression token

parseBinaryOp :: Parser Expr -> [TokenKind] -> Parser Expr
parseBinaryOp term operatorTokens = do
    left <- term
    loop left
  where
    loop left = do
        mt <- optional peek
        case mt of
            Just t
                | tokenKind t `elem` operatorTokens
                , Just op <- toBinaryOp (tokenKind t) -> do
                    _ <- next
                    right <- term
                    loop $ ExprBinaryOp op left right
            _ -> pure left

toBinaryOp :: TokenKind -> Maybe BinaryOp
toBinaryOp = \case
    TokenPlus -> Just BinaryAdd
    TokenMinus -> Just BinarySubtract
    TokenAsterisk -> Just BinaryMultiply
    TokenSlash -> Just BinaryDivide
    _ -> Nothing

parseLetExpression :: Parser Expr
parseLetExpression = do
    letToken <- consume TokenLet
    identifier <- consume TokenIdentifier
    _ <- consume TokenEquals
    value <- parseExpression
    inTok <- consumeRelevant TokenIn

    mapM_ validateIndentation =<< optional (consume TokenNewline)

    body <- parseExpression

    pure $ ExprLet
        { letName = tokenValue identifier
        , letValue = value
        , letBody = body
        , letSpan = Span (tokenPos letToken) (tokenPos inTok)
        }
  where
    validateIndentation newline =
        let actualIndent = length (tokenValue newline)
            expectedIndent = tokenIndent newline
        in when (actualIndent /= expectedIndent)
            $ throwError
            $ ExpectedDifferentIndentation newline expectedIndent actualIndent