{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Parsing.Atoms where

import qualified Debug.Trace as Debug

import Control.Applicative ((<|>))
import Control.Monad (when)
import Control.Monad.Error.Class (MonadError (throwError))
import Data.Maybe (fromMaybe)
import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens, tokenSpan)
import Lexing.Position (Span (Span))
import Parsing.Errors (ParsingError (..))
import Parsing.Parser
import Syntax.Tree (Expr (..), modifySpan)

parseExpression :: Parser Expr
parseExpression = parseExprPrec 0

parseApplication :: Parser Expr
parseApplication = do
    atoms <-
        someAccepting
            parseAtom
            ( \case
                NotAnExpression _ -> True
                ExpectedAnExpression _ -> True
                _ -> False
            )
    if null atoms
        then do
            inc <- peek
            throwError $ ExpectedAnExpression inc
        else pure $ foldl2 ExprApp atoms
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
            pure $ ExprNum (tokenValue numToken) (tokenSpan numToken)
        TokenLeftParen -> do
            lparen <- consume TokenLeftParen
            inc <- peek
            case tokenKind inc of
                TokenLambda -> do
                    _ <- next
                    nameToks <- parseFluidSequence TokenRightArrow (consume TokenLowerIdentifier)
                    let names = map tokenValue nameToks
                    _ <- consume TokenRightArrow
                    body <- parseExpression
                    rparen <- consume TokenRightParen
                    pure $ ExprLambda names body (Span (tokenPos lparen) (tokenPos rparen))
                _ -> do
                    contents <- parseCommaSeparatedUntil TokenRightParen parseExpression
                    rparen <- consume TokenRightParen
                    let spanning = spanningTokens lparen rparen
                    case contents of
                        [first] -> pure $ modifySpan first spanning
                        _ -> pure $ ExprTuple contents spanning
        TokenLeftBracket -> do
            lbracket <- consume TokenLeftBracket
            contents <- parseCommaSeparatedUntil TokenRightBracket parseExpression
            rbracket <- consume TokenRightBracket
            let spanning = Span (tokenPos lbracket) (tokenPos rbracket)
            pure $ ExprArray contents spanning
        TokenLowerIdentifier -> do
            idToken <- next
            pure $ ExprUVar (tokenValue idToken) (tokenSpan idToken)
        TokenUpperIdentifier -> do
            idToken <- next
            pure $ ExprUVar (tokenValue idToken) (tokenSpan idToken)
        TokenString str -> do
            ExprStr str . tokenSpan <$> next
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
            ExprBool True . tokenSpan <$> next
        TokenFalse -> do
            ExprBool False . tokenSpan <$> next
        _ -> throwError $ NotAnExpression token

parseLetExpression :: Parser Expr
parseLetExpression = do
    letToken <- consume TokenLet
    identifier <- consume TokenLowerIdentifier
    Debug.traceM $ "Parsing let expression for: " ++ tokenValue identifier
    _ <- consume TokenEquals
    value <- parseExpression
    Debug.traceM $ "Parsed value: " ++ show value
    inTok <- consumeRelevant TokenIn
    Debug.traceM $ "Found 'in' token"

    mapM_ validateIndentation =<< optional (consume TokenNewline)

    body <- parseExpression
    Debug.traceM $ "Parsed body: " ++ show body

    pure
        $ ExprLet
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

operatorPrecedenceTable :: [[String]]
operatorPrecedenceTable =
    [ ["*", "/"]
    , ["+", "-"]
    , ["==", "!=", "<", ">", "<=", ">="]
    ]

getOpPrecedence :: String -> Maybe (Int, Associativity)
getOpPrecedence sym = go 0 operatorPrecedenceTable
  where
    go _ [] = Nothing
    go i (level : rest)
        | sym `elem` level = Just (length operatorPrecedenceTable - i, LeftAssoc)
        | otherwise = go (i + 1) rest

data Associativity = LeftAssoc | RightAssoc

parseExprPrec :: Int -> Parser Expr
parseExprPrec prec = do
    lhs <- parseApplication
    parseInfixRest lhs prec

parseInfixRest :: Expr -> Int -> Parser Expr
parseInfixRest lhs prec = do
    mtok <- optional peek
    case mtok of
        Just tok
            | TokenVarSymbol <- tokenKind tok
            , let opStr = tokenValue tok -> do
                let (opPrec, assoc) = fromMaybe (0, LeftAssoc) (getOpPrecedence opStr)
                if shouldContinue prec opPrec assoc
                    then do
                        _ <- next
                        rhs <- parseExprPrec (nextPrec assoc opPrec)
                        let op = ExprUVar opStr (tokenSpan tok)
                        let appL = ExprApp op lhs
                        parseInfixRest (ExprApp appL rhs) prec
                    else pure lhs
        _ -> pure lhs
  where
    shouldContinue current nextOpPrec assoc =
        case assoc of
            LeftAssoc -> nextOpPrec >= current
            RightAssoc -> nextOpPrec > current
    nextPrec assoc opPrec =
        case assoc of
            LeftAssoc -> opPrec + 1
            RightAssoc -> opPrec

parseModuleName :: Parser [String]
parseModuleName = do
    toks <- parseSequence TokenReturns TokenNewline (consume TokenVarSymbol <|> consume TokenLowerIdentifier)
    pure $ map tokenValue toks
