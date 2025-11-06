{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Parsing.Atoms where

import Control.Applicative ((<|>))
import Control.Monad (when)
import Control.Monad.Error.Class (MonadError (throwError))
import Data.Maybe (fromMaybe)
import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens, tokenSpan)
import Lexing.Position (Span (Span))
import Parsing.Errors (ParsingError (..))
import Parsing.Parser
import Syntax.Tree (ComposeStmt (..), Expr (..), exprSpan, modifySpan)

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
        TokenTrue -> do
            ExprBool True . tokenSpan <$> next
        TokenFalse -> do
            ExprBool False . tokenSpan <$> next
        TokenCompose -> parseCompose
        TokenIf -> parseIf
        _ -> throwError $ NotAnExpression token

parseLetExpression :: Parser Expr
parseLetExpression = do
    letToken <- consume TokenLet
    identifier <- consume TokenLowerIdentifier
    _ <- consume TokenEquals
    value <- parseExpression
    inTok <- consumeRelevant TokenIn

    mapM_ validateIndentation =<< optional (consume TokenNewline)

    body <- parseExpression

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
    toks <- parseExhaustiveSequence TokenSlash (consume TokenVarSymbol <|> consume TokenLowerIdentifier)
    pure $ map tokenValue toks

parseCompose :: Parser Expr
parseCompose = do
    composeTok <- consume TokenCompose
    stmts <- parseIndentedBlock (tokenIndent composeTok) parseComposeStmt
    pure $ ExprCompose stmts (tokenSpan composeTok)

parseComposeStmt :: Parser ComposeStmt
parseComposeStmt = do
    tok <- peek
    case tokenKind tok of
        TokenBind -> do
            bindTok <- next
            nameTok <- consume TokenLowerIdentifier
            _ <- consume TokenLeftArrow
            val <- parseExpression
            pure $ CSBind (tokenValue nameTok) val (spanningTokens bindTok nameTok)
        TokenLet -> do
            letTok <- next
            nameTok <- consume TokenLowerIdentifier
            _ <- consume TokenEquals
            val <- parseExpression
            pure $ CSLet (tokenValue nameTok) val (spanningTokens letTok nameTok)
        _ -> do
            e <- parseExpression
            pure $ CSExpr e (exprSpan e)

parseIf :: Parser Expr
parseIf = do
    ifToken <- consume TokenIf
    condition <- parseExpression
    _ <- consume TokenThen
    body <- parseExpression
    _ <- consume TokenElse
    elseBody <- parseExpression
    let Span _ elseEnd = exprSpan elseBody
    pure
        ExprIf
            { ifCondition = condition
            , ifBody = body
            , ifElseBody = elseBody
            , ifSpan = Span (tokenPos ifToken) elseEnd
            }
