module Parsing.Cst.Atoms (
    parseExpression,
    parseApplication,
    parseAtom,
    parseModuleName,
    parseCompose,
    parseComposeStmt,
    parseIf,
    parseLetExpression,
) where

import Control.Monad (when)
import Data.Maybe (fromMaybe)
import Lexing.Lexer (Token (..))
import qualified Lexing.Lexer as Lexer
import Parsing.CstBuilder
import Syntax.CST.SyntaxKind
import qualified Text.Megaparsec as MP

parseExpression :: CstParser ()
parseExpression = parseExprPrec 0

parseApplication :: CstParser ()
parseApplication = withNode (SK_Node NK_EXPR_APP) $ do
    _ <- parseAtom
    _ <- MP.many parseAtom
    pure ()

parseAtom :: CstParser ()
parseAtom = do
    tok <- cstTryPeek
    case Lexer.tokenKind <$> tok of
        Just TokenNumber -> withNode (SK_Node NK_EXPR_LITERAL) $ do
            _ <- cstConsume TokenNumber
            pure ()
        Just TokenLeftParen -> parseParenExpr
        Just TokenLeftBracket -> parseArrayExpr
        Just TokenLowerIdentifier -> withNode (SK_Node NK_EXPR_VAR) $ do
            _ <- cstConsume TokenLowerIdentifier
            pure ()
        Just TokenUpperIdentifier -> withNode (SK_Node NK_EXPR_CONSTRUCTOR) $ do
            _ <- cstConsume TokenUpperIdentifier
            pure ()
        Just (TokenString _) -> withNode (SK_Node NK_EXPR_LITERAL) $ do
            _ <- cstSatisfy (\t -> case Lexer.tokenKind t of TokenString _ -> True; _ -> False)
            pure ()
        Just TokenLet -> parseLetExpression
        Just TokenDollar -> do
            _ <- cstConsume TokenDollar
            parseExpression
        Just TokenTrue -> withNode (SK_Node NK_EXPR_LITERAL) $ do
            _ <- cstConsume TokenTrue
            pure ()
        Just TokenFalse -> withNode (SK_Node NK_EXPR_LITERAL) $ do
            _ <- cstConsume TokenFalse
            pure ()
        Just TokenCompose -> parseCompose
        Just TokenIf -> parseIf
        _ -> MP.empty

parseParenExpr :: CstParser ()
parseParenExpr = do
    _ <- cstConsume TokenLeftParen
    tok <- cstPeek
    case Lexer.tokenKind tok of
        TokenLambda -> withNode (SK_Node NK_EXPR_LAMBDA) $ do
            _ <- cstConsume TokenLambda
            withNode (SK_Node NK_PARAM_LIST) $ do
                _ <- parseFluidSequence TokenRightArrow (cstConsume TokenLowerIdentifier)
                pure ()
            _ <- cstConsume TokenRightArrow
            _ <- parseExpression
            _ <- cstConsume TokenRightParen
            pure ()
        TokenRightParen -> withNode (SK_Node NK_EXPR_TUPLE) $ do
            _ <- cstConsume TokenRightParen
            pure ()
        _ -> do
            parseExpressionReturning
            tok' <- cstTryPeek
            case Lexer.tokenKind <$> tok' of
                Just TokenComma -> withNode (SK_Node NK_EXPR_TUPLE) $ do
                    _ <- parseCommaSeparatedRest
                    _ <- cstConsume TokenRightParen
                    pure ()
                Just TokenRightParen -> withNode (SK_Node NK_EXPR_PARENS) $ do
                    _ <- cstConsume TokenRightParen
                    pure ()
                _ -> do
                    _ <- cstConsume TokenRightParen
                    pure ()
  where
    parseExpressionReturning = parseExpression
    parseCommaSeparatedRest = MP.many $ do
        _ <- cstConsume TokenComma
        parseExpression

parseArrayExpr :: CstParser ()
parseArrayExpr = withNode (SK_Node NK_EXPR_LIST) $ do
    _ <- cstConsume TokenLeftBracket
    parseCommaSeparatedUntil TokenRightBracket parseExpression
    _ <- cstConsume TokenRightBracket
    pure ()

parseLetExpression :: CstParser ()
parseLetExpression = withNode (SK_Node NK_EXPR_LET) $ do
    _ <- cstConsume TokenLet
    _ <- cstConsume TokenLowerIdentifier
    _ <- cstConsume TokenEquals
    parseExpression
    _ <- cstConsume TokenIn
    _ <- MP.optional (cstConsume TokenLayoutSeparator)
    parseExpression

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

parseExprPrec :: Int -> CstParser ()
parseExprPrec prec = do
    parseApplication
    parseInfixRest prec

parseInfixRest :: Int -> CstParser ()
parseInfixRest prec = do
    mtok <- cstTryPeek
    case mtok of
        Just tok
            | TokenVarSymbol <- Lexer.tokenKind tok
            , let opStr = tokenValue tok -> do
                let (opPrec, assoc) = fromMaybe (0, LeftAssoc) (getOpPrecedence opStr)
                when (shouldContinue prec opPrec assoc) $ do
                    _ <- cstConsume TokenVarSymbol
                    parseExprPrec (nextPrec assoc opPrec)
                    parseInfixRest prec
        _ -> pure ()
  where
    shouldContinue current nextOpPrec assoc =
        case assoc of
            LeftAssoc -> nextOpPrec >= current
            RightAssoc -> nextOpPrec > current
    nextPrec assoc opPrec =
        case assoc of
            LeftAssoc -> opPrec + 1
            RightAssoc -> opPrec

parseModuleName :: CstParser [String]
parseModuleName = withNode (SK_Node NK_QUALIFIED_NAME) $ do
    toks <- parseExhaustiveSequence TokenSlash (cstConsumeAnyOf [TokenVarSymbol, TokenLowerIdentifier])
    pure $ map tokenValue toks

parseCompose :: CstParser ()
parseCompose = withNode (SK_Node NK_EXPR_COMPOSE) $ do
    _ <- cstConsume TokenCompose
    parseLayout parseComposeStmt

parseComposeStmt :: CstParser ()
parseComposeStmt = do
    tok <- cstTryPeek
    case Lexer.tokenKind <$> tok of
        Just TokenBind -> withNode (SK_Node NK_COMPOSE_BIND) $ do
            _ <- cstConsume TokenBind
            _ <- cstConsume TokenLowerIdentifier
            _ <- cstConsume TokenLeftArrow
            parseExpression
        Just TokenLet -> withNode (SK_Node NK_COMPOSE_LET) $ do
            _ <- cstConsume TokenLet
            _ <- cstConsume TokenLowerIdentifier
            _ <- cstConsume TokenEquals
            parseExpression
        _ -> withNode (SK_Node NK_COMPOSE_STMT) $ do
            parseExpression

parseIf :: CstParser ()
parseIf = withNode (SK_Node NK_EXPR_IF) $ do
    _ <- cstConsume TokenIf
    parseExpression
    _ <- cstConsume TokenThen
    parseExpression
    _ <- cstConsume TokenElse
    parseExpression

-- Helper: parse comma-separated items until end token
parseCommaSeparatedUntil :: TokenKind -> CstParser () -> CstParser ()
parseCommaSeparatedUntil end itemParser = do
    tok <- cstTryPeekOrEOF
    if Lexer.tokenKind tok == end
        then pure ()
        else do
            itemParser
            parseRest
  where
    parseRest = do
        tok <- cstTryPeekOrEOF
        case Lexer.tokenKind tok of
            k | k == end -> pure ()
            TokenComma -> do
                _ <- cstConsume TokenComma
                itemParser
                parseRest
            _ -> pure ()

-- Helper: parse fluid sequence (items until end token, no separator)
parseFluidSequence :: TokenKind -> CstParser a -> CstParser [a]
parseFluidSequence end itemParser = do
    tok <- cstTryPeekOrEOF
    if Lexer.tokenKind tok == end
        then pure []
        else do
            first <- itemParser
            rest <- go
            pure (first : rest)
  where
    go = do
        tok <- cstTryPeekOrEOF
        if Lexer.tokenKind tok == end
            then pure []
            else do
                item <- MP.optional itemParser
                case item of
                    Nothing -> pure []
                    Just x -> do
                        xs <- go
                        pure (x : xs)

-- Helper: parse exhaustive sequence (items separated by token)
parseExhaustiveSequence :: TokenKind -> CstParser a -> CstParser [a]
parseExhaustiveSequence separator itemParser = do
    first <- itemParser
    rest <- MP.many $ do
        tok <- cstTryPeekOrEOF
        if Lexer.tokenKind tok == separator
            then do
                _ <- cstConsume separator
                itemParser
            else MP.empty
    pure (first : rest)

-- Helper: parse layout block
parseLayout :: CstParser () -> CstParser ()
parseLayout itemParser = do
    _ <- cstConsume TokenLayoutStart
    parseLayoutItems
    _ <- cstConsume TokenLayoutEnd
    pure ()
  where
    parseLayoutItems = do
        tok <- cstTryPeekOrEOF
        if Lexer.tokenKind tok == TokenLayoutEnd
            then pure ()
            else do
                itemParser
                tok' <- cstTryPeekOrEOF
                case Lexer.tokenKind tok' of
                    TokenLayoutSeparator -> do
                        _ <- cstConsume TokenLayoutSeparator
                        parseLayoutItems
                    TokenLayoutEnd -> pure ()
                    _ -> parseLayoutItems
