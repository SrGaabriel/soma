module Parsing.Atoms where

import Data.Maybe (fromMaybe)
import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens, tokenSpan)
import Lexing.Position (Span (Span))
import Parsing.Errors (ParsingError (..))
import Parsing.Parser
import Syntax.Tree
import qualified Text.Megaparsec as MP

parseExpression :: Parser Expr
parseExpression = parseExprPrec 0

parseApplication :: Parser Expr
parseApplication = do
    atoms <- MP.some parseAtom
    if null atoms
        then do
            inc <- peek
            MP.customFailure $ ExpectedAnExpression inc
        else pure $ foldl2 ExprApp atoms
  where
    foldl2 _ [] = error "foldl2: empty list"
    foldl2 _ [x] = x
    foldl2 f (x : xs) = foldl f x xs

parseAtom :: Parser Expr
parseAtom = do
    token <- tryPeek
    case tokenKind <$> token of
        Just TokenNumber -> do
            numToken <- consume TokenNumber
            pure $ ExprNum (tokenValue numToken) (tokenSpan numToken)
        Just TokenLeftParen -> do
            lparen <- consume TokenLeftParen
            inc <- peek
            case tokenKind inc of
                TokenLambda -> do
                    _ <- consume TokenLambda
                    nameToks <- parseFluidSequence TokenRightArrow (consume TokenLowerIdentifier)
                    let names = map tokenValue nameToks
                    _ <- consume TokenRightArrow
                    body <- parseLambdaBody
                    rparen <- consumeRelevant TokenRightParen
                    pure $ ExprLambda names body (Span (tokenPos lparen) (tokenPos rparen))
                _ -> do
                    contents <- parseCommaSeparatedUntil TokenRightParen parseExpression
                    rparen <- consumeRelevant TokenRightParen
                    let spanning = spanningTokens lparen rparen
                    case contents of
                        [first] -> pure $ modifySpan first spanning
                        _ -> pure $ ExprTuple contents spanning
        Just TokenLeftBracket -> do
            lbracket <- consume TokenLeftBracket
            contents <- parseCommaSeparatedUntil TokenRightBracket parseExpression
            rbracket <- consume TokenRightBracket
            let spanning = Span (tokenPos lbracket) (tokenPos rbracket)
            pure $ ExprArray contents spanning
        Just TokenLowerIdentifier -> do
            idToken <- consume TokenLowerIdentifier
            pure $ ExprUVar (tokenValue idToken) (tokenSpan idToken)
        Just TokenUpperIdentifier -> do
            idToken <- consume TokenUpperIdentifier
            pure $ ExprUVar (tokenValue idToken) (tokenSpan idToken)
        Just (TokenString str) -> do
            strToken <- consume (TokenString str)
            pure $ ExprStr str (tokenSpan strToken)
        Just TokenLet -> parseLetExpression
        Just TokenDollar -> do
            _ <- consume TokenDollar
            parseExpression
        Just TokenTrue -> do
            trueToken <- consume TokenTrue
            pure $ ExprBool True (tokenSpan trueToken)
        Just TokenFalse -> do
            falseToken <- consume TokenFalse
            pure $ ExprBool False (tokenSpan falseToken)
        Just TokenCompose -> parseCompose
        Just TokenIf -> parseIf
        _ -> MP.empty

parseLetExpression :: Parser Expr
parseLetExpression = do
    letToken <- consume TokenLet
    identifier <- consume TokenLowerIdentifier
    _ <- consume TokenEquals
    value <- parseExpression
    inTok <- consume TokenIn
    _ <- MP.optional $ consume TokenLayoutSeparator
    body <- parseExpression

    pure
        $ ExprLet
            { letName = tokenValue identifier
            , letValue = value
            , letBody = body
            , letSpan = Span (tokenPos letToken) (tokenPos inTok)
            }

{- | Parse a lambda body, handling optional layout blocks that the lexer may insert
after the arrow when the body is on a new indented line.
-}
parseLambdaBody :: Parser Expr
parseLambdaBody = do
    tok <- tryPeek
    case tokenKind <$> tok of
        Just TokenLayoutStart -> do
            _ <- consume TokenLayoutStart
            expr <- parseLayoutBody
            _ <- consume TokenLayoutEnd
            pure expr
        _ -> parseExpression
  where
    -- Parse expressions within a layout block, consuming layout separators
    parseLayoutBody :: Parser Expr
    parseLayoutBody = do
        expr <- parseExpression
        next <- tryPeek
        case tokenKind <$> next of
            Just TokenLayoutSeparator -> do
                _ <- consume TokenLayoutSeparator
                parseLayoutBody
            _ -> pure expr

operatorPrecedenceTable :: [[String]]
operatorPrecedenceTable =
    [ ["*", "/", "%"]
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
    lhs <- withRecovery parseApplication $ do
        actualToken <- tryPeekOrEOF
        MP.customFailure $ ExpectedAnExpression actualToken
    parseInfixRest lhs prec

parseInfixRest :: Expr -> Int -> Parser Expr
parseInfixRest lhs prec = do
    mtok <- tryPeek
    case mtok of
        Just tok
            | TokenVarSymbol <- tokenKind tok
            , let opStr = tokenValue tok -> do
                let (opPrec, assoc) = fromMaybe (0, LeftAssoc) (getOpPrecedence opStr)
                if shouldContinue prec opPrec assoc
                    then do
                        _ <- consume TokenVarSymbol
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
    toks <- parseExhaustiveSequence TokenSlash (consumeAnyOf [TokenVarSymbol, TokenLowerIdentifier])
    pure $ map tokenValue toks

parseCompose :: Parser Expr
parseCompose = do
    composeTok <- consume TokenCompose
    stmts <- parseLayout parseComposeStmt
    pure $ ExprCompose stmts (tokenSpan composeTok)

parseComposeStmt :: Parser ComposeStmt
parseComposeStmt = do
    tok <- tryPeek
    case tokenKind <$> tok of
        Just TokenBind -> do
            bindTok <- consume TokenBind
            nameTok <- consume TokenLowerIdentifier
            _ <- consume TokenLeftArrow
            val <- parseExpression
            pure $ CSBind (tokenValue nameTok) val (spanningTokens bindTok nameTok)
        Just TokenLet -> do
            letTok <- consume TokenLet
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
