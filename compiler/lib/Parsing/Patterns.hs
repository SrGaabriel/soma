module Parsing.Patterns where

import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens, tokenSpan)
import Lexing.Position (Span (..))
import Parsing.Atoms (parseExpression)
import Parsing.Errors (ParsingError (InvalidPattern, PatternNeedsParentheses))
import Parsing.Parser (Parser, consume, parseFluidSequence, parseLayout, peek)
import Syntax.Patterns (Literal (LitInt), ParsedPattern, Pattern (..), patternSpan)
import Syntax.Tree (Expr (ExprPatternMatchArm))
import qualified Text.Megaparsec as MP

parseMultiplePatterns :: Parser [ParsedPattern]
parseMultiplePatterns = parseFluidSequence TokenStrongRightArrow parseMultiPatternAtom

parseMultiPatternAtom :: Parser ParsedPattern
parseMultiPatternAtom = parseSinglePattern False

parseSinglePattern :: Bool -> Parser ParsedPattern
parseSinglePattern parentheziedConstructors = do
    inc <- peek
    case tokenKind inc of
        TokenLowerIdentifier -> do
            varTok <- consume TokenLowerIdentifier
            pure $ PVar (tokenValue varTok) (tokenSpan varTok)
        TokenNumber -> do
            numToken <- consume TokenNumber
            pure $ PLit (LitInt (read (tokenValue numToken) :: Int)) (tokenSpan numToken)
        TokenLeftParen -> do
            lparen <- consume TokenLeftParen
            innerPat <- parseSinglePattern True
            nextTok <- peek
            case tokenKind nextTok of
                TokenColon -> do
                    -- Cons pattern: (x:xs) or (x:y:zs)
                    tailPat <- parseConsTail
                    rparen <- consume TokenRightParen
                    pure $ PCons innerPat tailPat (spanningTokens lparen rparen)
                _ -> do
                    _ <- consume TokenRightParen
                    pure innerPat
        TokenLeftBracket -> do
            -- List literal pattern: [x, y, z] or []
            lbracket <- consume TokenLeftBracket
            nextTok <- peek
            case tokenKind nextTok of
                TokenRightBracket -> do
                    rbracket <- consume TokenRightBracket
                    pure $ PArray [] (spanningTokens lbracket rbracket)
                _ -> do
                    pats <- parseCommaSeparatedPatterns
                    rbracket <- consume TokenRightBracket
                    pure $ PArray pats (spanningTokens lbracket rbracket)
        TokenUnderscore -> do
            PWildcard . tokenSpan <$> consume TokenUnderscore
        TokenUpperIdentifier | parentheziedConstructors -> do
            nameToken <- consume TokenUpperIdentifier
            patterns <- parseFluidSequence TokenRightParen (parseSinglePattern False)
            pure $ PConstructor (tokenValue nameToken) patterns (tokenSpan nameToken)
        TokenUpperIdentifier
            | not parentheziedConstructors ->
                MP.customFailure $ PatternNeedsParentheses inc (tokenValue inc)
        _ -> MP.customFailure $ InvalidPattern inc

{- | Parse the tail of a cons pattern (after the first colon)
This handles chained cons like x:y:zs
-}
parseConsTail :: Parser ParsedPattern
parseConsTail = do
    _ <- consume TokenColon
    headPat <- parseSinglePattern True
    nextTok <- peek
    case tokenKind nextTok of
        TokenColon -> do
            -- Another cons: y:zs
            tailPat <- parseConsTail
            let Span start _ = patternSpan headPat
                Span _ end = patternSpan tailPat
            pure $ PCons headPat tailPat (Span start end)
        _ -> pure headPat

-- | Parse comma-separated patterns for list literals
parseCommaSeparatedPatterns :: Parser [ParsedPattern]
parseCommaSeparatedPatterns = do
    firstPat <- parseSinglePattern True
    rest <- MP.many $ do
        _ <- consume TokenComma
        parseSinglePattern True
    pure (firstPat : rest)

parsePipePatternArms :: Parser [Expr]
parsePipePatternArms = parseLayout parsePipePatternArm

parsePipePatternArm :: Parser Expr
parsePipePatternArm = do
    _ <- consume TokenPipe
    parseMultiPatternArm True

parseMultiPatternArm :: Bool -> Parser Expr
parseMultiPatternArm multiAllowed = do
    currentTok <- peek
    patterns <-
        if multiAllowed
            then parseMultiplePatterns
            else (: []) <$> parseSinglePattern False

    arrowTok <- consume TokenStrongRightArrow
    body <- parseExpression
    pure $ ExprPatternMatchArm patterns body (spanningTokens currentTok arrowTok)
