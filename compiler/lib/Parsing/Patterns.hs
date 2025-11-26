module Parsing.Patterns where

import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens, tokenSpan)
import Parsing.Atoms (parseExpression)
import Parsing.Errors (ParsingError (InvalidPattern, PatternNeedsParentheses))
import Parsing.Parser (Parser, consume, parseFluidSequence, parseLayout, peek)
import Syntax.Patterns (Literal (LitInt), Pattern (..))
import Syntax.Tree (Expr (ExprPatternMatchArm))
import qualified Text.Megaparsec as MP

parseMultiplePatterns :: Parser [Pattern]
parseMultiplePatterns = parseFluidSequence TokenStrongRightArrow parseMultiPatternAtom

parseMultiPatternAtom :: Parser Pattern
parseMultiPatternAtom = parseSinglePattern False

parseSinglePattern :: Bool -> Parser Pattern
parseSinglePattern parentheziedConstructors = do
    inc <- peek
    case tokenKind inc of
        TokenLowerIdentifier -> do
            varTok <- consume TokenLowerIdentifier
            pure $ PVar (tokenValue varTok) (tokenSpan varTok)
        TokenNumber -> do
            numToken <- consume TokenNumber
            pure $ PLit (LitInt (read (tokenValue numToken) :: Int)) (tokenSpan numToken)
        TokenLeftParen ->
            consume TokenLeftParen
                >> parseSinglePattern True <* consume TokenRightParen
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
