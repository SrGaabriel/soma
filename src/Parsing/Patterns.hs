module Parsing.Patterns where

import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens)
import Parsing.Atoms (parseExpression)
import Parsing.Errors (ParsingError (InvalidPattern))
import Parsing.Parser (Parser, consume, parseFluidSequence, parseLayout, peek, withRecovery)
import Syntax.Patterns (Literal (LitInt), Pattern (..))
import Syntax.Tree (Expr (ExprPatternMatchArm))
import qualified Text.Megaparsec as MP

parseMultiplePatterns :: Parser [Pattern]
parseMultiplePatterns = parseFluidSequence TokenStrongRightArrow parseMultiPatternAtom

parseMultiPatternAtom :: Parser Pattern
parseMultiPatternAtom = parseSinglePattern True

parseSinglePattern :: Bool -> Parser Pattern
parseSinglePattern parentheziedConstructors = withRecovery parseSinglePattern' $ do
    pure PWildcard
  where
    parseSinglePattern' = do
        inc <- peek
        case tokenKind inc of
            TokenLowerIdentifier ->
                PVar . tokenValue <$> consume TokenLowerIdentifier
            TokenNumber -> do
                numToken <- consume TokenNumber
                pure $ PLit $ LitInt (read (tokenValue numToken) :: Int)
            TokenLeftParen ->
                consume TokenLeftParen
                    >> parseSinglePattern True <* consume TokenRightParen
            TokenUnderscore -> do
                _ <- consume TokenUnderscore
                pure PWildcard
            TokenUpperIdentifier | parentheziedConstructors -> do
                nameToken <- consume TokenUpperIdentifier
                patterns <- parseFluidSequence TokenRightParen (parseSinglePattern False)
                pure $ PConstructor (tokenValue nameToken) patterns
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
