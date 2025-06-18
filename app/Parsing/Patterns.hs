module Parsing.Patterns where

import Control.Monad.Error.Class (MonadError (throwError))
import Lexing.Lexer (Token (..), TokenKind (..))
import Parsing.Atoms (parseExpression)
import Parsing.Errors (ParsingError (InvalidPattern))
import Parsing.Parser (Parser, consume, next, parseFluidSequence, parseIndentedBlock)
import Syntax.Patterns (Literal (LitInt), Pattern (..))
import Syntax.Tree (MultiPatternArm (MultiPatternArm))

parseMultiplePatterns :: Parser [Pattern]
parseMultiplePatterns = parseFluidSequence TokenStrongRightArrow parseMultiPatternAtom

parseMultiPatternAtom :: Parser Pattern
parseMultiPatternAtom = parseSinglePattern True

parseSinglePattern :: Bool -> Parser Pattern
parseSinglePattern parentheziedConstructors = do
    inc <- next
    case tokenKind inc of
        TokenLowerIdentifier -> do
            nameToken <- next
            pure $ PVar (tokenValue nameToken)
        TokenNumber -> do
            numToken <- next
            pure $ PLit $ LitInt (read (tokenValue numToken) :: Integer)
        TokenLeftParen ->
            parseSinglePattern True <* consume TokenRightParen
        TokenUnderscore -> do
            _ <- next
            pure PWildcard
        TokenUpperIdentifier | parentheziedConstructors -> do
            nameToken <- next
            patterns <- parseFluidSequence TokenRightParen (parseSinglePattern False)
            pure $ PConstructor (tokenValue nameToken) patterns
        _ -> throwError $ InvalidPattern inc

parsePipePatternArms :: Parser [MultiPatternArm]
parsePipePatternArms = parseIndentedBlock 0 parsePipePatternArm

parsePipePatternArm :: Parser MultiPatternArm
parsePipePatternArm = do
    _ <- consume TokenPipe
    parseMultiPatternArm True

parseMultiPatternArm :: Bool -> Parser MultiPatternArm
parseMultiPatternArm multiAllowed = do
    patterns <-
        if multiAllowed
            then do
                parseMultiplePatterns
            else
                (: []) <$> parseSinglePattern False
    _ <- consume TokenStrongRightArrow
    body <- parseExpression
    pure $ MultiPatternArm patterns body
