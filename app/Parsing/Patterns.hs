module Parsing.Patterns where

import Control.Monad.Error.Class (MonadError (throwError))
import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens)
import Parsing.Atoms (parseExpression)
import Parsing.Errors (ParsingError (InvalidPattern))
import Parsing.Parser (Parser, consume, next, parseFluidSequence, parseIndentedBlock, peek)
import Syntax.Patterns (Literal (LitInt), Pattern (..))
import Syntax.Tree (Expr (ExprPatternMatchArm))
import Typing.Types (QualifiedType)

parseMultiplePatterns :: Parser [Pattern]
parseMultiplePatterns = parseFluidSequence TokenStrongRightArrow parseMultiPatternAtom

parseMultiPatternAtom :: Parser Pattern
parseMultiPatternAtom = parseSinglePattern True

parseSinglePattern :: Bool -> Parser Pattern
parseSinglePattern parentheziedConstructors = do
    inc <- peek
    case tokenKind inc of
        TokenLowerIdentifier ->
            PVar . tokenValue <$> next
        TokenNumber -> do
            numToken <- next
            pure $ PLit $ LitInt (read (tokenValue numToken) :: Integer)
        TokenLeftParen ->
            next >> parseSinglePattern True <* consume TokenRightParen
        TokenUnderscore -> do
            _ <- next
            pure PWildcard
        TokenUpperIdentifier | parentheziedConstructors -> do
            nameToken <- next
            patterns <- parseFluidSequence TokenRightParen (parseSinglePattern False)
            pure $ PConstructor (tokenValue nameToken) patterns
        _ -> throwError $ InvalidPattern inc

parsePipePatternArms :: [QualifiedType] -> Parser [Expr]
parsePipePatternArms typs = parseIndentedBlock 0 (parsePipePatternArm typs)

parsePipePatternArm :: [QualifiedType] -> Parser Expr
parsePipePatternArm typs = do
    _ <- consume TokenPipe
    parseMultiPatternArm typs True

parseMultiPatternArm :: [QualifiedType] -> Bool -> Parser Expr
parseMultiPatternArm typs multiAllowed = do
    currentTok <- peek
    patterns <-
        if multiAllowed
            then do
                parseMultiplePatterns
            else
                (: []) <$> parseSinglePattern False
    arrowTok <- consume TokenStrongRightArrow
    body <- parseExpression
    pure $ ExprPatternMatchArm patterns typs body (spanningTokens currentTok arrowTok)
