module Parsing.Cst.Patterns (
    parsePattern,
    parseSinglePattern,
    parseMultiplePatterns,
    parsePipePatternArms,
    parseMultiPatternArm,
) where

import Control.Monad (unless, void)
import Lexing.Lexer (Token (..))
import qualified Lexing.Lexer as Lexer
import Parsing.CstBuilder
import Parsing.Errors (ParsingError (..))
import Syntax.CST.SyntaxKind
import qualified Text.Megaparsec as MP

parsePattern :: CstParser ()
parsePattern = parseSinglePattern False

parseMultiplePatterns :: CstParser ()
parseMultiplePatterns = do
    _ <- parseMultiPatternAtom
    _ <- MP.many $ do
        tok <- cstTryPeekOrEOF
        if Lexer.tokenKind tok == TokenStrongRightArrow
            then MP.empty
            else do
                _ <- parseMultiPatternAtom
                pure ()
    pure ()

parseMultiPatternAtom :: CstParser ()
parseMultiPatternAtom = parseSinglePattern False

parseSinglePattern :: Bool -> CstParser ()
parseSinglePattern parenthesizedConstructors = do
    tok <- cstPeek
    case Lexer.tokenKind tok of
        TokenLowerIdentifier -> withNode (SK_Node NK_PATTERN_VAR) $ do
            _ <- cstConsume TokenLowerIdentifier
            pure ()
        TokenNumber -> withNode (SK_Node NK_PATTERN_LITERAL) $ do
            _ <- cstConsume TokenNumber
            pure ()
        TokenLeftParen -> do
            _ <- cstConsume TokenLeftParen
            parseSinglePattern True
            _ <- cstConsume TokenRightParen
            pure ()
        TokenUnderscore -> withNode (SK_Node NK_PATTERN_WILDCARD) $ do
            _ <- cstConsume TokenUnderscore
            pure ()
        TokenUpperIdentifier
            | parenthesizedConstructors -> withNode (SK_Node NK_PATTERN_CONSTRUCTOR) $ do
                _ <- cstConsume TokenUpperIdentifier
                parseFluidSequence TokenRightParen (parseSinglePattern False)
        TokenUpperIdentifier
            | not parenthesizedConstructors ->
                MP.customFailure $ PatternNeedsParentheses tok (tokenValue tok)
        _ -> MP.customFailure $ InvalidPattern tok

parsePipePatternArms :: CstParser ()
parsePipePatternArms = parseLayout parsePipePatternArm

parsePipePatternArm :: CstParser ()
parsePipePatternArm = withNode (SK_Node NK_MATCH_ARM) $ do
    _ <- cstConsume TokenPipe
    parseMultiPatternArm True

parseMultiPatternArm :: Bool -> CstParser ()
parseMultiPatternArm multiAllowed = do
    if multiAllowed
        then parseMultiplePatterns
        else parseSinglePattern False
    _ <- cstConsume TokenStrongRightArrow
    parseExpression

-- We need to import parseExpression but that would create a cycle
-- So we'll forward declare it here and have Atoms import Patterns
parseExpression :: CstParser ()
parseExpression = do
    -- This is a simplified version, the real one is in Atoms
    parseAtoms
  where
    parseAtoms = do
        tok <- cstTryPeek
        case Lexer.tokenKind <$> tok of
            Just TokenNumber -> do
                withNode (SK_Node NK_EXPR_LITERAL) $ void (cstConsume TokenNumber)
                parseAtoms
            Just TokenLowerIdentifier -> do
                withNode (SK_Node NK_EXPR_VAR) $ void (cstConsume TokenLowerIdentifier)
                parseAtoms
            Just TokenUpperIdentifier -> do
                withNode (SK_Node NK_EXPR_CONSTRUCTOR) $ void (cstConsume TokenUpperIdentifier)
                parseAtoms
            Just TokenTrue -> do
                withNode (SK_Node NK_EXPR_LITERAL) $ void (cstConsume TokenTrue)
                parseAtoms
            Just TokenFalse -> do
                withNode (SK_Node NK_EXPR_LITERAL) $ void (cstConsume TokenFalse)
                parseAtoms
            Just TokenVarSymbol -> do
                _ <- cstConsume TokenVarSymbol
                parseAtoms
            Just TokenLeftParen -> do
                _ <- cstConsume TokenLeftParen
                parseAtoms
                _ <- MP.optional (cstConsume TokenRightParen)
                parseAtoms
            _ -> pure ()

parseFluidSequence :: TokenKind -> CstParser () -> CstParser ()
parseFluidSequence end itemParser = do
    tok <- cstTryPeekOrEOF
    unless (Lexer.tokenKind tok == end) go
  where
    go = do
        tok <- cstTryPeekOrEOF
        if Lexer.tokenKind tok == end
            then pure ()
            else do
                result <- MP.optional itemParser
                case result of
                    Nothing -> pure ()
                    Just () -> go

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
