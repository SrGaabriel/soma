module Parsing.Cst.Helpers (
    parseCommaSeparatedUntil,
    parseFluidSequence,
    parseExhaustiveSequence,
    parseLayout,
    parseOptionallyLayout,
    parseOptionallyInLayout,
) where

import Control.Monad (unless)
import Lexing.Lexer (TokenKind (..))
import qualified Lexing.Lexer as Lexer
import Parsing.CstBuilder
import qualified Text.Megaparsec as MP

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

parseExhaustiveSequence :: TokenKind -> CstParser () -> CstParser ()
parseExhaustiveSequence separator itemParser = do
    _ <- itemParser
    _ <- MP.many $ do
        tok <- cstTryPeekOrEOF
        if Lexer.tokenKind tok == separator
            then do
                _ <- cstConsume separator
                _ <- itemParser
                pure ()
            else MP.empty
    pure ()

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

parseOptionallyLayout :: CstParser () -> CstParser ()
parseOptionallyLayout itemParser = do
    tok <- cstTryPeek
    case Lexer.tokenKind <$> tok of
        Just TokenLayoutStart -> parseLayout itemParser
        _ -> pure ()

parseOptionallyInLayout :: CstParser () -> CstParser ()
parseOptionallyInLayout p = do
    tok <- cstTryPeek
    case Lexer.tokenKind <$> tok of
        Just TokenLayoutStart -> do
            _ <- cstConsume TokenLayoutStart
            p
            _ <- cstConsume TokenLayoutEnd
            pure ()
        _ -> p
