module Parsing.Cst.Types (
    parseType,
    parseQualifiedType,
    parseConstraint,
    parseKind,
    parseTyVar,
) where

import Control.Monad (void, when)
import Lexing.Lexer (Token (..))
import qualified Lexing.Lexer as Lexer
import Parsing.CstBuilder
import Parsing.Errors (ParsingError (..))
import Syntax.CST.SyntaxKind
import qualified Text.Megaparsec as MP

parseQualifiedType :: CstParser ()
parseQualifiedType = do
    parseType
    tok <- cstTryPeekOrEOF
    when (Lexer.tokenKind tok == TokenWith) $ do
        _ <- cstConsume TokenWith
        parseConstraints

parseConstraints :: CstParser ()
parseConstraints = do
    tok <- cstTryPeekOrEOF
    case Lexer.tokenKind tok of
        TokenLeftParen -> do
            _ <- cstConsume TokenLeftParen
            parseCommaSeparatedUntil TokenRightParen parseConstraint
            void $ cstConsume TokenRightParen
        _ -> parseExhaustiveSequence TokenComma parseConstraint

parseConstraint :: CstParser ()
parseConstraint = withNode (SK_Node NK_CONSTRAINT) $ do
    parseAtomicType

parseType :: CstParser ()
parseType = do
    parseBaseType
    parseTypeRest

parseTypeRest :: CstParser ()
parseTypeRest = do
    tok <- cstTryPeekOrEOF
    case Lexer.tokenKind tok of
        TokenRightArrow -> withNode (SK_Node NK_TYPE_ARROW) $ do
            _ <- cstConsume TokenRightArrow
            parseType
        _ -> do
            result <- tryParseBaseType
            case result of
                Nothing -> pure ()
                Just () -> parseTypeRest

parseBaseType :: CstParser ()
parseBaseType = do
    result <- tryParseBaseType
    case result of
        Just () -> pure ()
        Nothing -> do
            tok <- cstPeek
            MP.customFailure $ InvalidTokenForType tok

tryParseBaseType :: CstParser (Maybe ())
tryParseBaseType = do
    tok <- cstTryPeekOrEOF
    case Lexer.tokenKind tok of
        TokenLeftParen -> do
            _ <- cstConsume TokenLeftParen
            tok' <- cstTryPeekOrEOF
            if Lexer.tokenKind tok' == TokenRightParen
                then withNode (SK_Node NK_TYPE_TUPLE) $ do
                    _ <- cstConsume TokenRightParen
                    pure (Just ())
                else do
                    parseType
                    tok'' <- cstTryPeekOrEOF
                    case Lexer.tokenKind tok'' of
                        TokenComma -> withNode (SK_Node NK_TYPE_TUPLE) $ do
                            _ <- parseCommaSeparatedRest
                            _ <- cstConsume TokenRightParen
                            pure (Just ())
                        TokenRightParen -> withNode (SK_Node NK_TYPE_PARENS) $ do
                            _ <- cstConsume TokenRightParen
                            pure (Just ())
                        _ -> do
                            _ <- cstConsume TokenRightParen
                            pure (Just ())
        TokenLeftBracket -> withNode (SK_Node NK_TYPE_LIST) $ do
            _ <- cstConsume TokenLeftBracket
            parseType
            _ <- cstConsume TokenRightBracket
            pure (Just ())
        TokenUpperIdentifier -> withNode (SK_Node NK_TYPE_CONSTRUCTOR) $ do
            _ <- cstConsume TokenUpperIdentifier
            pure (Just ())
        TokenLowerIdentifier -> withNode (SK_Node NK_TYPE_VAR) $ do
            _ <- cstConsume TokenLowerIdentifier
            pure (Just ())
        _ -> pure Nothing
  where
    parseCommaSeparatedRest = MP.many $ do
        _ <- cstConsume TokenComma
        _ <- parseType
        pure ()

parseAtomicType :: CstParser ()
parseAtomicType = do
    parseAtomicBase
    parseApps
  where
    parseApps = do
        tok <- cstTryPeekOrEOF
        case Lexer.tokenKind tok of
            TokenUpperIdentifier -> do
                parseAtomicBase
                parseApps
            TokenLowerIdentifier -> do
                parseAtomicBase
                parseApps
            _ -> pure ()

parseAtomicBase :: CstParser ()
parseAtomicBase = do
    tok <- cstTryPeekOrEOF
    case Lexer.tokenKind tok of
        TokenUpperIdentifier -> withNode (SK_Node NK_TYPE_CONSTRUCTOR) $ do
            _ <- cstConsume TokenUpperIdentifier
            pure ()
        TokenLowerIdentifier -> withNode (SK_Node NK_TYPE_VAR) $ do
            _ <- cstConsume TokenLowerIdentifier
            pure ()
        _ -> MP.customFailure $ InvalidTokenForType tok

parseTyVar :: CstParser ()
parseTyVar = withNode (SK_Node NK_TYPE_VAR) $ do
    _ <- cstConsume TokenLowerIdentifier
    pure ()

parseKind :: CstParser ()
parseKind = do
    tok <- cstTryPeekOrEOF
    case Lexer.tokenKind tok of
        TokenVarSymbol | tokenValue tok == "*" -> do
            _ <- cstConsume TokenVarSymbol
            tok' <- cstTryPeekOrEOF
            case Lexer.tokenKind tok' of
                TokenRightArrow -> do
                    _ <- cstConsume TokenRightArrow
                    parseKind
                _ -> pure ()
        _ -> MP.customFailure $ InvalidTokenForType tok

-- Helper functions

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
