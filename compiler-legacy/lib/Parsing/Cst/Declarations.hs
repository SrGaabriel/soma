module Parsing.Cst.Declarations (
    parseDeclaration,
    parseBinding,
    parseDataType,
    parseTrait,
    parseInstance,
    parseIntrinsic,
    parseImport,
) where

import Control.Monad (unless)
import qualified Lexing.Lexer as Lexer
import Parsing.Cst.Atoms (parseExpression, parseModuleName)
import Parsing.Cst.Patterns (parsePipePatternArms)
import Parsing.Cst.Types (parseKind, parseQualifiedType, parseTyVar, parseType)
import Parsing.CstBuilder
import Parsing.Errors (ParsingError (..))
import Syntax.CST.SyntaxKind
import qualified Text.Megaparsec as MP

parseDeclaration :: CstParser ()
parseDeclaration = do
    tok <- cstPeek
    case Lexer.tokenKind tok of
        TokenDef -> parseBinding
        TokenData -> parseDataType
        TokenTrait -> parseTrait
        TokenInstance -> parseInstance
        TokenIntrinsic -> parseIntrinsic
        TokenImport -> parseImport
        _ -> MP.customFailure $ InvalidTokenForTopLevelDeclaration tok

parseBinding :: CstParser ()
parseBinding = withNode (SK_Node NK_BINDING_DEF) $ do
    _ <- cstConsume TokenDef
    parseFuncName
    parseBindingSyntax
    parseBindingBody

parseFuncName :: CstParser ()
parseFuncName = do
    tok <- cstPeek
    case Lexer.tokenKind tok of
        TokenLowerIdentifier -> do
            _ <- cstConsume TokenLowerIdentifier
            pure ()
        TokenLeftBraces -> do
            _ <- cstConsume TokenLeftBraces
            _ <- cstConsume TokenVarSymbol
            _ <- cstConsume TokenRightBraces
            pure ()
        _ -> MP.customFailure $ InvalidFunctionName tok

parseBindingSyntax :: CstParser ()
parseBindingSyntax = do
    tok <- cstPeek
    case Lexer.tokenKind tok of
        TokenLeftParen -> parseImperativeStyle
        _ -> parseTraditionalStyle

parseImperativeStyle :: CstParser ()
parseImperativeStyle = do
    _ <- cstConsume TokenLeftParen
    withNode (SK_Node NK_PARAM_LIST) $ do
        parseCommaSeparatedUntil TokenRightParen parseFuncParam
    _ <- cstConsume TokenRightParen
    tok <- cstPeek
    case Lexer.tokenKind tok of
        TokenRightArrow -> do
            _ <- cstConsume TokenRightArrow
            withNode (SK_Node NK_TYPE) parseType
        TokenReturns -> do
            _ <- cstConsume TokenReturns
            withNode (SK_Node NK_TYPE_SIGNATURE) parseQualifiedType
        _ -> MP.customFailure $ InvalidFunctionSignature tok

parseTraditionalStyle :: CstParser ()
parseTraditionalStyle = do
    _ <- cstConsume TokenReturns
    withNode (SK_Node NK_TYPE_SIGNATURE) parseQualifiedType

parseFuncParam :: CstParser ()
parseFuncParam = withNode (SK_Node NK_PARAM) $ do
    _ <- cstConsume TokenLowerIdentifier
    tok <- cstTryPeek
    case Lexer.tokenKind <$> tok of
        Just TokenColon -> do
            _ <- cstConsume TokenColon
            withNode (SK_Node NK_TYPE) parseType
        _ -> pure ()

parseBindingBody :: CstParser ()
parseBindingBody = do
    tok <- cstPeek
    case Lexer.tokenKind tok of
        TokenEquals -> do
            _ <- cstConsume TokenEquals
            parseOptionallyInLayout parseExpression
        TokenLayoutStart -> parsePipePatternArms
        TokenPipe -> parsePipePatternArms
        _ -> MP.customFailure $ InvalidFunctionBody tok

parseDataType :: CstParser ()
parseDataType = withNode (SK_Node NK_DATA_DEF) $ do
    _ <- cstConsume TokenData
    _ <- cstConsume TokenUpperIdentifier
    parseFluidSequence TokenLayoutStart parseTyVar
    parseLayout parseDataConstructor

parseDataConstructor :: CstParser ()
parseDataConstructor = withNode (SK_Node NK_DATA_CONSTRUCTOR) $ do
    _ <- cstConsume TokenPipe
    _ <- cstConsume TokenUpperIdentifier
    parseOptionallyLayout parseConstructorField

parseConstructorField :: CstParser ()
parseConstructorField = withNode (SK_Node NK_CONSTRUCTOR_FIELD) $ do
    _ <- cstConsume TokenLowerIdentifier
    _ <- cstConsume TokenReturns
    withNode (SK_Node NK_TYPE) parseType

parseTrait :: CstParser ()
parseTrait = withNode (SK_Node NK_TRAIT_DEF) $ do
    _ <- cstConsume TokenTrait
    withNode (SK_Node NK_TYPE_SIGNATURE) parseQualifiedType
    _ <- cstConsume TokenWhere
    parseOptionallyLayout parseTraitMethod

parseTraitMethod :: CstParser ()
parseTraitMethod = withNode (SK_Node NK_TRAIT_METHOD) $ do
    _ <- cstConsume TokenDef
    parseFuncName
    _ <- cstConsume TokenReturns
    withNode (SK_Node NK_TYPE_SIGNATURE) parseQualifiedType

parseInstance :: CstParser ()
parseInstance = withNode (SK_Node NK_INSTANCE_DEF) $ do
    _ <- cstConsume TokenInstance
    withNode (SK_Node NK_TYPE) parseType
    _ <- cstConsume TokenWhere
    parseOptionallyLayout parseInstanceMethod

parseInstanceMethod :: CstParser ()
parseInstanceMethod = withNode (SK_Node NK_INSTANCE_METHOD) $ do
    _ <- cstConsume TokenDef
    parseFuncName
    parseBindingSyntax
    parseBindingBody

parseIntrinsic :: CstParser ()
parseIntrinsic = do
    _ <- cstConsume TokenIntrinsic
    tok <- cstTryPeekOrEOF
    case Lexer.tokenKind tok of
        TokenDef -> parseIntrinsicDef
        TokenData -> parseIntrinsicData
        _ -> MP.customFailure $ InvalidIntrinsic tok

parseIntrinsicDef :: CstParser ()
parseIntrinsicDef = withNode (SK_Node NK_INTRINSIC_DEF) $ do
    _ <- cstConsume TokenDef
    parseFuncName
    _ <- cstConsume TokenReturns
    withNode (SK_Node NK_TYPE_SIGNATURE) parseQualifiedType

parseIntrinsicData :: CstParser ()
parseIntrinsicData = withNode (SK_Node NK_INTRINSIC_DATA) $ do
    _ <- cstConsume TokenData
    _ <- cstConsume TokenUpperIdentifier
    _ <- cstConsume TokenReturns
    parseKind

parseImport :: CstParser ()
parseImport = withNode (SK_Node NK_IMPORT_DECL) $ do
    _ <- cstConsume TokenImport
    _ <- parseModuleName
    _ <- cstConsume TokenVarSymbol -- The dot
    _ <- cstConsume TokenLeftBraces
    withNode (SK_Node NK_IMPORT_LIST) $ do
        parseCommaSeparatedUntil TokenRightBraces parseImportItem
    _ <- cstConsume TokenRightBraces
    pure ()

parseImportItem :: CstParser ()
parseImportItem = do
    _ <- cstConsumeAnyOf [TokenLowerIdentifier, TokenUpperIdentifier, TokenVarSymbol]
    pure ()

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
