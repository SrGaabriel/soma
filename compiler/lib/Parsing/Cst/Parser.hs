module Parsing.Cst.Parser (
    parseCst,
    module Parsing.CstBuilder,
) where

import Control.Monad (void, when)
import Data.Maybe (fromMaybe)
import Lexing.Lexer (Token (..))
import qualified Lexing.Lexer as Lexer
import Parsing.Cst.Helpers
import Parsing.CstBuilder
import Parsing.Errors (ParsingError (..))
import Parsing.Parser (TokenStream (..))
import Syntax.CST.GreenTree (GreenNode)
import Syntax.CST.SyntaxKind
import qualified Text.Megaparsec as MP

parseCst :: [Token] -> Either (MP.ParseErrorBundle TokenStream ParsingError) GreenNode
parseCst tokens = case runCstParser parseSourceFile tokens of
    Left err -> Left err
    Right ((), tree) -> Right tree

parseSourceFile :: CstParser ()
parseSourceFile = do
    skipLayoutSeparators
    parseDeclarations
  where
    parseDeclarations = do
        atEnd <- cstIsEOF
        if atEnd
            then pure ()
            else do
                parseDeclaration
                skipLayoutSeparators
                parseDeclarations

    skipLayoutSeparators = do
        tok <- cstTryPeek
        case Lexer.tokenKind <$> tok of
            Just TokenLayoutSeparator -> do
                _ <- cstConsume TokenLayoutSeparator
                skipLayoutSeparators
            _ -> pure ()

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
        TokenLowerIdentifier -> void $ cstConsume TokenLowerIdentifier
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
    withNode (SK_Node NK_QUALIFIED_NAME) $ do
        _ <- cstConsumeAnyOf [TokenVarSymbol, TokenLowerIdentifier]
        _ <- MP.many $ do
            tok <- cstTryPeekOrEOF
            if Lexer.tokenKind tok == TokenSlash
                then do
                    _ <- cstConsume TokenSlash
                    _ <- cstConsumeAnyOf [TokenVarSymbol, TokenLowerIdentifier]
                    pure ()
                else MP.empty
        pure ()
    _ <- cstConsume TokenVarSymbol -- The dot
    _ <- cstConsume TokenLeftBraces
    withNode (SK_Node NK_IMPORT_LIST) $ do
        parseCommaSeparatedUntil TokenRightBraces $ do
            _ <- cstConsumeAnyOf [TokenLowerIdentifier, TokenUpperIdentifier, TokenVarSymbol]
            pure ()
    _ <- cstConsume TokenRightBraces
    pure ()

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
            _ <- cstConsume TokenRightParen
            pure ()
        _ -> parseExhaustiveSequence TokenComma parseConstraint

parseConstraint :: CstParser ()
parseConstraint = withNode (SK_Node NK_CONSTRAINT) parseAtomicType

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
                            _ <- MP.many $ do
                                _ <- cstConsume TokenComma
                                _ <- parseType
                                pure ()
                            _ <- cstConsume TokenRightParen
                            pure (Just ())
                        _ -> withNode (SK_Node NK_TYPE_PARENS) $ do
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

parseAtomicType :: CstParser ()
parseAtomicType = do
    parseAtomicBase
    parseApps
  where
    parseApps = do
        tok <- cstTryPeekOrEOF
        case Lexer.tokenKind tok of
            TokenUpperIdentifier -> parseAtomicBase >> parseApps
            TokenLowerIdentifier -> parseAtomicBase >> parseApps
            _ -> pure ()

parseAtomicBase :: CstParser ()
parseAtomicBase = do
    tok <- cstTryPeekOrEOF
    case Lexer.tokenKind tok of
        TokenUpperIdentifier -> withNode (SK_Node NK_TYPE_CONSTRUCTOR) $ void $ cstConsume TokenUpperIdentifier
        TokenLowerIdentifier -> withNode (SK_Node NK_TYPE_VAR) $ void $ cstConsume TokenLowerIdentifier
        _ -> MP.customFailure $ InvalidTokenForType tok

parseTyVar :: CstParser ()
parseTyVar = withNode (SK_Node NK_TYPE_VAR) $ void $ cstConsume TokenLowerIdentifier

parseKind :: CstParser ()
parseKind = do
    tok <- cstTryPeekOrEOF
    case Lexer.tokenKind tok of
        TokenVarSymbol | tokenValue tok == "*" -> do
            _ <- cstConsume TokenVarSymbol
            tok' <- cstTryPeekOrEOF
            when (Lexer.tokenKind tok' == TokenRightArrow) $ do
                _ <- cstConsume TokenRightArrow
                parseKind
        _ -> MP.customFailure $ InvalidTokenForType tok

parseExpression :: CstParser ()
parseExpression = parseExprPrec 0

parseExprPrec :: Int -> CstParser ()
parseExprPrec prec = do
    parseApplication
    parseInfixRest prec

parseApplication :: CstParser ()
parseApplication = withNode (SK_Node NK_EXPR_APP) $ do
    _ <- parseAtom
    _ <- MP.many parseAtom
    pure ()

parseAtom :: CstParser ()
parseAtom = do
    tok <- cstTryPeek
    case Lexer.tokenKind <$> tok of
        Just TokenNumber -> withNode (SK_Node NK_EXPR_LITERAL) $ void $ cstConsume TokenNumber
        Just TokenLeftParen -> parseParenExpr
        Just TokenLeftBracket -> parseArrayExpr
        Just TokenLowerIdentifier -> withNode (SK_Node NK_EXPR_VAR) $ void $ cstConsume TokenLowerIdentifier
        Just TokenUpperIdentifier -> withNode (SK_Node NK_EXPR_CONSTRUCTOR) $ void $ cstConsume TokenUpperIdentifier
        Just (TokenString _) -> withNode (SK_Node NK_EXPR_LITERAL) $ void $ cstSatisfy isStringToken
        Just TokenLet -> parseLetExpression
        Just TokenDollar -> cstConsume TokenDollar >> parseExpression
        Just TokenTrue -> withNode (SK_Node NK_EXPR_LITERAL) $ void $ cstConsume TokenTrue
        Just TokenFalse -> withNode (SK_Node NK_EXPR_LITERAL) $ void $ cstConsume TokenFalse
        Just TokenCompose -> parseCompose
        Just TokenIf -> parseIf
        _ -> MP.empty
  where
    isStringToken t = case Lexer.tokenKind t of TokenString _ -> True; _ -> False

parseParenExpr :: CstParser ()
parseParenExpr = do
    _ <- cstConsume TokenLeftParen
    tok <- cstPeek
    case Lexer.tokenKind tok of
        TokenLambda -> withNode (SK_Node NK_EXPR_LAMBDA) $ do
            _ <- cstConsume TokenLambda
            withNode (SK_Node NK_PARAM_LIST) $ parseFluidSequence TokenRightArrow $ void $ cstConsume TokenLowerIdentifier
            _ <- cstConsume TokenRightArrow
            parseExpression
            void $ cstConsume TokenRightParen
        TokenRightParen -> withNode (SK_Node NK_EXPR_TUPLE) $ void $ cstConsume TokenRightParen
        _ -> do
            parseExpression
            tok' <- cstTryPeek
            case Lexer.tokenKind <$> tok' of
                Just TokenComma -> withNode (SK_Node NK_EXPR_TUPLE) $ do
                    _ <- MP.many $ do
                        _ <- cstConsume TokenComma
                        _ <- parseExpression
                        pure ()
                    _ <- cstConsume TokenRightParen
                    pure ()
                _ -> withNode (SK_Node NK_EXPR_PARENS) $ void $ cstConsume TokenRightParen

parseArrayExpr :: CstParser ()
parseArrayExpr = withNode (SK_Node NK_EXPR_LIST) $ do
    _ <- cstConsume TokenLeftBracket
    parseCommaSeparatedUntil TokenRightBracket parseExpression
    void $ cstConsume TokenRightBracket

parseLetExpression :: CstParser ()
parseLetExpression = withNode (SK_Node NK_EXPR_LET) $ do
    _ <- cstConsume TokenLet
    _ <- cstConsume TokenLowerIdentifier
    _ <- cstConsume TokenEquals
    parseExpression
    _ <- cstConsume TokenIn
    _ <- MP.optional (cstConsume TokenLayoutSeparator)
    parseExpression

parseInfixRest :: Int -> CstParser ()
parseInfixRest prec = do
    mtok <- cstTryPeek
    case mtok of
        Just tok
            | TokenVarSymbol <- Lexer.tokenKind tok
            , let opStr = tokenValue tok -> do
                let (opPrec, assoc) = fromMaybe (0, LeftAssoc) (getOpPrecedence opStr)
                when (shouldContinue prec opPrec assoc) $ do
                    _ <- cstConsume TokenVarSymbol
                    _ <- parseExprPrec (nextPrec assoc opPrec)
                    parseInfixRest prec
        _ -> pure ()
  where
    shouldContinue current nextOpPrec assoc =
        case assoc of
            LeftAssoc -> nextOpPrec >= current
            RightAssoc -> nextOpPrec > current
    nextPrec assoc opPrec =
        case assoc of
            LeftAssoc -> opPrec + 1
            RightAssoc -> opPrec

data Associativity = LeftAssoc | RightAssoc

operatorPrecedenceTable :: [[String]]
operatorPrecedenceTable =
    [ ["*", "/"]
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

parseCompose :: CstParser ()
parseCompose = withNode (SK_Node NK_EXPR_COMPOSE) $ do
    _ <- cstConsume TokenCompose
    parseLayout parseComposeStmt

parseComposeStmt :: CstParser ()
parseComposeStmt = do
    tok <- cstTryPeek
    case Lexer.tokenKind <$> tok of
        Just TokenBind -> withNode (SK_Node NK_COMPOSE_BIND) $ do
            _ <- cstConsume TokenBind
            _ <- cstConsume TokenLowerIdentifier
            _ <- cstConsume TokenLeftArrow
            parseExpression
        Just TokenLet -> withNode (SK_Node NK_COMPOSE_LET) $ do
            _ <- cstConsume TokenLet
            _ <- cstConsume TokenLowerIdentifier
            _ <- cstConsume TokenEquals
            parseExpression
        _ -> withNode (SK_Node NK_COMPOSE_STMT) parseExpression

parseIf :: CstParser ()
parseIf = withNode (SK_Node NK_EXPR_IF) $ do
    _ <- cstConsume TokenIf
    parseExpression
    _ <- cstConsume TokenThen
    parseExpression
    _ <- cstConsume TokenElse
    parseExpression

parsePipePatternArms :: CstParser ()
parsePipePatternArms = parseLayout parsePipePatternArm

parsePipePatternArm :: CstParser ()
parsePipePatternArm = withNode (SK_Node NK_MATCH_ARM) $ do
    _ <- cstConsume TokenPipe
    parseMultiplePatterns
    _ <- cstConsume TokenStrongRightArrow
    parseExpression

parseMultiplePatterns :: CstParser ()
parseMultiplePatterns = do
    _ <- parseSinglePattern False
    _ <- MP.many $ do
        tok <- cstTryPeekOrEOF
        if Lexer.tokenKind tok == TokenStrongRightArrow
            then MP.empty
            else do
                _ <- parseSinglePattern False
                pure ()
    pure ()

parseSinglePattern :: Bool -> CstParser ()
parseSinglePattern parenthesizedConstructors = do
    tok <- cstPeek
    case Lexer.tokenKind tok of
        TokenLowerIdentifier -> withNode (SK_Node NK_PATTERN_VAR) $ void $ cstConsume TokenLowerIdentifier
        TokenNumber -> withNode (SK_Node NK_PATTERN_LITERAL) $ void $ cstConsume TokenNumber
        TokenLeftParen -> do
            _ <- cstConsume TokenLeftParen
            parseSinglePattern True
            void $ cstConsume TokenRightParen
        TokenUnderscore -> withNode (SK_Node NK_PATTERN_WILDCARD) $ void $ cstConsume TokenUnderscore
        TokenUpperIdentifier
            | parenthesizedConstructors -> withNode (SK_Node NK_PATTERN_CONSTRUCTOR) $ do
                _ <- cstConsume TokenUpperIdentifier
                parseFluidSequence TokenRightParen (parseSinglePattern False)
        TokenUpperIdentifier
            | not parenthesizedConstructors ->
                MP.customFailure $ PatternNeedsParentheses tok (tokenValue tok)
        _ -> MP.customFailure $ InvalidPattern tok
