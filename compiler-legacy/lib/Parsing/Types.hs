module Parsing.Types where

import Data.List (nubBy)
import Lexing.Lexer (Token (..), TokenKind (..), tokenSpan)
import Lexing.Position (Located (..), Span (..))
import Parsing.Errors (ParsingError (..))
import Parsing.Parser (
    Parser,
    consume,
    optionallySurround,
    parseExhaustiveSequence,
    parseSequence,
    peek,
    tryPeekOrEOF,
    withRecovery,
 )
import Text.Megaparsec (anySingle)
import qualified Text.Megaparsec as MP
import Typing.Types (Constraint (Constraint), Kind (..), QualifiedType (..), TyVar (..), Type (..), arrayType, boolType, constraintTypes, extractTyVars, intType, strType, tupleType)

parseLocatedQualifiedType :: Parser (Located QualifiedType)
parseLocatedQualifiedType = do
    (qtype, span') <- parseQualifiedTypeWithSpan
    pure $ Located span' qtype

parseQualifiedTypeWithSpan :: Parser (QualifiedType, Span)
parseQualifiedTypeWithSpan = do
    (baseType, typeSpan) <- parseTypeWithSpan
    incoming <- tryPeekOrEOF
    if tokenKind incoming == TokenWith
        then do
            _ <- consume TokenWith
            let constraintsParser = parseExhaustiveSequence TokenComma parseConstraint
            constraints <- optionallySurround TokenLeftParen TokenRightParen constraintsParser
            let tyVarsFromType = extractTyVars baseType
            let tyVarsFromConstraints = concatMap (extractTyVarsFromTypes . constraintTypes) constraints
            let allVars = deduplicateTyVars (tyVarsFromType ++ tyVarsFromConstraints)
            pure (Forall allVars constraints baseType, typeSpan)
        else do
            let tyVars = extractTyVars baseType
            pure (Forall tyVars [] baseType, typeSpan)

parseQualifiedType :: Parser QualifiedType
parseQualifiedType = do
    baseType <- parseType
    incoming <- tryPeekOrEOF
    if tokenKind incoming == TokenWith
        then do
            _ <- consume TokenWith
            let constraintsParser = parseExhaustiveSequence TokenComma parseConstraint
            constraints <- optionallySurround TokenLeftParen TokenRightParen constraintsParser
            let tyVarsFromType = extractTyVars baseType
            let tyVarsFromConstraints = concatMap (extractTyVarsFromTypes . constraintTypes) constraints
            let allVars = deduplicateTyVars (tyVarsFromType ++ tyVarsFromConstraints)
            pure $ Forall allVars constraints baseType
        else do
            let tyVars = extractTyVars baseType
            pure $ Forall tyVars [] baseType

parseWithClause :: Parser ([Constraint], [TyVar])
parseWithClause = do
    incoming <- tryPeekOrEOF
    if tokenKind incoming == TokenWith
        then do
            _ <- consume TokenWith
            constraints <- parseExhaustiveSequence TokenComma parseConstraint
            let tyVarsFromConstraints = concatMap (extractTyVarsFromTypes . constraintTypes) constraints
            pure (constraints, tyVarsFromConstraints)
        else pure ([], [])

parseLocatedType :: Parser (Located Type)
parseLocatedType = do
    (ty, span') <- parseTypeWithSpan
    pure $ Located span' ty

parseTypeWithSpan :: Parser (Type, Span)
parseTypeWithSpan = do
    firstTok <- peek
    ty <- parseType
    pure (ty, extractTypeSpan firstTok ty)
  where
    extractTypeSpan :: Token -> Type -> Span
    extractTypeSpan tok _ = tokenSpan tok -- todo: parse type's span

parseType :: Parser Type
parseType = do
    baseType <- parseBaseType
    parseTypeRest baseType

parseTypeRest :: Type -> Parser Type
parseTypeRest baseType = do
    incoming <- tryPeekOrEOF
    case tokenKind incoming of
        TokenRightArrow -> do
            _ <- consume TokenRightArrow
            TArrow baseType <$> parseType
        _ -> do
            appType <- tryParseBaseType
            case appType of
                Nothing -> pure baseType
                Just appType' -> do
                    let appliedType = TApp baseType appType'
                    parseTypeRest appliedType

parseBaseType :: Parser Type
parseBaseType = withRecovery tryParse recover
  where
    tryParse = do
        maybeType <- tryParseBaseType
        case maybeType of
            Just t -> pure t
            Nothing -> do
                nextToken <- peek
                MP.customFailure $ InvalidTokenForType nextToken
    recover = do
        _ <- anySingle
        pure $ TUnresolved "[ERROR]"

tryParseBaseType :: Parser (Maybe Type)
tryParseBaseType = do
    nextToken <- tryPeekOrEOF
    case tokenKind nextToken of
        TokenLeftParen -> do
            _ <- consume TokenLeftParen
            types <- parseSequence TokenComma TokenRightParen parseType
            _ <- consume TokenRightParen
            pure $ Just $ case types of
                [singleType] -> singleType
                _ -> tupleType types
        TokenLeftBracket -> do
            _ <- consume TokenLeftBracket
            innerType <- parseType
            _ <- consume TokenRightBracket
            pure $ Just $ arrayType innerType
        TokenUpperIdentifier -> Just <$> parseTypeConstructor
        TokenLowerIdentifier -> do
            _ <- consume TokenLowerIdentifier
            let name = tokenValue nextToken
            pure $ Just $ TVar (TypeVar name KindStar)
        _ -> pure Nothing

parseAtomicType :: Parser Type
parseAtomicType = do
    base <- parseAtomicBase
    parseApps base
  where
    parseApps t = do
        incoming <- tryPeekOrEOF
        case tokenKind incoming of
            TokenUpperIdentifier -> do
                arg <- parseAtomicBase
                parseApps (TApp t arg)
            TokenLowerIdentifier -> do
                arg <- parseAtomicBase
                parseApps (TApp t arg)
            _ -> pure t

parseAtomicBase :: Parser Type
parseAtomicBase = do
    nextToken <- tryPeekOrEOF
    case tokenKind nextToken of
        TokenUpperIdentifier -> parseTypeConstructor
        TokenLowerIdentifier -> TVar <$> parseTyVar
        _ -> MP.customFailure $ InvalidTokenForType nextToken

parseTyVar :: Parser TyVar
parseTyVar = do
    nameTok <- consume TokenLowerIdentifier
    let name = tokenValue nameTok
    pure $ TypeVar name KindStar

parseTypeConstructor :: Parser Type
parseTypeConstructor = do
    name <- consume TokenUpperIdentifier
    case tokenValue name of
        "Int" -> pure intType
        "String" -> pure strType
        "Bool" -> pure boolType
        other -> pure $ TUnresolved other

parseConstraint :: Parser Constraint
parseConstraint = Constraint <$> parseAtomicType

parseKind :: Parser Kind
parseKind = do
    nextToken <- tryPeekOrEOF
    case tokenKind nextToken of
        TokenVarSymbol | tokenValue nextToken == "*" -> do
            _ <- consume TokenVarSymbol
            incoming <- tryPeekOrEOF
            case tokenKind incoming of
                TokenRightArrow -> do
                    _ <- consume TokenRightArrow
                    KindArrow KindStar <$> parseKind
                _ -> pure KindStar
        _ -> MP.customFailure $ InvalidTokenForType nextToken

deduplicateTyVars :: [TyVar] -> [TyVar]
deduplicateTyVars = nubBy (\a b -> tvId a == tvId b)

extractTyVarsFromTypes :: [Type] -> [TyVar]
extractTyVarsFromTypes = concatMap extractTyVars
