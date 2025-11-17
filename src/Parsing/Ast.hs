module Parsing.Ast where

import Control.Applicative (Alternative (many, (<|>)))
import Control.Monad (unless)
import Control.Monad.Error.Class (MonadError (throwError))
import Data.List (intercalate)
import Lexing.Lexer (Token (tokenKind, tokenValue), TokenKind (..), spanningTokens, tokenSpan)
import Lexing.Position (Span (Span))
import Parsing.Atoms (parseModuleName)
import Parsing.Bindings (parseBinding)
import Parsing.Errors (ParsingError (UnexpectedToken))
import Parsing.Parser (
    Parser (runParser),
    consume,
    indexedSepBy1Till,
    next,
    optional,
    parseFuncName,
    parseInLayout,
    parseLayout,
    parseSequence,
    peek,
 )
import Parsing.Types (parseKind, parseQualifiedType, parseTyVar, parseType)
import Syntax.Tree (Expr (..))
import Typing.Types (Constraint, QualifiedType (Forall), Type (TVar), mkConstraint)

parse :: [Token] -> Either ParsingError Expr
parse tokens = do
    (root, remaining) <- runParser parser tokens
    case remaining of
        [] -> pure root
        tok : _ -> throwError $ UnexpectedToken tok
  where
    parser = do
        ExprRoot <$> someDeclarations

someDeclarations :: Parser [Expr]
someDeclarations = do
    mtok <- optional peek
    case mtok of
        Nothing -> pure []
        Just _ -> do
            decl <- parseDeclaration
            rest <- someDeclarations
            pure (decl : rest)

parseDeclaration :: Parser Expr
parseDeclaration = do
    token <- peek
    case tokenKind token of
        TokenDef -> parseBinding True
        TokenIntrinsic -> parseIntrinsicDef
        TokenData -> parseDataType
        TokenClass -> parseTypeClass
        TokenInstance -> parseInstance
        TokenImport -> parseImport
        _ -> throwError $ UnexpectedToken token

parseDataType :: Parser Expr
parseDataType = do
    dataToken <- consume TokenData
    nameToken <- consume TokenUpperIdentifier

    tyVars <- many parseTyVar

    let name = tokenValue nameToken
    let spanning = spanningTokens dataToken nameToken
    constructors <- parseInLayout $ indexedSepBy1Till parseStructConstructor (consume TokenPipe) (consume TokenLayoutEnd)
    pure
        $ ExprDataTypeDef
            { dataName = name
            , dataGenerics = tyVars
            , dataConstraints = []
            , dataConstructors = constructors
            , dataSpan = spanning
            }

parseStructConstructor :: Int -> Parser Expr
parseStructConstructor index = do
    firstToken <-
        if index == 0
            then consume TokenEquals
            else consume TokenPipe
    nameToken <- consume TokenUpperIdentifier
    fields <- parseLayout parseStructField
    pure
        $ ExprDataConstructor
            { structConstructorName = tokenValue nameToken
            , structConstructorArgs = fields
            , structConstructorSpan = spanningTokens firstToken nameToken
            }

parseStructField :: Parser (String, Type)
parseStructField = do
    nameToken <- consume TokenLowerIdentifier
    _ <- consume TokenReturns
    typeExpr <- parseType
    pure (tokenValue nameToken, typeExpr)

parseTypeClass :: Parser Expr
parseTypeClass = do
    classToken <- consume TokenClass
    nameToken <- consume TokenUpperIdentifier

    tyVars <- many parseTyVar

    _where <- consume TokenWhere
    let name = tokenValue nameToken
    let typeClassConstraint = mkConstraint name (map TVar tyVars)

    bindings <- parseLayout (parseTypeClassBinding typeClassConstraint)
    pure
        $ ExprTypeClassDef
            { typeClassName = name
            , typeClassGenerics = tyVars
            , typeClassBindings = bindings
            , typeClassSpan = spanningTokens classToken nameToken
            }

parseTypeClassBinding :: Typing.Types.Constraint -> Parser Expr
parseTypeClassBinding typeClassConstraint = do
    defToken <- consume TokenDef
    bindName <- parseFuncName
    retTok <- consume TokenReturns
    Forall tyVars baseConstraints baseType <- parseQualifiedType
    let bindTyp = Forall tyVars (typeClassConstraint : baseConstraints) baseType

    pure
        $ ExprTypeClassBinding
            { typeClassBindName = bindName
            , typeClassBindType = bindTyp
            , typeClassBindDefaultImpl = Nothing
            , typeClassBindSpan = spanningTokens defToken retTok
            }

parseInstance :: Parser Expr
parseInstance = do
    instanceToken <- consume TokenInstance
    constraintType <- parseType

    whereTok <- consume TokenWhere
    bindings <- parseLayout (parseBinding False)
    pure
        $ ExprInstanceDef
            { instanceConstraint = constraintType
            , instanceMethods = bindings
            , instanceSpan = spanningTokens instanceToken whereTok
            }

parseImport :: Parser Expr
parseImport = do
    importToken <- consume TokenImport
    moduleNameSegments <- parseModuleName
    separator <- consume TokenVarSymbol
    unless (tokenValue separator == ".") $ do
        throwError $ UnexpectedToken separator

    _ <- consume TokenLeftBraces
    imports <-
        parseSequence
            TokenComma
            TokenRightBraces
            ( do
                nameToken <- consume TokenUpperIdentifier <|> consume TokenLowerIdentifier <|> consume TokenVarSymbol
                pure $ tokenValue nameToken
            )
    _ <- consume TokenRightBraces

    let moduleName = intercalate "/" moduleNameSegments
    let Span importStart _ = tokenSpan importToken
    let importEnd = importStart + length moduleNameSegments
    pure $ ExprImport moduleName imports (Span importStart importEnd)

parseIntrinsicDef :: Parser Expr
parseIntrinsicDef = do
    intrinsicToken <- consume TokenIntrinsic
    inc <- next
    case tokenKind inc of
        TokenDef -> do
            name <- parseFuncName
            _ <- consume TokenReturns
            typ <- parseQualifiedType
            let spanning = spanningTokens intrinsicToken intrinsicToken
            pure $ ExprIntrinsicDef name typ spanning
        TokenData -> do
            nameToken <- consume TokenUpperIdentifier
            _ <- consume TokenReturns
            kind <- parseKind
            let name = tokenValue nameToken
            let spanning = spanningTokens intrinsicToken nameToken
            pure $ ExprIntrinsicDataTypeDef name kind spanning
        _ -> throwError $ UnexpectedToken inc
