module Parsing.Ast where

import Control.Applicative (Alternative (many))
import Control.Monad.Error.Class (MonadError (throwError))
import Data.List (intercalate)
import Lexing.Lexer (Token (tokenIndent, tokenKind, tokenValue), TokenKind (..), spanningTokens, tokenSpan)
import Lexing.Position (Span (Span))
import Parsing.Atoms (parseModuleName)
import Parsing.Bindings (parseBinding)
import Parsing.Errors (ParsingError (UnexpectedToken))
import Parsing.Parser (Parser (runParser), consume, consumeRelevant, next, parseExhaustiveSequence, parseFuncName, parseIndentedBlock, parseIndexedIndentedBlock, peek)
import Parsing.Types (parseQualifiedType, parseTyVar, parseType)
import Syntax.Tree (Expr (..))
import Typing.Types (Constraint (Constraint), QualifiedType (Forall), Type (TVar))

parse :: [Token] -> Either ParsingError Expr
parse tokens = do
    (root, _) <- runParser parser tokens
    pure root
  where
    parser = do
        declarations <- parseExhaustiveSequence TokenNewline parseDeclaration
        pure $ ExprRoot declarations

parseDeclaration :: Parser Expr
parseDeclaration = do
    token <- peek
    case tokenKind token of
        TokenDef -> parseBinding True
        TokenIntrinsic -> parseIntrinsicDef
        TokenNewline -> next >> parseDeclaration
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
    constructors <- parseIndexedIndentedBlock (tokenIndent nameToken) parseStructConstructor
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
    fields <- parseIndentedBlock (tokenIndent nameToken) parseStructField
    pure
        $ ExprDataConstructor
            { structConstructorName = tokenValue nameToken
            , structConstructorArgs = fields
            , structConstructorSpan = spanningTokens firstToken nameToken
            }

parseStructField :: Parser (String, Type)
parseStructField = do
    nameToken <- consume TokenLowerIdentifier
    _ <- consumeRelevant TokenReturns
    typeExpr <- parseType
    pure (tokenValue nameToken, typeExpr)

parseTypeClass :: Parser Expr
parseTypeClass = do
    classToken <- consume TokenClass
    nameToken <- consume TokenUpperIdentifier

    tyVars <- many parseTyVar

    _where <- consume TokenWhere
    let name = tokenValue nameToken
    let typeClassConstraint = Constraint name (map TVar tyVars)

    bindings <- parseIndentedBlock (tokenIndent nameToken) (parseTypeClassBinding typeClassConstraint)
    pure
        $ ExprTypeClassDef
            { typeClassName = name
            , typeClassGenerics = tyVars
            , typeClassBindings = bindings
            , typeClassSpan = spanningTokens classToken nameToken
            }

parseTypeClassBinding :: Constraint -> Parser Expr
parseTypeClassBinding typeClassConstraint = do
    defToken <- consume TokenDef
    bindName <- parseFuncName
    retTok <- consumeRelevant TokenReturns
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
    classNameToken <- consume TokenUpperIdentifier
    dataTypeToken <- consume TokenUpperIdentifier

    _where <- consume TokenWhere
    bindings <- parseIndentedBlock (tokenIndent classNameToken) (parseBinding False)
    let className = tokenValue classNameToken
    pure
        $ ExprInstanceDef
            { instanceClassName = className
            , instanceDataTypeName = tokenValue dataTypeToken
            , instanceMethods = bindings
            , instanceSpan = spanningTokens instanceToken dataTypeToken
            }

parseImport :: Parser Expr
parseImport = do
    importToken <- consume TokenImport
    moduleNameSegments <- parseModuleName
    let moduleName = intercalate "::" moduleNameSegments
    let Span importStart _ = tokenSpan importToken
    let importEnd = importStart + length moduleNameSegments
    pure $ ExprImport moduleName (Span importStart importEnd)

parseIntrinsicDef :: Parser Expr
parseIntrinsicDef = do
    intrinsicToken <- consume TokenIntrinsic
    _ <- consume TokenDef
    name <- parseFuncName
    _ <- consumeRelevant TokenReturns
    typ <- parseQualifiedType
    let spanning = spanningTokens intrinsicToken intrinsicToken
    pure $ ExprIntrinsicDef name typ spanning
