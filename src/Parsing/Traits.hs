module Parsing.Traits where

import Lexing.Lexer (TokenKind (..), spanningTokens, Token (..))
import Parsing.Parser (Parser, consume, parseFuncName, parseOptionallyLayout, parseFluidSequence)
import Parsing.Types (parseQualifiedType, parseTyVar, parseType)
import Syntax.Tree (Expr (..))
import Typing.Types (Constraint, QualifiedType (Forall), mkConstraint, Type (..))
import Parsing.Bindings (parseBinding)

parseTrait :: Parser Expr
parseTrait = do
    classToken <- consume TokenTrait
    nameToken <- consume TokenUpperIdentifier

    tyVars <- parseFluidSequence TokenWhere parseTyVar

    _where <- consume TokenWhere
    let name = tokenValue nameToken
    let typeClassConstraint = mkConstraint name (map TVar tyVars)

    bindings <- parseOptionallyLayout (parseTraitBinding typeClassConstraint)
    pure
        $ ExprTypeClassDef
            { typeClassName = name
            , typeClassGenerics = tyVars
            , typeClassBindings = bindings
            , typeClassSpan = spanningTokens classToken nameToken
            }

parseTraitBinding :: Constraint -> Parser Expr
parseTraitBinding typeClassConstraint = do
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
    bindings <- parseOptionallyLayout (parseBinding False)
    pure
        $ ExprInstanceDef
            { instanceConstraint = constraintType
            , instanceMethods = bindings
            , instanceSpan = spanningTokens instanceToken whereTok
            }