module Parsing.Traits where

import Lexing.Lexer (TokenKind (..), spanningTokens)
import Parsing.Bindings (parseBinding)
import Parsing.Errors (ParsingError (..))
import Parsing.Parser (Parser, consume, parseFuncName, parseOptionallyLayout)
import Parsing.Types (parseQualifiedType, parseType)
import Syntax.Tree (Expr (..))
import qualified Text.Megaparsec as MP
import Typing.Types (Constraint (Constraint), QualifiedType (Forall), getUnknownTypeConstructorName)

parseTrait :: Parser Expr
parseTrait = do
    classToken <- consume TokenTrait
    classType@(Forall _ _ traitType) <- parseQualifiedType
    case getUnknownTypeConstructorName classType of
        Nothing -> MP.customFailure $ InvalidTypeForTrait classToken traitType
        Just name -> do
            whereTok <- consume TokenWhere

            bindings <- parseOptionallyLayout (parseTraitBinding classType)
            pure
                $ ExprTypeClassDef
                    { typeClassName = name
                    , typeClassType = classType
                    , typeClassBindings = bindings
                    , typeClassSpan = spanningTokens classToken whereTok
                    }

parseTraitBinding :: QualifiedType -> Parser Expr
parseTraitBinding (Forall typeClassTyVars typeClassConstraints typeClassConstraint) = do
    defToken <- consume TokenDef
    bindName <- parseFuncName
    retTok <- consume TokenReturns
    Forall tyVars baseConstraints baseType <- parseQualifiedType
    let allTyVars = typeClassTyVars ++ tyVars
    let bindTyp =
            Forall
                allTyVars
                ( Constraint
                    typeClassConstraint
                    : typeClassConstraints
                    ++ baseConstraints
                )
                baseType

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
