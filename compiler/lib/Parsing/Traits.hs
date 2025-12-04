{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}
module Parsing.Traits where

import Lexing.Lexer (TokenKind (..), spanningTokens)
import Lexing.Position (Located (..))
import Parsing.Bindings (parseBinding)
import Parsing.Errors (ParsingError (..))
import Parsing.Parser (Parser, consume, parseFuncName, parseOptionallyLayout)
import Parsing.Types (parseLocatedQualifiedType, parseQualifiedType)
import Syntax.Tree (Expr (..))
import qualified Text.Megaparsec as MP
import Typing.Types (Constraint (Constraint), QualifiedType (Forall), getUnknownTypeConstructorName)

parseTrait :: Parser Expr
parseTrait = do
    classToken <- consume TokenTrait
    locClassType@(Located _ classType@(Forall _ _ traitType)) <- parseLocatedQualifiedType
    case getUnknownTypeConstructorName classType of
        Nothing -> MP.customFailure $ InvalidTypeForTrait classToken traitType
        Just name -> do
            whereTok <- consume TokenWhere

            bindings <- parseOptionallyLayout (parseTraitBinding locClassType)
            pure
                $ ExprTypeClassDef
                    { typeClassName = name
                    , typeClassType = locClassType
                    , typeClassBindings = bindings
                    , typeClassSpan = spanningTokens classToken whereTok
                    }

parseTraitBinding :: Located QualifiedType -> Parser Expr
parseTraitBinding (Located typeSpan (Forall typeClassTyVars typeClassConstraints typeClassConstraint)) = do
    defToken <- consume TokenDef
    bindName <- parseFuncName
    retTok <- consume TokenReturns
    Located _ (Forall tyVars baseConstraints baseType) <- parseLocatedQualifiedType
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
            , typeClassBindType = Located typeSpan bindTyp
            , typeClassBindDefaultImpl = Nothing
            , typeClassBindSpan = spanningTokens defToken retTok
            }

parseInstance :: Parser Expr
parseInstance = do
    instanceToken <- consume TokenInstance
    instanceType@(Forall _ instanceConstraints _) <- parseQualifiedType

    whereTok <- consume TokenWhere
    bindings <- parseOptionallyLayout (parseBinding False)
    
    let constrainedBindings = map (\b -> b{
        bindingType = case bindingType b of
            Located span' (Forall tyVars constraints baseType) ->
                Located span' (Forall tyVars (instanceConstraints ++ constraints) baseType)
        }) bindings

    pure
        $ ExprInstanceDef
            { instanceConstraint = instanceType
            , instanceMethods = constrainedBindings
            , instanceSpan = spanningTokens instanceToken whereTok
            }
