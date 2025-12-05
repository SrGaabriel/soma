module Parsing.Bindings (parseBinding, parseBindingWithAttributes) where

import Control.Monad (unless)
import Lexing.Lexer (Token (..), TokenKind (..), spanningTokens)
import Lexing.Position (Located (..), dummySpan)
import Parsing.Atoms (parseExpression)
import Parsing.Errors (ParsingError (..))
import Parsing.Parser (Parser, ParserContext (..), consume, parseCommaSeparatedUntil, parseFuncName, parseOptionallyInLayout, peek, withinContext)
import Parsing.Patterns (parsePipePatternArms)
import Parsing.Types (parseLocatedQualifiedType, parseType)
import Syntax.Tree (Attribute, Expr (..), exprSpan)
import qualified Text.Megaparsec as MP
import Typing.Currying (curryFunction)
import Typing.Types (QualifiedType (..), Type, extractTyVars)

data FuncParam
    = TypedParam String Type
    | UntypedParam String
    deriving (Show, Eq)

data BindingSyntax
    = ImperativeStyled [FuncParam] Type Token
    | ImperativeUntyped [String] (Located QualifiedType) Token
    | TraditionalStyled (Located QualifiedType) Token
    deriving (Show, Eq)

parseBinding :: Bool -> Parser Expr
parseBinding isTopLevel = parseBindingWithAttributes isTopLevel []

parseBindingWithAttributes :: Bool -> [Located Attribute] -> Parser Expr
parseBindingWithAttributes isTopLevel attrs = withinContext (InFunctionSignature "") $ do
    defToken <- consume TokenDef
    name <- parseFuncName
    syntax <- parseBindingSyntax
    body <- withinContext (InFunctionBody name) $ parseBindingBody name syntax
    let bindType = getBindingType syntax
    let styleToken = getStyleToken syntax
    pure
        $ ExprBindingDef
            { bindingName = name
            , bindingType = bindType
            , bindingBody = wrapWithLambda syntax body
            , bindingIsImpl = isTopLevel
            , bindingAttributes = attrs
            , bindingSpan = spanningTokens defToken styleToken
            }

parseBindingSyntax :: Parser BindingSyntax
parseBindingSyntax = do
    nextTok <- peek
    let hasParens = tokenKind nextTok == TokenLeftParen

    if hasParens
        then parseImperativeStyle
        else parseTraditionalStyle

parseImperativeStyle :: Parser BindingSyntax
parseImperativeStyle = do
    _ <- consume TokenLeftParen
    params <- parseCommaSeparatedUntil TokenRightParen parseFuncParam
    _ <- consume TokenRightParen

    nextTok <- peek
    case tokenKind nextTok of
        TokenRightArrow -> do
            _ <- consume TokenRightArrow
            unless (all isTyped params)
                $ MP.customFailure
                $ MixedParameterStyles nextTok
            returnType <- parseType
            let types = map extractType params
            return $ ImperativeStyled params (curryFunction types returnType) nextTok
        TokenReturns -> do
            _ <- consume TokenReturns
            unless (all isUntyped params)
                $ MP.customFailure
                $ MixedParameterStyles nextTok
            let names = map extractName params
            paramType <- parseLocatedQualifiedType
            return $ ImperativeUntyped names paramType nextTok
        _ -> MP.customFailure $ InvalidFunctionSignature nextTok

parseTraditionalStyle :: Parser BindingSyntax
parseTraditionalStyle = do
    returns <- consume TokenReturns
    qty <- parseLocatedQualifiedType
    return $ TraditionalStyled qty returns

parseFuncParam :: Parser FuncParam
parseFuncParam = do
    nameToken <- consume TokenLowerIdentifier
    let name = tokenValue nameToken

    inc <- peek
    if tokenKind inc == TokenColon
        then do
            _ <- consume TokenColon
            TypedParam name <$> parseType
        else return $ UntypedParam name

parseBindingBody :: String -> BindingSyntax -> Parser Expr
parseBindingBody funcName syntax = do
    case syntax of
        TraditionalStyled{} -> parseTraditionalBody funcName
        ImperativeStyled{} -> parseSimpleBody
        ImperativeUntyped{} -> parseSimpleBody

parseTraditionalBody :: String -> Parser Expr
parseTraditionalBody funcName = do
    nextTok <- peek
    case tokenKind nextTok of
        TokenEquals -> parseSimpleBody
        TokenLayoutStart -> withinContext (InPatternMatch funcName) $ do
            ExprDerivedPatternMatch <$> parsePipePatternArms
        TokenCompose -> MP.customFailure $ MissingEqualsBeforeExpression nextTok funcName
        _ -> MP.customFailure $ InvalidFunctionBody nextTok

parseSimpleBody :: Parser Expr
parseSimpleBody = do
    _ <- consume TokenEquals
    parseOptionallyInLayout parseExpression

getBindingType :: BindingSyntax -> Located QualifiedType
getBindingType syntax = case syntax of
    ImperativeStyled _ funcType _ -> do
        let tyVars = extractTyVars funcType
        Located dummySpan (Forall tyVars [] funcType)
    ImperativeUntyped _ qty _ -> qty
    TraditionalStyled qty _ -> qty

wrapWithLambda :: BindingSyntax -> Expr -> Expr
wrapWithLambda syntax body = case syntax of
    ImperativeStyled params _ _ ->
        let names = map extractName params
        in ExprLambda names body (exprSpan body)
    ImperativeUntyped names _ _ ->
        ExprLambda names body (exprSpan body)
    TraditionalStyled _ _ -> body

-- Helper functions
isTyped :: FuncParam -> Bool
isTyped (TypedParam _ _) = True
isTyped _ = False

isUntyped :: FuncParam -> Bool
isUntyped = not . isTyped

extractName :: FuncParam -> String
extractName (TypedParam name _) = name
extractName (UntypedParam name) = name

extractType :: FuncParam -> Type
extractType (TypedParam _ typ) = typ
extractType (UntypedParam _) = error "extractType called on untyped parameter"

getStyleToken :: BindingSyntax -> Token
getStyleToken (ImperativeStyled _ _ tok) = tok
getStyleToken (ImperativeUntyped _ _ tok) = tok
getStyleToken (TraditionalStyled _ tok) = tok
