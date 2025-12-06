{-# LANGUAGE OverloadedStrings #-}

module Syntax.CST.Lower (
    lowerSourceFile,
    lowerExpr,
    lowerPattern,
    lowerType,
    LowerError (..),
) where

import Data.Maybe (mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Lexing.Position (Located (..), Span (..))
import Syntax.CST.GreenTree hiding (node, token)
import Syntax.CST.RedTree hiding (tokens)
import Syntax.CST.SyntaxKind
import Syntax.Patterns (Literal (..), Pattern (..))
import Syntax.Tree (ComposeStmt (..), Expr (..))
import Typing.Types (Constraint (..), Kind (..), QualifiedType (..), TyConstructor (..), TyVar (..), Type (..), tupleType)

data LowerError
    = UnexpectedNodeKind !SyntaxKind !Text
    | MissingChild !NodeKind !Text
    | InvalidLiteral !Text
    deriving (Eq, Show)

toSpan :: SyntaxNode -> Span
toSpan node =
    let start = fromIntegral (snOffset node)
        len = fromIntegral (ndTextLen (unGreenNode (snGreen node)))
    in Span start (start + len)

tokenSpan :: SyntaxToken -> Span
tokenSpan tok =
    let start = fromIntegral (stOffset tok)
        len = T.length (gtText (stGreen tok))
    in Span start (start + len)

lowerSourceFile :: SyntaxNode -> Either [LowerError] Expr
lowerSourceFile root = do
    let decls = mapMaybe lowerDeclaration (children root)
    Right $ ExprRoot decls

lowerDeclaration :: SyntaxNode -> Maybe Expr
lowerDeclaration node = case ndKind (unGreenNode (snGreen node)) of
    SK_Node NK_BINDING_DEF -> lowerBinding node
    SK_Node NK_DATA_DEF -> lowerDataDef node
    SK_Node NK_TRAIT_DEF -> lowerTrait node
    SK_Node NK_INSTANCE_DEF -> lowerInstance node
    SK_Node NK_INTRINSIC_DEF -> lowerIntrinsic node
    SK_Node NK_INTRINSIC_DATA -> lowerIntrinsicData node
    SK_Node NK_IMPORT_DECL -> lowerImport node
    _ -> Nothing

lowerBinding :: SyntaxNode -> Maybe Expr
lowerBinding = lowerBindingWithImpl True

lowerBindingWithImpl :: Bool -> SyntaxNode -> Maybe Expr
lowerBindingWithImpl isImpl node = do
    nameTok <- findNameToken node
    let name = T.unpack $ gtText (stGreen nameTok)

    let mTypeSig = childOfKind (SK_Node NK_TYPE_SIGNATURE) node
    qualType <- lowerTypeSig =<< mTypeSig

    let bodyExprs = childrenOfKind (SK_Node NK_MATCH_ARM) node
    body <-
        if null bodyExprs
            then do
                exprNode <- findExprChild node
                lowerExpr exprNode
            else do
                arms <- mapM lowerMatchArm bodyExprs
                Just $ ExprDerivedPatternMatch arms

    Just
        $ ExprBindingDef
            { bindingName = name
            , bindingType = Located (toSpan node) qualType
            , bindingBody = body
            , bindingIsImpl = isImpl
            , bindingAttributes = []
            , bindingSpan = toSpan node
            }

lowerDataDef :: SyntaxNode -> Maybe Expr
lowerDataDef node = do
    nameTok <- findNameToken node
    let name = T.unpack $ gtText (stGreen nameTok)

    let generics = extractTypeVars node

    let constraints = extractConstraints node

    let constructorNodes = childrenOfKind (SK_Node NK_DATA_CONSTRUCTOR) node
    constructors <- mapM lowerDataConstructor constructorNodes

    Just
        $ ExprDataTypeDef
            { dataName = name
            , dataGenerics = generics
            , dataConstraints = constraints
            , dataConstructors = constructors
            , dataAttributes = []
            , dataSpan = toSpan node
            }

lowerDataConstructor :: SyntaxNode -> Maybe Expr
lowerDataConstructor node = do
    nameTok <- findNameToken node
    let name = T.unpack $ gtText (stGreen nameTok)

    let fieldNodes = childrenOfKind (SK_Node NK_CONSTRUCTOR_FIELD) node
    fields <- mapM lowerField fieldNodes

    Just
        $ ExprDataConstructor
            { structConstructorName = name
            , structConstructorArgs = fields
            , structConstructorSpan = toSpan node
            }

lowerField :: SyntaxNode -> Maybe (String, Located Type)
lowerField node = do
    nameTok <- findNameToken node
    let name = T.unpack $ gtText (stGreen nameTok)

    typeNode <- childOfKind (SK_Node NK_TYPE) node
    ty <- lowerType typeNode

    Just (name, Located (toSpan typeNode) ty)

lowerTrait :: SyntaxNode -> Maybe Expr
lowerTrait node = do
    nameTok <- findNameToken node
    let name = T.unpack $ gtText (stGreen nameTok)

    let mTypeSig = childOfKind (SK_Node NK_TYPE_SIGNATURE) node
    qualType <- lowerTypeSig =<< mTypeSig

    let methodNodes = childrenOfKind (SK_Node NK_TRAIT_METHOD) node
    methods <- mapM lowerTraitMethod methodNodes

    Just
        $ ExprTypeClassDef
            { typeClassName = name
            , typeClassType = Located (toSpan node) qualType
            , typeClassBindings = methods
            , typeClassSpan = toSpan node
            }

lowerTraitMethod :: SyntaxNode -> Maybe Expr
lowerTraitMethod node = do
    nameTok <- findNameToken node
    let name = T.unpack $ gtText (stGreen nameTok)

    let mTypeSig = childOfKind (SK_Node NK_TYPE_SIGNATURE) node
    qualType <- lowerTypeSig =<< mTypeSig

    let mDefaultImpl = Nothing
    Just
        $ ExprTypeClassBinding
            { typeClassBindName = name
            , typeClassBindType = Located (toSpan node) qualType
            , typeClassBindDefaultImpl = mDefaultImpl
            , typeClassBindSpan = toSpan node
            }

lowerInstance :: SyntaxNode -> Maybe Expr
lowerInstance node = do
    constraintTy <- lowerInstanceConstraint node

    let methodNodes = childrenOfKind (SK_Node NK_INSTANCE_METHOD) node
    methods <- mapM lowerInstanceMethod methodNodes

    Just
        $ ExprInstanceDef
            { instanceConstraint = constraintTy
            , instanceMethods = methods
            , instanceSpan = toSpan node
            }

lowerInstanceConstraint :: SyntaxNode -> Maybe QualifiedType
lowerInstanceConstraint node = do
    typeNode <- childOfKind (SK_Node NK_TYPE_SIGNATURE) node
    lowerTypeSig typeNode

lowerInstanceMethod :: SyntaxNode -> Maybe Expr
lowerInstanceMethod = lowerBindingWithImpl False

lowerIntrinsic :: SyntaxNode -> Maybe Expr
lowerIntrinsic node = do
    nameTok <- findNameToken node
    let name = T.unpack $ gtText (stGreen nameTok)

    let mTypeSig = childOfKind (SK_Node NK_TYPE_SIGNATURE) node
    qualType <- lowerTypeSig =<< mTypeSig
    Just
        $ ExprIntrinsicDef
            { intrinsicName = name
            , intrinsicType = Located (toSpan node) qualType
            , intrinsicSpan = toSpan node
            }

lowerIntrinsicData :: SyntaxNode -> Maybe Expr
lowerIntrinsicData node = do
    nameTok <- findNameToken node
    let name = T.unpack $ gtText (stGreen nameTok)

    let kind = parseKindFromTokens node
    Just
        $ ExprIntrinsicDataTypeDef
            { intrinsicDataTypeName = name
            , intrinsicDataTypeKind = kind
            , intrinsicDataTypeSpan = toSpan node
            }

parseKindFromTokens :: SyntaxNode -> Kind
parseKindFromTokens node =
    let tokens = collectKindTokens node
    in parseKindTokenList tokens
  where
    collectKindTokens n =
        let allTokens = allTokensInNode n
            afterArrow = dropWhile (not . isReturnsToken) allTokens
        in case afterArrow of
            (_ : rest) -> rest
            [] -> []

    isReturnsToken tok = gtKind (stGreen tok) == SK_Token TokenReturns

    parseKindTokenList [] = KindStar
    parseKindTokenList (tok : rest)
        | gtKind (stGreen tok) == SK_Token TokenVarSymbol
        , gtText (stGreen tok) == "*" =
            case rest of
                (arrTok : rest')
                    | gtKind (stGreen arrTok) == SK_Token TokenRightArrow ->
                        KindArrow KindStar (parseKindTokenList rest')
                _ -> KindStar
        | otherwise = KindStar

allTokensInNode :: SyntaxNode -> [SyntaxToken]
allTokensInNode node = concatMap getToken (childrenWithTokens node)
  where
    getToken (SyntaxTokenElement tok) = [tok]
    getToken (SyntaxNodeElement n) = allTokensInNode n

lowerImport :: SyntaxNode -> Maybe Expr
lowerImport node = do
    let moduleNameParts = extractModuleName node
    let moduleName = T.unpack $ T.intercalate "/" moduleNameParts

    let importList = case childOfKind (SK_Node NK_IMPORT_LIST) node of
            Just list -> mapMaybe extractImportItem (children list)
            Nothing -> []
    Just $ ExprImport moduleName importList (toSpan node)

extractModuleName :: SyntaxNode -> [Text]
extractModuleName node =
    case childOfKind (SK_Node NK_QUALIFIED_NAME) node of
        Just qname -> mapMaybe getIdentText (childrenWithTokens qname)
        Nothing -> mapMaybe getIdentText (childrenWithTokens node)
  where
    getIdentText (SyntaxTokenElement tok)
        | gtKind (stGreen tok) == SK_Token TokenLowerIdentifier = Just (gtText (stGreen tok))
        | gtKind (stGreen tok) == SK_Token TokenUpperIdentifier = Just (gtText (stGreen tok))
    getIdentText _ = Nothing

extractImportItem :: SyntaxNode -> Maybe String
extractImportItem node = do
    tok <- firstToken node
    Just $ T.unpack $ gtText (stGreen tok)

lowerTypeSig :: SyntaxNode -> Maybe QualifiedType
lowerTypeSig node = do
    let constraints = extractConstraints node

    let forallVars = extractForallVars node

    typeNode <- childOfKind (SK_Node NK_TYPE) node
    ty <- lowerType typeNode

    Just $ Forall forallVars constraints ty

lowerType :: SyntaxNode -> Maybe Type
lowerType node = case ndKind (unGreenNode (snGreen node)) of
    SK_Node NK_TYPE_VAR -> do
        tok <- firstToken node
        let name = T.unpack $ gtText (stGreen tok)
        Just $ TVar (TypeVar name KindStar)
    SK_Node NK_TYPE_CONSTRUCTOR -> do
        tok <- firstToken node
        let name = T.unpack $ gtText (stGreen tok)
        Just $ TConstructor (TypeConstructor name KindStar)
    SK_Node NK_TYPE_APP -> do
        let typeChildren = children node
        case typeChildren of
            (f : args) -> do
                fTy <- lowerType f
                argTys <- mapM lowerType args
                Just $ foldl TApp fTy argTys
            [] -> Nothing
    SK_Node NK_TYPE_ARROW -> do
        let typeChildren = children node
        case typeChildren of
            [from, to] -> do
                fromTy <- lowerType from
                toTy <- lowerType to
                Just $ TArrow fromTy toTy
            _ -> Nothing
    SK_Node NK_TYPE_TUPLE -> do
        let typeChildren = children node
        tys <- mapM lowerType typeChildren
        Just $ tupleType tys
    SK_Node NK_TYPE_LIST -> do
        let typeChildren = children node
        case typeChildren of
            [elemType] -> do
                elemTy <- lowerType elemType
                Just $ TApp (TConstructor (TypeConstructor "[]" (KindArrow KindStar KindStar))) elemTy
            _ -> Nothing
    SK_Node NK_TYPE_PARENS -> do
        inner <- firstChild node
        lowerType inner
    SK_Node NK_TYPE -> do
        inner <- firstChild node
        lowerType inner
    _ -> Nothing

lowerExpr :: SyntaxNode -> Maybe Expr
lowerExpr node = case ndKind (unGreenNode (snGreen node)) of
    SK_Node NK_EXPR_VAR -> do
        tok <- firstToken node
        let name = T.unpack $ gtText (stGreen tok)
        Just $ ExprUVar name (toSpan node)
    SK_Node NK_EXPR_CONSTRUCTOR -> do
        tok <- firstToken node
        let name = T.unpack $ gtText (stGreen tok)
        Just $ ExprUVar name (toSpan node)
    SK_Node NK_EXPR_LITERAL -> do
        tok <- firstToken node
        lowerLiteral tok
    SK_Node NK_EXPR_APP -> do
        let exprChildren = children node
        case exprChildren of
            (f : args) -> do
                fExpr <- lowerExpr f
                argExprs <- mapM lowerExpr args
                Just $ foldl ExprApp fExpr argExprs
            [] -> Nothing
    SK_Node NK_EXPR_LAMBDA -> do
        let params = extractLambdaParams node

        bodyNode <- findExprChild node
        body <- lowerExpr bodyNode

        Just $ ExprLambda params body (toSpan node)
    SK_Node NK_EXPR_LET -> do
        nameTok <- findNameToken node
        let name = T.unpack $ gtText (stGreen nameTok)

        let exprChildren = filter isExprNode (children node)
        case exprChildren of
            [valueNode, bodyNode] -> do
                value <- lowerExpr valueNode
                body <- lowerExpr bodyNode
                Just $ ExprLet name value body (toSpan node)
            _ -> Nothing
    SK_Node NK_EXPR_IF -> do
        let exprChildren = filter isExprNode (children node)
        case exprChildren of
            [cond, thenBranch, elseBranch] -> do
                condExpr <- lowerExpr cond
                thenExpr <- lowerExpr thenBranch
                elseExpr <- lowerExpr elseBranch
                Just $ ExprIf condExpr thenExpr elseExpr (toSpan node)
            _ -> Nothing
    SK_Node NK_EXPR_MATCH -> do
        scrutineeNode <- firstChild node
        scrutinee <- lowerExpr scrutineeNode

        let armNodes = childrenOfKind (SK_Node NK_MATCH_ARM) node
        arms <- mapM lowerMatchArm armNodes

        Just $ ExprPatternMatch scrutinee arms (toSpan node)
    SK_Node NK_EXPR_TUPLE -> do
        let exprChildren = filter isExprNode (children node)
        exprs <- mapM lowerExpr exprChildren
        Just $ ExprTuple exprs (toSpan node)
    SK_Node NK_EXPR_LIST -> do
        let exprChildren = filter isExprNode (children node)
        exprs <- mapM lowerExpr exprChildren
        Just $ ExprArray exprs (toSpan node)
    SK_Node NK_EXPR_PARENS -> do
        inner <- firstChild node
        lowerExpr inner
    SK_Node NK_EXPR_BLOCK -> do
        let exprChildren = filter isExprNode (children node)
        exprs <- mapM lowerExpr exprChildren
        Just $ ExprBlock exprs (toSpan node)
    SK_Node NK_EXPR_COMPOSE -> do
        let stmtNodes =
                childrenOfKind (SK_Node NK_COMPOSE_STMT) node
                    ++ childrenOfKind (SK_Node NK_COMPOSE_BIND) node
                    ++ childrenOfKind (SK_Node NK_COMPOSE_LET) node
        stmts <- mapM lowerComposeStmt stmtNodes
        Just $ ExprCompose stmts (toSpan node)
    SK_Node NK_EXPR -> do
        inner <- firstChild node
        lowerExpr inner
    _ -> Nothing

isExprNode :: SyntaxNode -> Bool
isExprNode node = case ndKind (unGreenNode (snGreen node)) of
    SK_Node nk -> nk `elem` exprKinds
    _ -> False
  where
    exprKinds =
        [ NK_EXPR
        , NK_EXPR_VAR
        , NK_EXPR_CONSTRUCTOR
        , NK_EXPR_LITERAL
        , NK_EXPR_APP
        , NK_EXPR_LAMBDA
        , NK_EXPR_LET
        , NK_EXPR_IF
        , NK_EXPR_MATCH
        , NK_EXPR_TUPLE
        , NK_EXPR_LIST
        , NK_EXPR_PARENS
        , NK_EXPR_BLOCK
        , NK_EXPR_COMPOSE
        ]

lowerLiteral :: SyntaxToken -> Maybe Expr
lowerLiteral tok = case gtKind (stGreen tok) of
    SK_Token TokenNumber ->
        Just $ ExprNum (T.unpack $ gtText (stGreen tok)) (tokenSpan tok)
    SK_Token (TokenString _) ->
        Just $ ExprStr (T.unpack $ gtText (stGreen tok)) (tokenSpan tok)
    SK_Token TokenTrue ->
        Just $ ExprBool True (tokenSpan tok)
    SK_Token TokenFalse ->
        Just $ ExprBool False (tokenSpan tok)
    _ -> Nothing

lowerMatchArm :: SyntaxNode -> Maybe Expr
lowerMatchArm node = do
    let patternNodes =
            childrenOfKind (SK_Node NK_PATTERN) node
                ++ childrenOfKind (SK_Node NK_PATTERN_VAR) node
                ++ childrenOfKind (SK_Node NK_PATTERN_CONSTRUCTOR) node
    patterns <- mapM lowerPattern patternNodes

    bodyNode <- findExprChild node
    body <- lowerExpr bodyNode

    Just $ ExprPatternMatchArm patterns body (toSpan node)

lowerPattern :: SyntaxNode -> Maybe Pattern
lowerPattern node = case ndKind (unGreenNode (snGreen node)) of
    SK_Node NK_PATTERN_VAR -> do
        tok <- firstToken node
        let name = T.unpack $ gtText (stGreen tok)
        Just $ PVar name (toSpan node)
    SK_Node NK_PATTERN_WILDCARD ->
        Just $ PWildcard (toSpan node)
    SK_Node NK_PATTERN_LITERAL -> do
        tok <- firstToken node
        lit <- lowerPatternLiteral tok
        Just $ PLit lit (toSpan node)
    SK_Node NK_PATTERN_CONSTRUCTOR -> do
        nameTok <- firstToken node
        let name = T.unpack $ gtText (stGreen nameTok)

        let patternChildren = filter isPatternNode (children node)
        patterns <- mapM lowerPattern patternChildren

        Just $ PConstructor name patterns (toSpan node)
    SK_Node NK_PATTERN_TUPLE -> do
        let patternChildren = filter isPatternNode (children node)
        patterns <- mapM lowerPattern patternChildren
        Just $ PTuple patterns (toSpan node)
    SK_Node NK_PATTERN_LIST -> do
        let patternChildren = filter isPatternNode (children node)
        patterns <- mapM lowerPattern patternChildren
        Just $ PArray patterns (toSpan node)
    SK_Node NK_PATTERN_AS -> do
        nameTok <- firstToken node
        let name = T.unpack $ gtText (stGreen nameTok)

        let patternChildren = filter isPatternNode (children node)
        case patternChildren of
            (inner : _) -> do
                innerPat <- lowerPattern inner
                Just $ PAs name innerPat (toSpan node)
            [] -> Nothing
    SK_Node NK_PATTERN -> do
        inner <- firstChild node
        lowerPattern inner
    _ -> Nothing

isPatternNode :: SyntaxNode -> Bool
isPatternNode node = case ndKind (unGreenNode (snGreen node)) of
    SK_Node nk -> nk `elem` patternKinds
    _ -> False
  where
    patternKinds =
        [ NK_PATTERN
        , NK_PATTERN_VAR
        , NK_PATTERN_CONSTRUCTOR
        , NK_PATTERN_LITERAL
        , NK_PATTERN_WILDCARD
        , NK_PATTERN_AS
        , NK_PATTERN_TUPLE
        , NK_PATTERN_LIST
        ]

lowerPatternLiteral :: SyntaxToken -> Maybe Literal
lowerPatternLiteral tok = case gtKind (stGreen tok) of
    SK_Token TokenNumber ->
        Just $ LitInt (read $ T.unpack $ gtText (stGreen tok))
    SK_Token (TokenString _) ->
        Just $ LitString (T.unpack $ gtText (stGreen tok))
    SK_Token TokenTrue ->
        Just $ LitBool True
    SK_Token TokenFalse ->
        Just $ LitBool False
    _ -> Nothing

lowerComposeStmt :: SyntaxNode -> Maybe ComposeStmt
lowerComposeStmt node = case ndKind (unGreenNode (snGreen node)) of
    SK_Node NK_COMPOSE_BIND -> do
        nameTok <- findNameToken node
        let name = T.unpack $ gtText (stGreen nameTok)
        exprNode <- findExprChild node
        expr <- lowerExpr exprNode
        Just $ CSBind name expr (toSpan node)
    SK_Node NK_COMPOSE_LET -> do
        nameTok <- findNameToken node
        let name = T.unpack $ gtText (stGreen nameTok)
        exprNode <- findExprChild node
        expr <- lowerExpr exprNode
        Just $ CSLet name expr (toSpan node)
    SK_Node NK_COMPOSE_STMT -> do
        exprNode <- findExprChild node
        expr <- lowerExpr exprNode
        Just $ CSExpr expr (toSpan node)
    _ -> Nothing

findNameToken :: SyntaxNode -> Maybe SyntaxToken
findNameToken node =
    case filter isNameToken (childrenWithTokens node) of
        (SyntaxTokenElement tok : _) -> Just tok
        _ -> Nothing
  where
    isNameToken (SyntaxTokenElement tok) =
        gtKind (stGreen tok)
            `elem` [ SK_Token TokenLowerIdentifier
                   , SK_Token TokenUpperIdentifier
                   , SK_Token TokenVarSymbol
                   ]
    isNameToken _ = False

findExprChild :: SyntaxNode -> Maybe SyntaxNode
findExprChild node =
    case filter isExprNode (children node) of
        (e : _) -> Just e
        [] -> Nothing

extractLambdaParams :: SyntaxNode -> [String]
extractLambdaParams node =
    case childOfKind (SK_Node NK_PARAM_LIST) node of
        Just paramList -> mapMaybe extractParamName (children paramList)
        Nothing -> mapMaybe extractParamName (children node)
  where
    extractParamName n = do
        tok <- firstToken n
        case gtKind (stGreen tok) of
            SK_Token TokenLowerIdentifier -> Just $ T.unpack $ gtText (stGreen tok)
            _ -> Nothing

extractTypeVars :: SyntaxNode -> [TyVar]
extractTypeVars node =
    mapMaybe extractTyVar (children node)
  where
    extractTyVar n = case ndKind (unGreenNode (snGreen n)) of
        SK_Node NK_TYPE_VAR -> do
            tok <- firstToken n
            let name = T.unpack $ gtText (stGreen tok)
            Just $ TypeVar name KindStar
        _ -> Nothing

extractConstraints :: SyntaxNode -> [Constraint]
extractConstraints node =
    mapMaybe extractConstraint (childrenOfKind (SK_Node NK_CONSTRAINT) node)
  where
    extractConstraint constraintNode = do
        ty <- lowerConstraintType constraintNode
        Just $ Constraint ty

    lowerConstraintType n =
        let typeChildren =
                childrenOfKind (SK_Node NK_TYPE_CONSTRUCTOR) n
                    ++ childrenOfKind (SK_Node NK_TYPE_VAR) n
        in case typeChildren of
            [] -> Nothing
            (first : rest) -> do
                firstTy <- lowerType first
                restTys <- mapM lowerType rest
                Just $ foldl TApp firstTy restTys

extractForallVars :: SyntaxNode -> [TyVar]
extractForallVars node =
    maybe [] extractTypeVars (childOfKind (SK_Node NK_FORALL) node)
