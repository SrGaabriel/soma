{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Metal.Gen.Value where

import Control.Monad.Reader (asks)
import Data.Map (Map)
import qualified Data.Map as Map
import Lexing.Position (Span)
import Metal.Expr hiding (exprSpan)
import Metal.Gen.Core
import Metal.Gen.Unique (sanitizeName)
import Metal.Metadata
import Project.Symbols
import Syntax.Tree
import Typing.Currying (uncurryFunction)
import Typing.Types

metallizeValue :: Expr -> MetalGen TypedExpr
metallizeValue (ExprNum n span') = pure $ MLit (MInt (read n)) span'
metallizeValue (ExprStr s span') = pure $ MLit (MString s) span'
metallizeValue (ExprBool b span') = pure $ MLit (MBool b) span'
metallizeValue expr@(ExprVar symbol@(ResolvedSymbol{resolvedSymbolName}) span') = do
    exprType <- getExprType expr
    let var = MVar resolvedSymbolName exprType span'
    pure
        $ if isBinding symbol
            then MCall var [] exprType span'
            else var
metallizeValue expr@(ExprApp _ _) = do
    let (base, args) = uncurryApp expr
    metallizeApp base args
metallizeValue expr@(ExprArray elements span') =
    MArrayLit <$> mapM metallizeValue elements <*> getExprType expr <*> pure span'
metallizeValue expr@(ExprTuple elements span') =
    MTuple <$> mapM metallizeValue elements <*> getExprType expr <*> pure span'
metallizeValue (ExprLet{letName, letValue, letBody, letSpan}) = do
    valueTy <- getExprType letValue
    metalValue <- metallizeValue letValue
    parentScope <- asks metalCurrentScope
    let newScope = MetalScope letName (Map.insert letName valueTy (scopeVars parentScope)) (Just parentScope)
    metalBody <- withScope newScope $ metallizeValue letBody
    bodyTy <- getExprType letBody
    pure $ MLet letName metalValue metalBody bodyTy letSpan
metallizeValue expr@(ExprPatternMatch scrutinee arms span') = do
    exprTy <- getExprType expr
    MCase . (: [])
        <$> metallizeValue scrutinee
        <*> mapM metallizeArm arms
        <*> pure Nothing
        <*> pure exprTy
        <*> pure span'
  where
    metallizeArm :: Expr -> MetalGen TypedArm
    metallizeArm (ExprPatternMatchArm pats body _) =
        MCaseArm pats <$> metallizeValue body
    metallizeArm other = error $ "Invalid pattern match arm: " ++ show other
metallizeValue expr@(ExprLambda paramNames body span') = do
    ty <- getExprType expr
    let (paramTypes, _retType) = uncurryFunction ty
    parentScope <- asks metalCurrentScope
    let paramBindings = Map.fromList (zip paramNames paramTypes)
        lambdaScope = MetalScope "lambda" paramBindings (Just parentScope)
    metalBody <- withScope lambdaScope $ metallizeValue body
    pure $ MLambda (zip paramNames paramTypes) metalBody ty span'
metallizeValue expr@(ExprCompose stmts span') = do
    resultTy <- getExprType expr
    desugarCompose stmts resultTy span'
metallizeValue expr@(ExprIf condition ifBlock elseBlock span') = do
    exprTy <- getExprType expr
    MIf
        <$> metallizeValue condition
        <*> metallizeValue ifBlock
        <*> metallizeValue elseBlock
        <*> pure exprTy
        <*> pure span'
metallizeValue u = error $ "Cannot metallize value: " ++ show u

desugarCompose :: [ComposeStmt] -> Type -> Span -> MetalGen TypedExpr
desugarCompose [] _ _ = error "Empty compose block"
desugarCompose [CSExpr e _] _ _ = metallizeValue e
desugarCompose (stmt : rest) resultTy span' = case stmt of
    CSBind name action stmtSpan -> do
        metalAction <- metallizeValue action
        let actionTy = getType metalAction
        -- Extract the inner type 'a' from 'm a'
        let innerTy = extractMonadInner actionTy
        -- Build the continuation type: a -> m b (where m b is resultTy)
        let contTy = TArrow innerTy resultTy
        -- Build the bind operator type: m a -> (a -> m b) -> m b
        let bindTy = TArrow actionTy (TArrow contTy resultTy)
        -- Desugar rest in scope with x bound
        parentScope <- asks metalCurrentScope
        let newScope = MetalScope name (Map.insert name innerTy (scopeVars parentScope)) (Just parentScope)
        restExpr <- withScope newScope $ desugarCompose rest resultTy span'
        -- Build: >>= action (\x -> restExpr)
        let bindVar = MVar ">>=" bindTy stmtSpan
            lambda = MLambda [(name, innerTy)] restExpr contTy stmtSpan
        pure $ MCall bindVar [metalAction, lambda] resultTy span'
    CSLet name expr stmtSpan -> do
        metalExpr <- metallizeValue expr
        let exprTy = getType metalExpr
        parentScope <- asks metalCurrentScope
        let newScope = MetalScope name (Map.insert name exprTy (scopeVars parentScope)) (Just parentScope)
        restExpr <- withScope newScope $ desugarCompose rest resultTy span'
        pure $ MLet name metalExpr restExpr resultTy stmtSpan
    CSExpr action stmtSpan -> do
        metalAction <- metallizeValue action
        let actionTy = getType metalAction
        -- Build the then operator type: m a -> m b -> m b
        let thenTy = TArrow actionTy (TArrow resultTy resultTy)
        -- Desugar rest
        restExpr <- desugarCompose rest resultTy span'
        -- Build: >> action restExpr
        let thenVar = MVar ">>" thenTy stmtSpan
        pure $ MCall thenVar [metalAction, restExpr] resultTy span'

-- | Extract the inner type from a monadic type (m a -> a)
extractMonadInner :: Type -> Type
extractMonadInner (TApp _ inner) = inner
extractMonadInner t = t -- fallback for malformed types

metallizeApp :: Expr -> [Expr] -> MetalGen TypedExpr
metallizeApp base args = do
    tyMap <- asks metalTypeMap
    let appExpr = foldl ExprApp base args
    let span' = exprSpan appExpr
    resultTy <- getExprType appExpr
    metalArgs <- mapM metallizeValue args

    case base of
        ExprVar symbol@(ResolvedSymbol{resolvedSymbolName}) _
            | isDataConstructor symbol -> do
                meta <- lookupConstructor resolvedSymbolName
                pure $ MConstruct resolvedSymbolName (mcmTag meta) metalArgs resultTy span'
        ExprVar (ResolvedSymbol{resolvedSymbolName}) baseSpan -> do
            case Map.lookup base tyMap of
                Just (Forall baseTypeVars _ _) | not (null baseTypeVars) -> do
                    typeArgs <- extractTypeArgs base args
                    baseTy <- getExprType base
                    let sanitized = sanitizeName resolvedSymbolName
                    let callee = MTypeApp (MVar sanitized baseTy baseSpan) typeArgs resultTy span'
                    pure $ MCall callee metalArgs resultTy span'
                _ -> do
                    baseTy <- getExprType base
                    pure $ MCall (MVar resolvedSymbolName baseTy baseSpan) metalArgs resultTy span'
        _ -> do
            metalBase <- metallizeValue base
            pure $ MCall metalBase metalArgs resultTy span'

isDataConstructor :: Symbol -> Bool
isDataConstructor symbol = case resolvedSymbolKind symbol of
    DataConstructorSymbol _ -> True
    _ -> False

isTypeclassMethod :: Symbol -> Bool
isTypeclassMethod symbol = case resolvedSymbolKind symbol of
    TypeClassMethodSymbol _ -> True
    _ -> False

isBinding :: Symbol -> Bool
isBinding symbol = case resolvedSymbolKind symbol of
    BindingSymbol _ -> True
    _ -> False

extractTypeArgs :: Expr -> [Expr] -> MetalGen [Type]
extractTypeArgs base args = do
    tyMap <- asks metalTypeMap
    let Just (Forall baseTypeVars _ baseFuncType) = Map.lookup base tyMap
        appExpr = foldl ExprApp base args
        Just (Forall _ _ instantiatedType) = Map.lookup appExpr tyMap
        subst = matchPolyWithConcrete baseFuncType instantiatedType
    pure [Map.findWithDefault (TVar tv) tv subst | tv <- baseTypeVars]

matchPolyWithConcrete :: Type -> Type -> Map TyVar Type
matchPolyWithConcrete poly concrete = go poly concrete Map.empty
  where
    go :: Type -> Type -> Map TyVar Type -> Map TyVar Type
    go (TVar tv) concreteType acc = Map.insert tv concreteType acc
    go (TApp poly1 poly2) (TApp conc1 conc2) acc =
        let acc' = go poly1 conc1 acc
        in go poly2 conc2 acc'
    go (TArrow poly1 poly2) (TArrow conc1 conc2) acc =
        let acc' = go poly1 conc1 acc
        in go poly2 conc2 acc'
    go (TConstructor _) (TConstructor _) acc = acc
    go _ _ acc = acc
