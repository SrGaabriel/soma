{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Metal.Gen.Value where

import Control.Monad.Reader (asks)
import Data.Map (Map)
import qualified Data.Map as Map
import Metal.Expr
import Metal.Gen.Core
import Metal.Gen.Unique (sanitizeName)
import Metal.Metadata
import Project.Symbols
import Syntax.Tree
import Typing.Currying (uncurryFunction)
import Typing.Types

metallizeValue :: Expr -> MetalGen MetallicExpr
metallizeValue (ExprNum n _) = pure $ MLit (MInt (read n))
metallizeValue (ExprStr s _) = pure $ MLit (MString s)
metallizeValue (ExprBool b _) = pure $ MLit (MBool b)
metallizeValue expr@(ExprVar symbol@(ResolvedSymbol{resolvedSymbolName}) _) = do
    exprType <- getExprType expr
    let var = MVar resolvedSymbolName exprType
    pure
        $ if isBinding symbol
            then MCall var [] exprType
            else var
metallizeValue expr@(ExprApp _ _) = do
    let (base, args) = uncurryApp expr
    metallizeApp base args
metallizeValue expr@(ExprArray elements _) =
    MArrayLit <$> mapM metallizeValue elements <*> getExprType expr
metallizeValue expr@(ExprTuple elements _) =
    MTuple <$> mapM metallizeValue elements <*> getExprType expr
metallizeValue (ExprLet{letName, letValue, letBody}) = do
    valueTy <- getExprType letValue
    metalValue <- metallizeValue letValue
    parentScope <- asks metalCurrentScope
    let newScope = MetalScope letName (Map.insert letName valueTy (scopeVars parentScope)) (Just parentScope)
    metalBody <- withScope newScope $ metallizeValue letBody
    MLet letName metalValue metalBody <$> getExprType letBody
metallizeValue expr@(ExprPatternMatch scrutinee arms _) =
    (MCase . (: []) <$> metallizeValue scrutinee)
        <*> mapM metallizeArm arms
        <*> pure Nothing
        <*> getExprType expr
  where
    metallizeArm :: Expr -> MetalGen MCaseArm
    metallizeArm (ExprPatternMatchArm pats body _) =
        MCaseArm pats <$> metallizeValue body
    metallizeArm other = error $ "Invalid pattern match arm: " ++ show other
metallizeValue expr@(ExprLambda paramNames body _) = do
    ty <- getExprType expr
    let (paramTypes, _retType) = uncurryFunction ty
    parentScope <- asks metalCurrentScope
    let paramBindings = Map.fromList (zip paramNames paramTypes)
        lambdaScope = MetalScope "lambda" paramBindings (Just parentScope)
    metalBody <- withScope lambdaScope $ metallizeValue body
    pure $ MLambda paramNames metalBody ty
metallizeValue expr@(ExprCompose stmts _) = do
    resultTy <- getExprType expr
    desugarCompose stmts resultTy
metallizeValue expr@(ExprIf condition ifBlock elseBlock _) =
    MIf
        <$> metallizeValue condition
        <*> metallizeValue ifBlock
        <*> metallizeValue elseBlock
        <*> getExprType expr
metallizeValue u = error $ "Cannot metallize value: " ++ show u

{- | Desugar compose blocks into explicit monad operations.

   Desugaring rules:
   - MCBind x <- action; rest  =>  >>= action (\x -> rest)
   - MCLet x = expr; rest      =>  let x = expr in rest
   - MCExpr action; rest       =>  >> action rest
   - Final MCExpr action       =>  action

   Types:
   - >>=  :: m a -> (a -> m b) -> m b
   - >>   :: m a -> m b -> m b
-}
desugarCompose :: [ComposeStmt] -> Type -> MetalGen MetallicExpr
desugarCompose [] _ = error "Empty compose block"
desugarCompose [CSExpr e _] _ = metallizeValue e
desugarCompose (stmt : rest) resultTy = case stmt of
    -- CSBind x <- action; rest  =>  >>= action (\x -> desugar rest)
    CSBind name action _ -> do
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
        restExpr <- withScope newScope $ desugarCompose rest resultTy
        -- Build: >>= action (\x -> restExpr)
        let bindVar = MVar ">>=" bindTy
            lambda = MLambda [name] restExpr contTy
        pure $ MCall bindVar [metalAction, lambda] resultTy

    -- CSLet x = expr; rest  =>  let x = expr in (desugar rest)
    CSLet name expr _ -> do
        metalExpr <- metallizeValue expr
        let exprTy = getType metalExpr
        parentScope <- asks metalCurrentScope
        let newScope = MetalScope name (Map.insert name exprTy (scopeVars parentScope)) (Just parentScope)
        restExpr <- withScope newScope $ desugarCompose rest resultTy
        pure $ MLet name metalExpr restExpr resultTy

    -- CSExpr action; rest  =>  >> action (desugar rest)
    CSExpr action _ -> do
        metalAction <- metallizeValue action
        let actionTy = getType metalAction
        -- Build the then operator type: m a -> m b -> m b
        let thenTy = TArrow actionTy (TArrow resultTy resultTy)
        -- Desugar rest
        restExpr <- desugarCompose rest resultTy
        -- Build: >> action restExpr
        let thenVar = MVar ">>" thenTy
        pure $ MCall thenVar [metalAction, restExpr] resultTy

-- | Extract the inner type from a monadic type (m a -> a)
extractMonadInner :: Type -> Type
extractMonadInner (TApp _ inner) = inner
extractMonadInner t = t -- fallback for malformed types

metallizeApp :: Expr -> [Expr] -> MetalGen MetallicExpr
metallizeApp base args = do
    tyMap <- asks metalTypeMap
    let appExpr = foldl ExprApp base args
    resultTy <- getExprType appExpr
    metalArgs <- mapM metallizeValue args

    case base of
        ExprVar symbol@(ResolvedSymbol{resolvedSymbolName}) _
            | isDataConstructor symbol -> do
                meta <- lookupConstructor resolvedSymbolName
                pure $ MConstruct resolvedSymbolName (mcmTag meta) metalArgs resultTy
        ExprVar (ResolvedSymbol{resolvedSymbolName}) _ -> do
            case Map.lookup base tyMap of
                Just (Forall baseTypeVars _ _) | not (null baseTypeVars) -> do
                    typeArgs <- extractTypeArgs base args
                    baseTy <- getExprType base
                    let sanitized = sanitizeName resolvedSymbolName
                    let callee = MTypeApp (MVar sanitized baseTy) typeArgs resultTy
                    pure $ MCall callee metalArgs resultTy
                _ -> (MCall . MVar resolvedSymbolName <$> getExprType base) <*> pure metalArgs <*> pure resultTy
        _ -> MCall <$> metallizeValue base <*> pure metalArgs <*> pure resultTy

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
