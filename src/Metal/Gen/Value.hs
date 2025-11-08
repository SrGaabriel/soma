{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Metal.Gen.Value where

import Control.Monad.Reader (asks)
import Data.Map (Map)
import qualified Data.Map as Map

import Metal.Expr
import Metal.Gen.Core
import Metal.Metadata
import Project.Symbols
import Syntax.Tree
import Typing.Currying (uncurryFunction)
import Typing.Types

metallizeValue :: Expr -> MetalGen MetallicExpr
metallizeValue (ExprNum n _) = pure $ MLit (MInt (read n))
metallizeValue (ExprStr s _) = pure $ MLit (MString s)
metallizeValue (ExprBool b _) = pure $ MLit (MBool b)
metallizeValue (ExprUVar name _) = do
    lookupVar name >>= \case
        Just ty -> pure $ MVar name ty
        Nothing -> error $ "Undefined variable: " ++ name
metallizeValue expr@(ExprVar (ResolvedSymbol{resolvedSymbolName}) _) =
    MVar resolvedSymbolName <$> getExprType expr
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
metallizeValue expr@(ExprCompose stmts _) =
    MCompose <$> metallizeComposeStmtsInScope stmts <*> getExprType expr
metallizeValue expr@(ExprIf condition ifBlock elseBlock _) =
    MIf
        <$> metallizeValue condition
        <*> metallizeValue ifBlock
        <*> metallizeValue elseBlock
        <*> getExprType expr
metallizeValue u = error $ "Cannot metallize value: " ++ show u

metallizeComposeStmt :: ComposeStmt -> MetalGen MetallicComposeStmt
metallizeComposeStmt (CSBind name e _) = MCBind name <$> metallizeValue e
metallizeComposeStmt (CSLet name e _) = MCLet name <$> metallizeValue e
metallizeComposeStmt (CSExpr e _) = MCExpr <$> metallizeValue e

metallizeComposeStmtsInScope :: [ComposeStmt] -> MetalGen [MetallicComposeStmt]
metallizeComposeStmtsInScope [] = pure []
metallizeComposeStmtsInScope (stmt : rest) = do
    (mStmt, mbBinding) <- case stmt of
        CSBind name e _ -> do
            me <- metallizeValue e
            eTy <- getExprType e
            pure (MCBind name me, Just (name, eTy))
        CSLet name e _ -> do
            me <- metallizeValue e
            eTy <- getExprType e
            pure (MCLet name me, Just (name, eTy))
        CSExpr e _ -> do
            me <- metallizeValue e
            pure (MCExpr me, Nothing)

    restStmts <- case mbBinding of
        Just (name, eTy) -> do
            parentScope <- asks metalCurrentScope
            let newScope = MetalScope name (Map.insert name eTy (scopeVars parentScope)) (Just parentScope)
            withScope newScope $ metallizeComposeStmtsInScope rest
        Nothing -> metallizeComposeStmtsInScope rest

    pure (mStmt : restStmts)

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
                    let callee = MTypeApp (MVar resolvedSymbolName baseTy) typeArgs resultTy
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
