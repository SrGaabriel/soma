{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Metal.Gen.Value where
import Metal.Expr
import Metal.Gen.Core
import Syntax.Tree
import Project.Symbols
import Metal.Metadata
import Control.Monad.Reader (asks)
import qualified Data.Map as Map
import Typing.Types
import Data.Map (Map)
import Decisions.Model
import Metal.Gen.Patterns (metallizeDag)

metallizeValue :: Expr -> MetalGen MetallicExpr
metallizeValue (ExprNum n _) = pure $ MLit (MInt $ read n)
metallizeValue (ExprStr s _) = pure $ MLit (MString s)
metallizeValue (ExprBool b _) = pure $ MLit (MBool b)
metallizeValue (ExprUVar name _) = do
        maybeTy <- lookupVar name
        case maybeTy of
            Just ty -> return $ MVar name ty
            Nothing -> error $ "Undefined variable: " ++ name
metallizeValue expr@(ExprVar symbol@(ResolvedSymbol { resolvedSymbolName }) _) = do
        ty <- getExprType expr
        
        case resolvedSymbolKind symbol of
            DataConstructorSymbol _ -> do
                meta <- lookupConstructor resolvedSymbolName
                pure $ MConstruct resolvedSymbolName (mcmTag meta) [] ty
            
            _ -> pure $ MVar resolvedSymbolName ty
metallizeValue expr@(ExprApp _ _) = do
        let (base, args) = uncurryApp expr
        metallizeApp base args
metallizeValue expr@(ExprArray elements _) = do
        ty <- getExprType expr
        metalElems <- mapM metallizeValue elements
        return $ MArrayLit metalElems ty
metallizeValue (ExprLet { letName, letValue, letBody }) = do
        valueTy <- getExprType letValue
        metalValue <- metallizeValue letValue
        
        parentScope <- asks metalCurrentScope
        let newScope = MetalScope letName (Map.insert letName valueTy (scopeVars parentScope)) (Just parentScope)
        
        metalBody <- withScope newScope $ metallizeValue letBody
        bodyTy <- getExprType letBody
        
        return $ MLet letName metalValue metalBody bodyTy
metallizeValue (ExprPatternMatch scrutinee arms _) = do
    metalScrutinee <- metallizeValue scrutinee
    resultTy <- getExprType (ExprPatternMatch scrutinee arms undefined)
    metallizePatternMatch metalScrutinee arms resultTy
metallizeValue u = error $ "Cannot metallize value: " ++ show u

metallizePatternMatch :: MetallicExpr -> [Expr] -> Type -> MetalGen MetallicExpr
metallizePatternMatch scrutinee arms resultTy = do
    let armData = [(pats, body) | ExprPatternMatchArm pats body _ <- arms]
        patterns = map fst armData
        clauses = zip patterns [0..length patterns - 1]
        matrix = mkPatternMatrix clauses
        tree = compile matrix
        dag = buildDAG tree
    bodies <- mapM (metallizeValue . snd) armData
    
    pure $ metallizeDag scrutinee dag bodies resultTy

metallizeApp :: Expr -> [Expr] -> MetalGen MetallicExpr
metallizeApp base args = do
    tyMap <- asks metalTypeMap
    let appExpr = foldl ExprApp base args
    resultTy <- getExprType appExpr
    metalArgs <- mapM metallizeValue args
    
    case base of
        ExprVar symbol@(ResolvedSymbol { resolvedSymbolName }) _
            | isTypeclassMethod symbol -> do
                -- let TypeClassMethodSymbol className = resolvedSymbolKind symbol
                
                typeArgs <- extractTypeArgs base args
                
                return $ MPolyApp resolvedSymbolName typeArgs metalArgs resultTy
        
        ExprVar (ResolvedSymbol { resolvedSymbolName }) _ -> do
            let Just (Forall typeVars _ _) = Map.lookup base tyMap
            
            if null typeVars
                then return $ MApp resolvedSymbolName metalArgs resultTy
                else do
                    typeArgs <- extractTypeArgs base args
                    return $ MPolyApp resolvedSymbolName typeArgs metalArgs resultTy
        
        _ -> do
            metalBase <- metallizeValue base
            return $ MIndirectCall metalBase metalArgs resultTy

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
    
    if null baseTypeVars
        then return []
        else do
            let appExpr = foldl ExprApp base args
            let Just (Forall _ _ instantiatedType) = Map.lookup appExpr tyMap
            
            let subst = matchPolyWithConcrete baseFuncType instantiatedType
            return [Map.findWithDefault (TVar tv) tv subst | tv <- baseTypeVars]

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