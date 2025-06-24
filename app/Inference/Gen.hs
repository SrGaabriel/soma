{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Inference.Gen where

import Control.Monad.State
import qualified Data.Map as Map
import Inference.Core (TypeEnv)
import Syntax.Tree (Expr (..), MultiPatternArm (MultiPatternArm))
import Typing.Types (Constraint (..), Kind (..), QualifiedType (..), TyVar (..), Type (..), boolType, cleanQualified, intType, strType)
import Syntax.Patterns (Pattern (..))
import Inference.Errors (InferenceError(Debug))
import qualified Debug.Trace as Debug
import Logging.PrettyTrees (TreeShow(treeShow))

newtype GenM a = GenM (State Int a)
    deriving (Functor, Applicative, Monad, MonadState Int)

data ConstraintSet = ConstraintSet
    { csTypeConstraints :: [TypeConstraint]
    , csClassConstraints :: [Constraint] -- Your existing Constraint type
    }
    deriving (Show)

data TypeConstraint = TypeConstraint
    { tcExpr :: Expr
    , tcExpected :: Type
    , tcActual :: Type
    }
    deriving (Show)

runGenM :: GenM a -> (a, Int)
runGenM (GenM m) = runState m 0

freshTyVar :: Kind -> GenM TyVar
freshTyVar k = do
    n <- get
    put (n + 1)
    return $ TypeVar ("t" ++ show n) k

generateConstraints :: TypeEnv -> Expr -> GenM (Maybe (Type, ConstraintSet))
generateConstraints env expr = case expr of
    ExprNum _ _ ->
        return $ Just (intType, noConstraints)
    ExprStr _ _ ->
        return $ Just (strType, noConstraints)
    ExprBool _ _ ->
        return $ Just (boolType, noConstraints)
    ExprVar name _ -> case Debug.trace ("Env: " ++ treeShow env) $ Map.lookup name env of
        Just (Forall tvs cs t) -> do
            freshVars <- mapM (freshTyVar . tvKind) tvs
            let subst = Map.fromList (zip tvs (map TVar freshVars))
            let instType = applyTySubst subst t
            let instConstraints = map (applyConstraintSubst subst) cs
            return $ Just (instType, ConstraintSet [] instConstraints)
        Nothing -> error $ "Unbound variable: " ++ show name
    ExprApp f a -> do
        Just (tf, cf) <- generateConstraints env f
        Just (ta, ca) <- generateConstraints env a
        retVar <- freshTyVar KindStar
        let retType = TVar retVar
        let funConstraint = TypeConstraint expr tf (TArrow ta retType)
        let combinedConstraints =
                ConstraintSet
                    (funConstraint : csTypeConstraints cf ++ csTypeConstraints ca)
                    (csClassConstraints cf ++ csClassConstraints ca)
        return $ Just (retType, combinedConstraints)
    ExprLambda paramNames body _ -> do
        paramVars  <- mapM (const $ freshTyVar KindStar) paramNames
        let paramTypes = map TVar paramVars
        let paramScheme t = Forall [] [] t
        let env' = Debug.trace ("Generating lambda with params: " ++ show paramNames ++ " and types: " ++ show paramTypes) $
                Map.union (Map.fromList (zip paramNames (map (paramScheme . TVar) paramVars))) env
        Debug.traceM ("New environment for lambda: " ++ treeShow env')

        Just (bodyType, bodyCS) <- generateConstraints env' body

        let funcType = foldr TArrow bodyType paramTypes
        return $ Just (funcType, bodyCS)
    ExprLet name value body _ -> do
        Just (valueType, valueConstraints) <- generateConstraints env value
        let newEnv = Map.insert name (cleanQualified valueType) env
        Just (bodyType, bodyConstraints) <- generateConstraints newEnv body
        let combinedConstraints =
                ConstraintSet
                    (csTypeConstraints valueConstraints ++ csTypeConstraints bodyConstraints)
                    (csClassConstraints valueConstraints ++ csClassConstraints bodyConstraints)
        return $ Just (bodyType, combinedConstraints)
    ExprBindingDef name bindType body _ -> do
        let newEnv = Map.insert name bindType env
        Just (bodyType, bodyConstraints) <- generateConstraints newEnv body
        let combinedConstraints =
                ConstraintSet
                    (csTypeConstraints bodyConstraints)
                    (csClassConstraints bodyConstraints)
        return $ Just (bodyType, combinedConstraints)
    ExprDerivedPatternMatch armTypes arms -> do
        mappedArms <- mapM (
            \(MultiPatternArm patterns body) -> do
                patternEnv <- generatePatternBindings env patterns armTypes
                Just (bodyType, bodyConstraints) <- generateConstraints patternEnv body
                return (bodyType, bodyConstraints)
            ) arms
        let (bodyTypes, bodyConstraintsList) = unzip mappedArms
        let combinedBodyType = foldr1 (\t1 t2 -> TArrow t1 t2) bodyTypes
        let combinedConstraints = foldr1 (\c1 c2 -> ConstraintSet (csTypeConstraints c1 ++ csTypeConstraints c2) (csClassConstraints c1 ++ csClassConstraints c2)) bodyConstraintsList
        return $ Just (combinedBodyType, combinedConstraints)
    u -> do
        Debug.trace ("Generating constraints for unsupported expression: " ++ treeShow u) $
            return Nothing

generatePatternBindings :: TypeEnv -> [Pattern] -> [QualifiedType] -> GenM TypeEnv
generatePatternBindings env patterns armTyps = do
    let zipped = zip patterns armTyps
    bindings <- mapM (\(p, t) -> generatePatternBinding env p t) zipped
    pure $ Map.unions bindings
    
generatePatternBinding :: TypeEnv -> Pattern -> QualifiedType -> GenM TypeEnv
generatePatternBinding env (PVar name) armType = do
    let newEnv = Map.insert name armType env
    return newEnv
generatePatternBinding env (PAs name pattern) armType = do
    let newEnv = Map.insert name armType env
    generatePatternBinding newEnv pattern armType
generatePatternBinding env (PConstructor name patterns) armType = do
    case Map.lookup name env of
        Just (Forall tvs cs t) -> do
            Debug.traceM ("Generating pattern binding for constructor: " ++ name)
            freshVars <- mapM (freshTyVar . tvKind) tvs
            let subst = Map.fromList (zip tvs (map TVar freshVars))
            let instType = applyTySubst subst t
            let instConstraints = map (applyConstraintSubst subst) cs
            let qualTyped = Forall freshVars instConstraints instType
            let newEnv = Map.insert name (Forall freshVars instConstraints instType) env
            generatePatternBindings newEnv patterns (replicate (length patterns) qualTyped)
        Nothing -> error $ "Unbound constructor: " ++ show name
generatePatternBinding _ _ _ = error "Unsupported pattern type in generatePatternBinding"

applyTySubst :: Map.Map TyVar Type -> Type -> Type
applyTySubst s (TVar tv) = Map.findWithDefault (TVar tv) tv s
applyTySubst s (TApp t1 t2) = TApp (applyTySubst s t1) (applyTySubst s t2)
applyTySubst s (TArrow t1 t2) = TArrow (applyTySubst s t1) (applyTySubst s t2)
applyTySubst _ t = t

applyConstraintSubst :: Map.Map TyVar Type -> Constraint -> Constraint
applyConstraintSubst s (Constraint n ts) = Constraint n (map (applyTySubst s) ts)

noConstraints :: ConstraintSet
noConstraints = ConstraintSet [] []

instance MonadFail GenM where
    fail msg = error $ "GenM failed: " ++ msg