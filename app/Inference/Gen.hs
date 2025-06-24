{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Inference.Gen where

import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import qualified Debug.Trace as Debug
import Inference.Core (TypeEnv)
import Logging.PrettyTrees (TreeShow (treeShow))
import Syntax.Patterns (Pattern (..))
import Syntax.Tree (Expr (..), MultiPatternArm (MultiPatternArm), exprChildren)
import Typing.Types (Constraint (..), Kind (..), QualifiedType (..), TyVar (..), Type (..), boolType, cleanQualified, intType, strType)

newtype GenM a = GenM (StateT GenState (Reader TypeEnv) a)
    deriving (Functor, Applicative, Monad, MonadState GenState, MonadReader TypeEnv)

data GenState = GenState
    { gsCounter :: Int
    , gsTypeMap :: Map.Map Expr Type
    }
    deriving (Show)

data ConstraintSet = ConstraintSet
    { csTypeConstraints :: [TypeConstraint]
    , csClassConstraints :: [Constraint]
    }
    deriving (Show)

instance Semigroup ConstraintSet where
    (ConstraintSet ts1 cs1) <> (ConstraintSet ts2 cs2) =
        ConstraintSet (ts1 ++ ts2) (cs1 ++ cs2)

instance Monoid ConstraintSet where
    mempty = ConstraintSet [] []

data TypeConstraint = TypeConstraint
    { tcExpr :: Expr
    , tcExpected :: Type
    , tcActual :: Type
    }
    deriving (Show)

runGenM :: TypeEnv -> GenM a -> (a, GenState)
runGenM env (GenM m) = runReader (runStateT m initialState) env
  where
    initialState = GenState 0 Map.empty

freshTyVar :: Kind -> GenM TyVar
freshTyVar k = do
    n <- gets gsCounter
    modify $ \s -> s{gsCounter = n + 1}
    return $ TypeVar ("t" ++ show n) k

recordType :: Expr -> Type -> GenM ()
recordType expr ty = modify $ \s -> s{gsTypeMap = Map.insert expr ty (gsTypeMap s)}

generateConstraints :: Expr -> GenM (Maybe Type, ConstraintSet)
generateConstraints expr = case expr of
    ExprNum _ _ -> do
        let ty = intType
        recordType expr ty
        pure $ (Just ty, ConstraintSet [] [])
    ExprStr _ _ -> do
        let ty = strType
        recordType expr ty
        pure $ (Just ty, ConstraintSet [] [])
    ExprBool _ _ -> do
        let ty = boolType
        recordType expr ty
        pure $ (Just ty, ConstraintSet [] [])
    ExprVar name _ -> do
        env <- ask
        case Map.lookup name env of
            Just (Forall tvs cs t) -> do
                freshVars <- mapM (freshTyVar . tvKind) tvs
                let subst = Map.fromList (zip tvs (map TVar freshVars))
                let instType = applyTySubst subst t
                let instConstraints = map (applyConstraintSubst subst) cs
                recordType expr instType
                return $ (Just instType, ConstraintSet [] instConstraints)
            Nothing -> error $ "Unbound variable: " ++ show name
    ExprApp f a -> do
        (Just tf, cf) <- generateConstraints f
        (Just ta, ca) <- generateConstraints a
        retVar <- freshTyVar KindStar
        let retType = TVar retVar
        let funConstraint = TypeConstraint expr tf (TArrow ta retType)
        let combinedConstraints =
                ConstraintSet
                    (funConstraint : csTypeConstraints cf ++ csTypeConstraints ca)
                    (csClassConstraints cf ++ csClassConstraints ca)
        recordType expr retType
        return (Just retType, combinedConstraints)
    ExprLambda paramNames body _ -> do
        paramVars <- mapM (const $ freshTyVar KindStar) paramNames
        let paramTypes = map TVar paramVars
        let paramScheme t = Forall [] [] t

        let paramBindings = Map.fromList (zip paramNames (map (paramScheme . TVar) paramVars))
        let extendEnv currentEnv = Map.union paramBindings currentEnv

        (Just bodyType, bodyConstraints) <- local extendEnv (generateConstraints body)

        let funcType = foldr TArrow bodyType paramTypes
        recordType expr funcType
        return (Just funcType, bodyConstraints)
    ExprLet name value body _ -> do
        (Just valueType, valueConstraints) <- generateConstraints value
        let extendEnv currentEnv = Map.insert name (cleanQualified valueType) currentEnv
        (Just bodyType, bodyConstraints) <- local extendEnv (generateConstraints body)
        let combinedConstraints =
                ConstraintSet
                    (csTypeConstraints valueConstraints ++ csTypeConstraints bodyConstraints)
                    (csClassConstraints valueConstraints ++ csClassConstraints bodyConstraints)
        recordType expr bodyType
        return (Just bodyType, combinedConstraints)
    ExprBindingDef name bindType body _ -> do
        let extendEnv currentEnv = Map.insert name bindType currentEnv
        (Just bodyType, bodyConstraints) <- local extendEnv (generateConstraints body)
        let combinedConstraints =
                ConstraintSet
                    (csTypeConstraints bodyConstraints)
                    (csClassConstraints bodyConstraints)
        recordType expr bodyType
        return (Just bodyType, combinedConstraints)
    ExprDerivedPatternMatch armTypes arms -> do
        mappedArms <- mapM processArm arms
        let (bodyTypes, bodyConstraintsList) = unzip mappedArms

        let combinedBodyType = foldr1 (\t1 t2 -> TArrow t1 t2) bodyTypes
        let combinedConstraints = foldr (<>) (ConstraintSet [] []) bodyConstraintsList

        recordType expr combinedBodyType
        return (Just combinedBodyType, combinedConstraints)
      where
        processArm (MultiPatternArm patterns body) = do
            currentEnv <- ask
            patternEnv <- generatePatternBindings currentEnv patterns armTypes

            let extendWithPatterns _ = patternEnv
            (Just bodyType, bodyConstraints) <- local extendWithPatterns (generateConstraints body)

            return (bodyType, bodyConstraints)
    u -> do
        let children = exprChildren expr
        results <- mapM generateConstraints children
        let combinedConstraints = mconcat (map snd results)
        Debug.trace ("Generating constraints for unsupported expression: " ++ treeShow u)
            $ return (Nothing, combinedConstraints)

generatePatternBindings :: TypeEnv -> [Pattern] -> [QualifiedType] -> GenM TypeEnv
generatePatternBindings env patterns armTypes = do
    let zipped = zip patterns armTypes
    bindings <- mapM (\(p, t) -> generatePatternBinding env p t) zipped
    pure $ Map.unions (env : bindings)

generatePatternBinding :: TypeEnv -> Pattern -> QualifiedType -> GenM TypeEnv
generatePatternBinding _env (PVar name) armType = do
    return $ Map.singleton name armType
generatePatternBinding env (PAs name pattern) armType = do
    let asBinding = Map.singleton name armType
    nestedBinding <- generatePatternBinding env pattern armType
    return $ Map.union asBinding nestedBinding
generatePatternBinding env (PConstructor name patterns) armType = do
    currentEnv <- ask
    case Map.lookup name currentEnv of
        Just (Forall tvs cs t) -> do
            freshVars <- mapM (freshTyVar . tvKind) tvs
            let subst = Map.fromList (zip tvs (map TVar freshVars))
            let instType = applyTySubst subst t
            let instConstraints = map (applyConstraintSubst subst) cs

            let argTypes = extractArgTypes instType (length patterns)
            let qualifiedArgTypes = map (\t -> Forall [] instConstraints t) argTypes

            generatePatternBindings env patterns qualifiedArgTypes
        Nothing -> error $ "Unbound constructor: " ++ show name
generatePatternBinding _env _ _ = error "Unsupported pattern type in generatePatternBinding"

extractArgTypes :: Type -> Int -> [Type]
extractArgTypes _ty 0 = []
extractArgTypes (TArrow arg rest) n = arg : extractArgTypes rest (n - 1)
extractArgTypes _ _ = error "Constructor type doesn't match pattern arity"

applyTySubst :: Map.Map TyVar Type -> Type -> Type
applyTySubst s (TVar tv) = Map.findWithDefault (TVar tv) tv s
applyTySubst s (TApp t1 t2) = TApp (applyTySubst s t1) (applyTySubst s t2)
applyTySubst s (TArrow t1 t2) = TArrow (applyTySubst s t1) (applyTySubst s t2)
applyTySubst _ t = t

applyConstraintSubst :: Map.Map TyVar Type -> Constraint -> Constraint
applyConstraintSubst s (Constraint n ts) = Constraint n (map (applyTySubst s) ts)

noConstraints :: ConstraintSet
noConstraints = ConstraintSet [] $ []

instance MonadFail GenM where
    fail msg = error $ "GenM failed: " ++ msg
