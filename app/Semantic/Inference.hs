{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Semantic.Inference where

import Control.Monad.Except
import Control.Monad.State
import Data.Map as Map
import Semantic.Errors (SemanticError (..))
import Typing.Types (Type (..), TyVar (TypeVar, tvKind), Constraint (..), Kind (..), TyConstructor (tcKind))
import Syntax.Tree (Expr)
import qualified Data.Set as Set
import Data.List (nub, find)
import Control.Monad (foldM)

newtype InferM a = InferM
    { runInfer :: ExceptT SemanticError (State InferState) a
    }

instance Functor InferM where
    fmap f m = InferM $ fmap f (runInfer m)

instance Applicative InferM where
    pure x = InferM $ pure x
    f <*> x = InferM $ runInfer f <*> runInfer x

instance Monad InferM where
    m >>= k = InferM $ runInfer m >>= runInfer . k

instance MonadState InferState InferM where
    get = InferM get
    put = InferM . put

instance MonadError SemanticError InferM where
    throwError = InferM . throwError
    catchError m h = InferM $ catchError (runInfer m) (runInfer . h)

type Subst = Map.Map TyVar Type

class Substitutable a where
    apply :: Subst -> a -> a
    ftv :: a -> Set.Set TyVar

instance Substitutable Type where
    apply s (TVar tv) = case Map.lookup tv s of
        Nothing -> TVar tv
        Just t -> t
    apply _ (TConstructor tc) = TConstructor tc
    apply s (TApp t1 t2) = TApp (apply s t1) (apply s t2)
    apply s (TArrow t1 t2) = TArrow (apply s t1) (apply s t2)
    apply s (TForall tv t) = TForall tv (apply (Map.delete tv s) t)
    apply s (TTuple ts) = TTuple (Prelude.map (apply s) ts)
    apply s (TConstrained cs t) = TConstrained (Prelude.map (apply s) cs) (apply s t)
    apply _ (TUnresolved name k) = TUnresolved name k

    ftv (TVar tv) = Set.singleton tv
    ftv (TConstructor _) = Set.empty
    ftv (TApp t1 t2) = ftv t1 `Set.union` ftv t2
    ftv (TArrow t1 t2) = ftv t1 `Set.union` ftv t2
    ftv (TForall tv t) = Set.delete tv (ftv t)
    ftv (TTuple ts) = Set.unions (Prelude.map ftv ts)
    ftv (TConstrained cs t) = Set.unions (Prelude.map ftv cs) `Set.union` ftv t
    ftv (TUnresolved _ _) = Set.empty

nullSubst :: Subst
nullSubst = Map.empty

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Map.map (apply s1) s2 `Map.union` s1

instance Substitutable Constraint where
    apply s (Constraint t ts) = Constraint (apply s t) (Prelude.map (apply s) ts)
    ftv (Constraint t ts) = Set.unions (ftv t : Prelude.map ftv ts)

instance Substitutable a => Substitutable [a] where
    apply s = Prelude.map (apply s)
    ftv = Set.unions . Prelude.map ftv

instance Substitutable TypeEnv where
    apply s = Map.map (apply s)
    ftv = ftv . Map.elems

type TypeMap = Map.Map Expr Type
type TypeEnv = Map.Map String Type
type InstanceEnv = [Instance]

data Instance = Instance
    { instConstraints :: [Constraint]
    , instHead :: Constraint
    } deriving (Show, Eq)

data Evidence
    = EvVar String
    | EvApp Evidence Evidence
    | EvDict String [Evidence]
    deriving (Show, Eq)

data InferState = InferState
    { inferNextVar :: Int
    , inferTypeMap :: TypeMap
    , globalEnv :: TypeEnv
    , structTypes :: Map.Map String Type
    , instanceEnv :: InstanceEnv
    , unsolvedConstraints :: [Constraint]
    }
    deriving (Show)

fresh :: Kind -> InferM TyVar
fresh k = do
    s <- get
    let i = inferNextVar s
    put s{inferNextVar = i + 1}
    pure $ TypeVar ("_t" ++ show i) k

freshTyVar :: Kind -> InferM Type
freshTyVar k = TVar <$> fresh k

generalize :: TypeEnv -> Type -> Type
generalize env t = Prelude.foldr TForall t (Set.toList $ ftv t `Set.difference` ftv env)

addGlobalBinding :: String -> Type -> InferM ()
addGlobalBinding name ty = do
    s <- get
    let globals = globalEnv s
    put s{globalEnv = Map.insert name ty globals}

unify :: Expr -> Type -> Type -> InferM Subst
unify _ t1 t2 | t1 == t2 = return nullSubst

unify expr (TVar tv) t = bindVar expr tv t
unify expr t (TVar tv) = bindVar expr tv t

unify expr (TApp l r) (TApp l' r') = do
    s1 <- unify expr l l'
    s2 <- unify expr (apply s1 r) (apply s1 r')
    return (s1 `composeSubst` s2)

unify expr (TArrow l r) (TArrow l' r') = do
    s1 <- unify expr l l'
    s2 <- unify expr (apply s1 r) (apply s1 r')
    return (s1 `composeSubst` s2)

unify expr (TTuple ts1) (TTuple ts2) 
    | length ts1 == length ts2 = unifyList expr ts1 ts2
    | otherwise = throwError $ TupleLengthMismatch expr ts1 ts2

unify expr (TConstrained cs1 t1) (TConstrained cs2 t2) = do
    s1 <- unify expr t1 t2
    s2 <- unifyConstraints (apply s1 cs1) (apply s1 cs2)
    return (s1 `composeSubst` s2)

unify expr (TConstrained _ t1) t2 = unify expr t1 t2
unify expr t1 (TConstrained _ t2) = unify expr t1 t2

unify expr t1 t2 = throwError $ TypeMismatch expr t1 t2

unifyList :: Expr -> [Type] -> [Type] -> InferM Subst
unifyList _ [] [] = return nullSubst
unifyList expr (t1:ts1) (t2:ts2) = do
    s1 <- unify expr t1 t2
    s2 <- unifyList expr (apply s1 ts1) (apply s1 ts2)
    return (s1 `composeSubst` s2)
unifyList expr _ _ = throwError $ ArityMismatch expr

bindVar :: Expr -> TyVar -> Type -> InferM Subst
bindVar expr tv t
    | t == TVar tv = return nullSubst
    | tv `Set.member` ftv t = throwError $ CircularTypeDependency expr
    | tvKind tv /= kindOf t = throwError $ KindMismatch expr (tvKind tv) (kindOf t)
    | otherwise = return $ Map.singleton tv t

kindOf :: Type -> Kind
kindOf (TVar tv) = tvKind tv
kindOf (TConstructor tc) = tcKind tc
kindOf (TApp t1 t2) = case kindOf t1 of
    KindArrow k1 k2 -> if k1 == kindOf t2 then k2 else error "Kind mismatch in application"
    _ -> error "Cannot apply non-function kind"
kindOf (TArrow _ _) = KindStar
kindOf (TForall _ t) = kindOf t
kindOf (TTuple _) = KindStar
kindOf (TConstrained _ t) = kindOf t
kindOf (TUnresolved _ k) = k

solveConstraints :: [Constraint] -> InferM Subst
solveConstraints constraints = do
    state <- get
    let instances = instanceEnv state
    result <- solveConstraintsWithInstances instances constraints
    case result of
        Left unsolved -> do
            put state{unsolvedConstraints = unsolved ++ unsolvedConstraints state}
            return nullSubst
        Right subst -> return subst

solveConstraintsWithInstances :: InstanceEnv -> [Constraint] -> InferM (Either [Constraint] Subst)
solveConstraintsWithInstances _ [] = return (Right nullSubst)
solveConstraintsWithInstances instances constraints = do
    (solved, unsolved, subst) <- solveStep instances constraints nullSubst
    if Prelude.null solved && not (Prelude.null unsolved)
        then return (Left unsolved)
        else if Prelude.null unsolved
            then return (Right subst)
            else solveConstraintsWithInstances instances unsolved

solveStep :: InstanceEnv -> [Constraint] -> Subst -> InferM ([Constraint], [Constraint], Subst)
solveStep instances constraints currentSubst = do
    let appliedConstraints = apply currentSubst constraints
    foldM processConstraint ([], [], currentSubst) appliedConstraints
  where
    processConstraint (solved, unsolved, subst) constraint = do
        result <- trysolveConstraint instances constraint
        case result of
            Just (newConstraints, newSubst) -> do
                let combinedSubst = subst `composeSubst` newSubst
                let solvedWithNew = constraint : solved
                let resolvedNew = apply combinedSubst newConstraints
                return (solvedWithNew, unsolved ++ resolvedNew, combinedSubst)
            Nothing -> 
                return (solved, constraint : unsolved, subst)

trysolveConstraint :: InstanceEnv -> Constraint -> InferM (Maybe ([Constraint], Subst))
trysolveConstraint instances constraint@(Constraint classType argTypes) = do
    case findMatchingInstance instances constraint of
        Just (Instance prereqs (Constraint _ instArgTypes), matchSubst) -> do
            let resolvedPrereqs = apply matchSubst prereqs
            return $ Just (resolvedPrereqs, matchSubst)
        Nothing -> do
            unificationResult <- tryUnificationSolve constraint
            return unificationResult

findMatchingInstance :: InstanceEnv -> Constraint -> Maybe (Instance, Subst)
findMatchingInstance instances target@(Constraint targetClass targetArgs) = 
    find isMatch (zip instances (Prelude.map (matchInstance target) instances)) >>= extractMatch
  where
    isMatch (_, Just _) = True
    isMatch (_, Nothing) = False
    
    extractMatch (inst, Just subst) = Just (inst, subst)
    extractMatch _ = Nothing

matchInstance :: Constraint -> Instance -> Maybe Subst
matchInstance (Constraint targetClass targetArgs) (Instance _ (Constraint instClass instArgs))
    | targetClass /= instClass = Nothing
    | length targetArgs /= length instArgs = Nothing
    | otherwise = tryUnifyTypes targetArgs instArgs

tryUnifyTypes :: [Type] -> [Type] -> Maybe Subst
tryUnifyTypes [] [] = Just nullSubst
tryUnifyTypes (t1:ts1) (t2:ts2) = do
    s1 <- tryUnifyType t1 t2
    s2 <- tryUnifyTypes (apply s1 ts1) (apply s1 ts2)
    return (s1 `composeSubst` s2)
tryUnifyTypes _ _ = Nothing

tryUnifyType :: Type -> Type -> Maybe Subst
tryUnifyType t1 t2 | t1 == t2 = Just nullSubst
tryUnifyType (TVar tv) t = tryBindVar tv t
tryUnifyType t (TVar tv) = tryBindVar tv t
tryUnifyType (TApp l1 r1) (TApp l2 r2) = do
    s1 <- tryUnifyType l1 l2
    s2 <- tryUnifyType (apply s1 r1) (apply s1 r2)
    return (s1 `composeSubst` s2)
tryUnifyType (TArrow l1 r1) (TArrow l2 r2) = do
    s1 <- tryUnifyType l1 l2
    s2 <- tryUnifyType (apply s1 r1) (apply s1 r2)
    return (s1 `composeSubst` s2)
tryUnifyType _ _ = Nothing

tryBindVar :: TyVar -> Type -> Maybe Subst
tryBindVar tv t
    | t == TVar tv = Just nullSubst
    | tv `Set.member` ftv t = Nothing
    | tvKind tv /= kindOf t = Nothing
    | otherwise = Just $ Map.singleton tv t

tryUnificationSolve :: Constraint -> InferM (Maybe ([Constraint], Subst))
tryUnificationSolve constraint@(Constraint classType argTypes) = do
    result <- tryBuiltinConstraints constraint
           `orElse` tryFunctionalDependencies constraint
           `orElse` tryTypeVariableElimination constraint
           `orElse` tryConstraintSimplification constraint
    return result
  where
    orElse :: InferM (Maybe a) -> InferM (Maybe a) -> InferM (Maybe a)
    orElse m1 m2 = do
        r1 <- m1
        case r1 of
            Just x -> return (Just x)
            Nothing -> m2

tryBuiltinConstraints :: Constraint -> InferM (Maybe ([Constraint], Subst))
tryBuiltinConstraints (Constraint classType argTypes) = do
    case (classType, argTypes) of
        (TConstructor eqTc, [t1, t2]) | isEqualityClass eqTc -> do
            case tryUnifyType t1 t2 of
                Just subst -> return $ Just ([], subst)
                Nothing -> return Nothing
        
        (_, [t1, t2]) | t1 == t2 -> return $ Just ([], nullSubst)
        
        (_, [TConstructor tc1, TConstructor tc2]) 
            | tc1 == tc2 -> return $ Just ([], nullSubst)
        
        _ -> return Nothing
  where
    isEqualityClass tc = tcKind tc == KindArrow KindStar (KindArrow KindStar KindStar)

tryFunctionalDependencies :: Constraint -> InferM (Maybe ([Constraint], Subst))
tryFunctionalDependencies (Constraint classType argTypes) = do
    case argTypes of
        [TApp (TConstructor f) a, TVar tv] -> do
            maybeResultType <- lookupTypeConstructorResult f a
            case maybeResultType of
                Just resultType -> do
                    case tryUnifyType (TVar tv) resultType of
                        Just subst -> return $ Just ([], subst)
                        Nothing -> return Nothing
                Nothing -> return Nothing
        _ -> return Nothing
  where
    lookupTypeConstructorResult _ _ = return Nothing -- todo: implement

tryTypeVariableElimination :: Constraint -> InferM (Maybe ([Constraint], Subst))
tryTypeVariableElimination (Constraint classType argTypes) = do
    case argTypes of
        args | all (== head args) args && not (Prelude.null args) -> 
            case head args of
                TVar _ -> return $ Just ([], nullSubst)
                _ -> return Nothing
        
        _ -> do
            state <- get
            let allConstraints = unsolvedConstraints state
            let thisConstraintVars = ftv (Constraint classType argTypes)
            let otherConstraintVars = Set.unions $ Prelude.map ftv $ 
                    Prelude.filter (/= Constraint classType argTypes) allConstraints
            
            let isolatedVars = thisConstraintVars `Set.difference` otherConstraintVars
            
            if Set.null isolatedVars
                then return Nothing
                else do
                    freshVars <- mapM (\tv -> do
                        fresh' <- fresh (tvKind tv)
                        return (tv, TVar fresh')) (Set.toList isolatedVars)
                    let subst = Map.fromList freshVars
                    return $ Just ([], subst)

tryConstraintSimplification :: Constraint -> InferM (Maybe ([Constraint], Subst))
tryConstraintSimplification (Constraint classType argTypes) = do
    let uniqueArgs = nub argTypes
    if length uniqueArgs < length argTypes
        then return $ Just ([Constraint classType uniqueArgs], nullSubst)
        else do
            simplifiedArgs <- mapM simplifyTypeInConstraint argTypes
            if simplifiedArgs /= argTypes
                then return $ Just ([Constraint classType simplifiedArgs], nullSubst)
                else return Nothing
  where
    simplifyTypeInConstraint :: Type -> InferM Type
    simplifyTypeInConstraint t = case t of
        TApp (TApp f a) b | isAssociativeOp f -> 
            return $ TApp f (TApp (TApp f a) b)
        _ -> return t
    
    isAssociativeOp _ = False

unifyConstraints :: [Constraint] -> [Constraint] -> InferM Subst
unifyConstraints cs1 cs2 = do
    let normalized1 = normalizeConstraints cs1
    let normalized2 = normalizeConstraints cs2
    unifyConstraintLists normalized1 normalized2

normalizeConstraints :: [Constraint] -> [Constraint]
normalizeConstraints = nub . Prelude.map normalizeConstraint

normalizeConstraint :: Constraint -> Constraint  
normalizeConstraint c = c -- todo: implement normalization

unifyConstraintLists :: [Constraint] -> [Constraint] -> InferM Subst
unifyConstraintLists [] [] = return nullSubst
unifyConstraintLists cs1 cs2 
    | length cs1 /= length cs2 = return nullSubst
    | otherwise = do
        substs <- mapM (uncurry unifyConstraintPair) (zip cs1 cs2)
        return $ Prelude.foldl composeSubst nullSubst substs

unifyConstraintPair :: Constraint -> Constraint -> InferM Subst
unifyConstraintPair (Constraint c1 args1) (Constraint c2 args2)
    | c1 /= c2 = return nullSubst
    | length args1 /= length args2 = return nullSubst
    | otherwise = do
        return nullSubst

solveConstraint :: Constraint -> InferM Subst
solveConstraint constraint = do
    result <- solveConstraints [constraint]
    return result

isConstraintSatisfiable :: Constraint -> InferM Bool
isConstraintSatisfiable constraint = do
    state <- get
    result <- trysolveConstraint (instanceEnv state) constraint
    return $ case result of
        Just _ -> True
        Nothing -> False

getUnsolvedConstraints :: InferM [Constraint]
getUnsolvedConstraints = do
    state <- get
    return $ unsolvedConstraints state

clearUnsolvedConstraints :: InferM ()
clearUnsolvedConstraints = do
    state <- get
    put state{unsolvedConstraints = []}

deferConstraint :: Constraint -> InferM ()
deferConstraint constraint = do
    state <- get
    put state{unsolvedConstraints = constraint : unsolvedConstraints state}

resolveDeferred :: InferM Subst
resolveDeferred = do
    state <- get
    let deferred = unsolvedConstraints state
    put state{unsolvedConstraints = []}
    solveConstraints deferred

evalInferM :: InferM a -> InferState -> IO (Either SemanticError a)
evalInferM m st = pure $ evalState (runExceptT (runInfer m)) st

cleanEvalInferM :: InferM a -> IO (Either SemanticError a)
cleanEvalInferM m = evalInferM m (InferState 0 Map.empty Map.empty Map.empty [] [])

runInferM :: InferM a -> InferState -> IO (Either SemanticError a, InferState)
runInferM m st = pure $ runState (runExceptT (runInfer m)) st

cleanRunInferM :: InferM a -> IO (Either SemanticError a, InferState)
cleanRunInferM m = runInferM m (InferState 0 Map.empty Map.empty Map.empty [] [])