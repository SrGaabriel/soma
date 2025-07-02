{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Inference.Gen where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as Map
import Inference.Core (TypeEnv, UnificationPurpose (..))
import Inference.Errors (InferenceError (..))
import Syntax.Patterns (Pattern (..))
import Syntax.Tree (Expr (..), exprChildren)
import Typing.Types (Constraint (..), Kind (..), QualifiedType (..), TyVar (..), Type (..), SkolemVar(..), Rigidity(..), boolType, cleanQualified, intType, strType, vectorize, vectorizeAllQualified)
import Utils.Lists (hardHead)

newtype GenM a = GenM (StateT GenState (ReaderT TypeEnv (Writer [InferenceError])) a)
    deriving (Functor, Applicative, Monad, MonadState GenState, MonadReader TypeEnv, MonadWriter [InferenceError])

data GenState = GenState
    { gsCounter :: Int
    , gsTypeMap :: Map.Map Expr Type
    }
    deriving (Show)

reportError :: InferenceError -> GenM ()
reportError err = tell [err]

reportErrors :: [InferenceError] -> GenM ()
reportErrors = tell

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
    , tcPurpose :: UnificationPurpose
    }
    deriving (Show)

freshTyVar :: Kind -> GenM TyVar
freshTyVar k = do
    n <- gets gsCounter
    modify $ \s -> s{gsCounter = n + 1}
    return $ TypeVar ("t" ++ show n) k

freshSkolemVar :: String -> Kind -> GenM SkolemVar
freshSkolemVar name k = do
    n <- gets gsCounter
    modify $ \s -> s{gsCounter = n + 1}
    return $ SkolemVar("s" ++ show n) k n name Rigid

recordType :: Expr -> Type -> GenM ()
recordType expr ty = modify $ \s -> s{gsTypeMap = Map.insert expr ty (gsTypeMap s)}

generateConstraints :: Expr -> GenM (Maybe Type, ConstraintSet)
generateConstraints expr = case expr of
    ExprNum _ _ -> do
        let ty = intType
        recordType expr ty
        pure (Just ty, ConstraintSet [] [])
    ExprStr _ _ -> do
        let ty = strType
        recordType expr ty
        pure (Just ty, ConstraintSet [] [])
    ExprBool _ _ -> do
        let ty = boolType
        recordType expr ty
        pure (Just ty, ConstraintSet [] [])
    ExprVar name _ -> do
        env <- ask
        case Map.lookup name env of
            Just (Forall tvs cs t) -> do
                freshVars <- mapM (freshTyVar . tvKind) tvs
                let subst = Map.fromList (zip tvs (map TVar freshVars))
                let instType = applyTySubst subst t
                let instConstraints = map (applyConstraintSubst subst) cs
                recordType expr instType
                return (Just instType, ConstraintSet [] instConstraints)
            Nothing -> do
                reportError (UnboundVariable expr name)
                errorVar <- freshTyVar KindStar
                let errorType = TVar errorVar
                recordType expr errorType
                return (Just errorType, ConstraintSet [] [])
    ExprApp f a -> do
        (Just tf, cf) <- generateConstraints f
        (Just ta, ca) <- generateConstraints a
        retVar <- freshTyVar KindStar
        let retType = TVar retVar
        let funConstraint = TypeConstraint expr (TArrow ta retType) tf UnifyFunctionApplication
        let combinedConstraints =
                ConstraintSet
                    (funConstraint : csTypeConstraints cf ++ csTypeConstraints ca)
                    (csClassConstraints cf ++ csClassConstraints ca)
        recordType expr retType
        return (Just retType, combinedConstraints)
    ExprLambda paramNames body _ -> do
        paramVars <- mapM (const $ freshTyVar KindStar) paramNames
        let paramTypes = map TVar paramVars
        let paramBindings = Map.fromList (zip paramNames (map (cleanQualified . TVar) paramVars))
        let extendEnv = Map.union paramBindings

        (Just bodyType, bodyConstraints) <- local extendEnv (generateConstraints body)
        let funcType = foldr TArrow bodyType paramTypes
        recordType expr funcType
        return (Just funcType, bodyConstraints)
    ExprLet name value body _ -> do
        (Just valueType, valueConstraints) <- generateConstraints value
        let extendEnv = Map.insert name (cleanQualified valueType)
        (Just bodyType, bodyConstraints) <- local extendEnv (generateConstraints body)
        let combinedConstraints =
                ConstraintSet
                    (csTypeConstraints valueConstraints ++ csTypeConstraints bodyConstraints)
                    (csClassConstraints valueConstraints ++ csClassConstraints bodyConstraints)
        recordType expr bodyType
        return (Just bodyType, combinedConstraints)
    ExprBindingDef name bindType body _ _ -> do
        let Forall tyVars annCs annType = bindType
        skVars <- mapM (\(TypeVar tyName kind) -> freshSkolemVar tyName kind) tyVars
        let skSubst = Map.fromList (zip tyVars (map TSkolem skVars))
        let skType = applyTySubst skSubst annType
        let skAnnCs = map (applyConstraintSubst skSubst) annCs
        instVars <- mapM (freshTyVar . tvKind) tyVars
        let instSubst = Map.fromList (zip tyVars (map TVar instVars))
        let instType = applyTySubst instSubst annType
        let instCs = map (applyConstraintSubst instSubst) annCs
        let sigQual = Forall [] instCs instType
        (Just bodyType, bodyCs) <- local (Map.insert name sigQual) (generateConstraints body)
        let sigConstraint = TypeConstraint expr skType bodyType UnifyFunctionBody
        let combinedConstraints =
                ConstraintSet
                    (sigConstraint : csTypeConstraints bodyCs)
                    (skAnnCs ++ csClassConstraints bodyCs)
        recordType expr bodyType
        return (Just bodyType, combinedConstraints)
    ExprDerivedPatternMatch _armTypes arms -> do
        mappedArms <- mapM generateConstraints arms
        let (armExprTypes, armConstraintsList) = unzip mappedArms
        let combinedBodyConstraints = mconcat armConstraintsList
 
        let Just exprType = hardHead armExprTypes
        let armTypeConstraints = map
                ( \(Just armType, ExprPatternMatchArm _ _ armBody _) ->
                    TypeConstraint armBody exprType armType UnifyPatternMatchArms
                )
                (zip armExprTypes arms)
        let combinedTypeConstraints = ConstraintSet
                (armTypeConstraints ++ csTypeConstraints combinedBodyConstraints)
                (csClassConstraints combinedBodyConstraints)

        recordType expr exprType
        return (Just exprType, combinedTypeConstraints)
    ExprPatternMatchArm patterns armTypes body _ -> do
        currentEnv <- ask
        (patternEnv, patternErrors) <- generatePatternBindings expr currentEnv patterns armTypes
        reportErrors patternErrors

        let extendWithPatterns = Map.union patternEnv
        (Just bodyType, bodyConstraints) <- local extendWithPatterns (generateConstraints body)
        let (providedTypes, missingBodyTypes) = splitAt (length patterns) armTypes

        returnTypVar <- freshTyVar KindStar
        let additionalConstraints =
                if null missingBodyTypes
                    then []
                    else do
                        let Forall _ _ missingBodyType = vectorizeAllQualified missingBodyTypes
                        let expectedType = TArrow missingBodyType (TVar returnTypVar)
                        [TypeConstraint body expectedType bodyType UnifyPatternMatchArmBody]

        let finalConstraints =
                ConstraintSet
                    (csTypeConstraints bodyConstraints ++ additionalConstraints)
                    (csClassConstraints bodyConstraints)

        let Forall _ _ providedTyp = vectorizeAllQualified providedTypes
        let exprType = vectorize providedTyp bodyType

        return (Just exprType, finalConstraints)
    _ -> do
        let children = exprChildren expr
        results <- mapM generateConstraints children
        let combinedConstraints = mconcat (map snd results)
        return (Nothing, combinedConstraints)

generatePatternBinding :: Expr -> TypeEnv -> Pattern -> QualifiedType -> GenM (TypeEnv, [InferenceError])
generatePatternBinding _expr _env (PVar name) armType = do
    return (Map.singleton name armType, [])
generatePatternBinding expr env (PAs name pat) armType = do
    let asBinding = Map.singleton name armType
    (nestedBinding, errs) <- generatePatternBinding expr env pat armType
    return (Map.union asBinding nestedBinding, errs)
generatePatternBinding expr env (PConstructor name patterns) _armType = do
    currentEnv <- ask
    case Map.lookup name currentEnv of
        Just (Forall tvs cs t) -> do
            freshVars <- mapM (freshTyVar . tvKind) tvs
            let subst = Map.fromList (zip tvs (map TVar freshVars))
            let instType = applyTySubst subst t
            let instConstraints = map (applyConstraintSubst subst) cs

            let argTypes = extractArgTypes instType (length patterns)
            let qualifiedArgTypes = map (Forall [] instConstraints) argTypes

            if length argTypes /= length patterns
                then do
                    let err = PatternArityMismatch expr (length patterns) (length argTypes)
                    reportError err
                    return (Map.empty, [err])
                else do
                    (bindings, errs) <- generatePatternBindings expr env patterns qualifiedArgTypes
                    return (bindings, errs)
        Nothing -> do
            let err = UnknownTypeConstructor expr name
            reportError err
            return (Map.empty, [err])
generatePatternBinding _expr _env PWildcard _ = return (Map.empty, [])
generatePatternBinding _expr _env PLit{} _ = return (Map.empty, [])
generatePatternBinding expr _env p _ = error $ "Unsupported pattern: " ++ show p ++ " in expression: " ++ show expr

generatePatternBindings :: Expr -> TypeEnv -> [Pattern] -> [QualifiedType] -> GenM (TypeEnv, [InferenceError])
generatePatternBindings expr env patterns armTypes = do
    let zipped = zip patterns armTypes
    results <- mapM (\(p, t) -> generatePatternBinding expr env p t) zipped
    let (bindings, errorLists) = unzip results
    let allErrors = concat errorLists
    pure (Map.unions (env : bindings), allErrors)

runGenM :: TypeEnv -> GenM a -> (a, GenState, [InferenceError])
runGenM env (GenM m) =
    let ((result, finalState), errors) = runWriter (runReaderT (runStateT m initialState) env)
    in (result, finalState, errors)
  where
    initialState = GenState 0 Map.empty

runGenMErrors :: TypeEnv -> GenM a -> [InferenceError]
runGenMErrors env genM =
    let (_, _, errors) = runGenM env genM
    in errors

isInferenceSuccess :: [InferenceError] -> Bool
isInferenceSuccess = null

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
noConstraints = ConstraintSet [] []

instance MonadFail GenM where
    fail msg = error $ "GenM failed: " ++ msg
