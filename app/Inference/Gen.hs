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
import Inference.Substitution (Substitutable (apply))
import Lexing.Position (Span (..))
import Project.Symbols (Symbol (..), SymbolKind (..))
import Syntax.Patterns (Pattern (..))
import Syntax.Tree (Expr (..), exprChildren)
import Typing.Types (Constraint (..), Kind (..), QualifiedType (..), Rigidity (..), SkolemVar (..), TyVar (..), Type (..), arrayType, boolType, cleanQualified, intType, strType, vectorize, vectorizeAll)
import Utils.Lists (hardHead)

newtype GenM a = GenM (StateT GenState (ReaderT TypeEnv (Writer [InferenceError])) a)
    deriving (Functor, Applicative, Monad, MonadState GenState, MonadReader TypeEnv, MonadWriter [InferenceError])

data GenState = GenState
    { gsCounter :: Int
    , gsTypeMap :: Map.Map Expr Type
    , gsSkolemEnv :: Map.Map String SkolemVar
    , gsCurrentModule :: String
    }
    deriving (Show)

reportError :: InferenceError -> GenM ()
reportError err = tell [err]

reportErrors :: [InferenceError] -> GenM ()
reportErrors = tell

data ClassConstraintWithSource = ClassConstraintWithSource
    { ccsConstraint :: Constraint
    , ccsSourceExpr :: Expr
    }
    deriving (Show)

data ConstraintSet = ConstraintSet
    { csTypeConstraints :: [TypeConstraint]
    , csClassConstraints :: [ClassConstraintWithSource]
    , csDeclaredConstraints :: [Constraint]
    }
    deriving (Show)

instance Semigroup ConstraintSet where
    (ConstraintSet ts1 cs1 dc1) <> (ConstraintSet ts2 cs2 dc2) =
        ConstraintSet (ts1 ++ ts2) (cs1 ++ cs2) (dc1 ++ dc2)

instance Monoid ConstraintSet where
    mempty = ConstraintSet [] [] []

emptyConstraints :: ConstraintSet
emptyConstraints = mempty

typeConstraints :: [TypeConstraint] -> ConstraintSet
typeConstraints tcs = ConstraintSet tcs [] []

classConstraints :: [ClassConstraintWithSource] -> ConstraintSet
classConstraints ccs = ConstraintSet [] ccs []

declaredConstraints :: [Constraint] -> ConstraintSet
declaredConstraints = ConstraintSet [] []

combineConstraints :: [ConstraintSet] -> ConstraintSet
combineConstraints = mconcat

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
    return $ SkolemVar ("s" ++ show n) k n name Rigid

recordType :: Expr -> Type -> GenM ()
recordType expr ty = modify $ \s -> s{gsTypeMap = Map.insert expr ty (gsTypeMap s)}

createLocalSymbol :: String -> GenM Symbol
createLocalSymbol name = do
    currentModule <- gets gsCurrentModule
    return
        $ ResolvedSymbol
            { resolvedSymbolName = name
            , resolvedSymbolKind = LocalVariableSymbol
            , resolvedSymbolModule = currentModule
            , resolvedSymbolSpan = Span 0 0
            }

findSymbolByName :: String -> TypeEnv -> Maybe (Symbol, QualifiedType)
findSymbolByName name env =
    let matches = [(sym, qual) | (sym, qual) <- Map.toList env, resolvedSymbolName sym == name]
    in case matches of
        (sym, qual) : _ -> Just (sym, qual)
        [] -> Nothing

generateConstraints :: Expr -> GenM (Maybe Type, ConstraintSet)
generateConstraints expr = case expr of
    ExprNum _ _ -> do
        let ty = intType
        recordType expr ty
        pure (Just ty, emptyConstraints)
    ExprStr _ _ -> do
        let ty = strType
        recordType expr ty
        pure (Just ty, emptyConstraints)
    ExprBool _ _ -> do
        let ty = boolType
        recordType expr ty
        pure (Just ty, emptyConstraints)
    ExprUVar name varSpan -> do
        env <- ask
        case findSymbolByName name env of
            Just (_, Forall tvs cs t) -> do
                freshVars <- mapM (freshTyVar . tvKind) tvs
                let subst = Map.fromList (zip tvs (map TVar freshVars))
                let instType = apply subst t
                let instConstraints = map (apply subst) cs
                let instConstraintsWithSource = map (`ClassConstraintWithSource` expr) instConstraints
                recordType expr instType
                return (Just instType, classConstraints instConstraintsWithSource)
            Nothing -> do
                reportError (UnboundVariable (ExprUVar name varSpan) name)
                errorVar <- freshTyVar KindStar
                let errorType = TVar errorVar
                recordType expr errorType
                return (Just errorType, emptyConstraints)
    ExprVar symbol _ -> do
        env <- ask
        case Map.lookup symbol env of
            Just (Forall tvs cs t) -> do
                freshVars <- mapM (freshTyVar . tvKind) tvs
                let subst = Map.fromList (zip tvs (map TVar freshVars))
                let instType = apply subst t
                let instConstraints = map (apply subst) cs
                let instConstraintsWithSource = map (`ClassConstraintWithSource` expr) instConstraints
                recordType expr instType
                return (Just instType, classConstraints instConstraintsWithSource)
            Nothing -> do
                reportError (UnboundVariable expr (resolvedSymbolName symbol))
                errorVar <- freshTyVar KindStar
                let errorType = TVar errorVar
                recordType expr errorType
                return (Just errorType, emptyConstraints)
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
                    (csDeclaredConstraints cf ++ csDeclaredConstraints ca)
        recordType expr retType
        return (Just retType, combinedConstraints)
    ExprLambda paramNames body _ -> do
        paramVars <- mapM (const $ freshTyVar KindStar) paramNames
        let paramTypes = map TVar paramVars

        paramSymbols <- mapM createLocalSymbol paramNames
        let paramBindings = Map.fromList (zip paramSymbols (map cleanQualified paramTypes))
        let extendEnv = Map.union paramBindings

        (Just bodyType, bodyConstraints) <- local extendEnv (generateConstraints body)
        let funcType = foldr TArrow bodyType paramTypes
        recordType expr funcType
        return (Just funcType, bodyConstraints)
    ExprLet name value body _ -> do
        (Just valueType, valueConstraints) <- generateConstraints value
        letSymbol <- createLocalSymbol name
        let extendEnv = Map.insert letSymbol (cleanQualified valueType)
        (Just bodyType, bodyConstraints) <- local extendEnv (generateConstraints body)
        let combinedConstraints =
                ConstraintSet
                    (csTypeConstraints valueConstraints ++ csTypeConstraints bodyConstraints)
                    (csClassConstraints valueConstraints ++ csClassConstraints bodyConstraints)
                    (csDeclaredConstraints valueConstraints ++ csDeclaredConstraints bodyConstraints)
        recordType expr bodyType
        return (Just bodyType, combinedConstraints)
    ExprBindingDef _name bindType body _ _ -> do
        let Forall tyVars annCs annType = bindType
        skVars <- mapM (\(TypeVar tyName kind) -> freshSkolemVar tyName kind) tyVars
        let skSubst = Map.fromList (zip tyVars (map TSkolem skVars))
        let skType = apply skSubst annType
        let skAnnCs = map (apply skSubst) annCs
        (maybeBodyType, bodyCs) <- generateConstraints body

        case maybeBodyType of
            Just bodyType -> do
                let sigConstraint = TypeConstraint expr skType bodyType UnifyFunctionBody
                let combinedConstraints =
                        ConstraintSet
                            (sigConstraint : csTypeConstraints bodyCs)
                            (csClassConstraints bodyCs)
                            skAnnCs
                recordType expr bodyType
                return (Just bodyType, combinedConstraints)
            Nothing -> do
                errorVar <- freshTyVar KindStar
                let errorType = TVar errorVar
                recordType expr errorType
                let combinedConstraints =
                        ConstraintSet
                            (csTypeConstraints bodyCs)
                            (csClassConstraints bodyCs)
                            skAnnCs
                return (Just errorType, combinedConstraints)
    ExprDerivedPatternMatch arms -> do
        mappedArms <- mapM generateConstraints arms
        let (armExprTypes, armConstraintsList) = unzip mappedArms
        let combinedBodyConstraints = mconcat armConstraintsList

        let Just exprType = hardHead armExprTypes
        let armTypeConstraints =
                zipWith
                    ( curry
                        ( \(Just armType, ExprPatternMatchArm _ armBody _) ->
                            TypeConstraint armBody exprType armType UnifyPatternMatchArms
                        )
                    )
                    armExprTypes
                    arms
        let combinedTypeConstraints =
                ConstraintSet
                    (armTypeConstraints ++ csTypeConstraints combinedBodyConstraints)
                    (csClassConstraints combinedBodyConstraints)
                    (csDeclaredConstraints combinedBodyConstraints)

        recordType expr exprType
        return (Just exprType, combinedTypeConstraints)
    ExprPatternMatchArm patterns body _ -> do
        armTyVars <- mapM (const $ freshTyVar KindStar) patterns
        let armTypes = map TVar armTyVars
        let qualifiedArmTypes = map cleanQualified armTypes

        currentEnv <- ask
        (patternEnv, patternErrors) <- generatePatternBindings expr currentEnv patterns qualifiedArmTypes
        reportErrors patternErrors

        let extendWithPatterns = Map.union patternEnv
        (maybeBodyType, bodyConstraints) <- local extendWithPatterns (generateConstraints body)
        case maybeBodyType of
            Just bodyType -> do
                let (providedTypes, missingBodyTypes) = splitAt (length patterns) armTypes

                returnTypVar <- freshTyVar KindStar
                let additionalConstraints =
                        if null missingBodyTypes
                            then []
                            else do
                                let missingBodyType = vectorizeAll missingBodyTypes
                                let expectedType = TArrow missingBodyType (TVar returnTypVar)
                                [TypeConstraint body expectedType bodyType UnifyPatternMatchArmBody]

                let finalConstraints =
                        ConstraintSet
                            (csTypeConstraints bodyConstraints ++ additionalConstraints)
                            (csClassConstraints bodyConstraints)
                            (csDeclaredConstraints bodyConstraints)

                let providedTyp = vectorizeAll providedTypes
                let exprType = vectorize providedTyp bodyType

                return (Just exprType, finalConstraints)
            Nothing -> do
                errorVar <- freshTyVar KindStar
                let errorType = TVar errorVar
                recordType expr errorType
                return (Just errorType, bodyConstraints)
    ExprArray elements _ -> do
        if null elements
            then do
                elemVar <- freshTyVar KindStar
                let elemType = TVar elemVar
                let arrType = arrayType elemType
                recordType expr arrType
                return (Just arrType, emptyConstraints)
            else do
                results <- mapM generateConstraints elements
                let (maybeElemTypes, elemConstraints) = unzip results

                let (Just firstElemType : _) = maybeElemTypes

                let elemTypeConstraints =
                        zipWith
                            ( \(Just elemType) elemExpr ->
                                TypeConstraint elemExpr firstElemType elemType UnifyPatternMatchArms
                            )
                            maybeElemTypes
                            elements

                let combinedConstraints =
                        ConstraintSet
                            (elemTypeConstraints ++ concatMap csTypeConstraints elemConstraints)
                            (concatMap csClassConstraints elemConstraints)
                            (concatMap csDeclaredConstraints elemConstraints)

                let arrType = arrayType firstElemType
                recordType expr arrType
                return (Just arrType, combinedConstraints)
    _ -> do
        let children = exprChildren expr
        results <- mapM generateConstraints children
        let combinedConstraints = mconcat (map snd results)
        return (Nothing, combinedConstraints)

generatePatternBinding :: Expr -> TypeEnv -> Pattern -> QualifiedType -> GenM (TypeEnv, [InferenceError])
generatePatternBinding _expr _env (PVar name) armType = do
    symbol <- createLocalSymbol name
    return (Map.singleton symbol armType, [])
generatePatternBinding expr env (PAs name pat) armType = do
    asSymbol <- createLocalSymbol name
    let asBinding = Map.singleton asSymbol armType
    (nestedBinding, errs) <- generatePatternBinding expr env pat armType
    return (Map.union asBinding nestedBinding, errs)
generatePatternBinding expr env (PConstructor name patterns) _armType = do
    currentEnv <- ask
    let constructorLookup = Map.toList currentEnv
    let maybeConstructor = lookup name [(resolvedSymbolName sym, qual) | (sym, qual) <- constructorLookup]
    case maybeConstructor of
        Just (Forall tvs cs t) -> do
            freshVars <- mapM (freshTyVar . tvKind) tvs
            let subst = Map.fromList (zip tvs (map TVar freshVars))
            let instType = apply subst t
            let instConstraints = map (apply subst) cs

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
    results <- mapM (uncurry (generatePatternBinding expr env)) zipped
    let (bindings, errorLists) = unzip results
    let allErrors = concat errorLists
    pure (Map.unions (env : bindings), allErrors)

runGenM :: String -> TypeEnv -> GenM a -> (a, GenState, [InferenceError])
runGenM currentModule env (GenM m) =
    let ((result, finalState), errors) = runWriter (runReaderT (runStateT m (initialState currentModule)) env)
    in (result, finalState, errors)
  where
    initialState = GenState 0 Map.empty Map.empty

runGenMErrors :: String -> TypeEnv -> GenM a -> [InferenceError]
runGenMErrors currentModule env genM =
    let (_, _, errors) = runGenM currentModule env genM
    in errors

extractArgTypes :: Type -> Int -> [Type]
extractArgTypes _ty 0 = []
extractArgTypes (TArrow arg rest) n = arg : extractArgTypes rest (n - 1)
extractArgTypes _ _ = error "Constructor type doesn't match pattern arity"

instance MonadFail GenM where
    fail msg = error $ "GenM failed: " ++ msg
