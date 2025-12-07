{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Inference.Gen (
    generateConstraints,
    generateBindingConstraints,
    generateInstanceConstraints,
    MetalGenM,
    MetalGenState (..),
    runMetalGenM,
    MetalConstraintSet (..),
    MetalTypeConstraint (..),
    MetalClassConstraint (..),
    emptyConstraints,
    typeConstraints,
    classConstraints,
    declaredConstraints,
    MetalTypeEnv,
) where

import Control.Monad (forM, when, zipWithM)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as Map
import Inference.Core (UnificationPurpose (..))
import Inference.Errors (InferenceError (..))
import Inference.Naming (nameSkolemPrefix, nameTmpPrefix)
import Inference.Substitution (Substitutable (apply))
import Lexing.Position (Span (..))
import Metal.Expr
import Project.Name (Name (..), nameToString)
import Syntax.Patterns (Pattern (..), ResolvedPattern)
import qualified Syntax.Tree
import Typing.Types (
    Constraint (..),
    Kind (..),
    QualifiedType (..),
    Rigidity (..),
    SkolemVar (..),
    TyConstructor (..),
    TyPrimitive (..),
    TyUnique (..),
    TyVar (..),
    Type (..),
    arrayType,
    boolType,
    cleanQualified,
    tupleType,
    unitType,
 )
import Utils.Lists (hardHead, hardTail)

type MetalTypeEnv = Map.Map Name QualifiedType

newtype MetalGenM a = MetalGenM (StateT MetalGenState (ReaderT MetalTypeEnv (Writer [InferenceError])) a)
    deriving (Functor, Applicative, Monad, MonadState MetalGenState, MonadReader MetalTypeEnv, MonadWriter [InferenceError])

data MetalGenState = MetalGenState
    { mgsCounter :: Int
    , mgsSkolemEnv :: Map.Map String SkolemVar
    , mgsCurrentModule :: String
    , mgsCurrentPackage :: String
    }
    deriving (Show)

data MetalTypeConstraint = MetalTypeConstraint
    { mtcSpan :: Span
    , mtcExpected :: Type
    , mtcActual :: Type
    , mtcPurpose :: UnificationPurpose
    }
    deriving (Show)

data MetalClassConstraint = MetalClassConstraint
    { mccConstraint :: Constraint
    , mccSpan :: Span
    }
    deriving (Show)

data MetalConstraintSet = MetalConstraintSet
    { mcsTypeConstraints :: [MetalTypeConstraint]
    , mcsClassConstraints :: [MetalClassConstraint]
    , mcsDeclaredConstraints :: [Constraint]
    }
    deriving (Show)

instance Semigroup MetalConstraintSet where
    (MetalConstraintSet ts1 cs1 dc1) <> (MetalConstraintSet ts2 cs2 dc2) =
        MetalConstraintSet (ts1 ++ ts2) (cs1 ++ cs2) (dc1 ++ dc2)

instance Monoid MetalConstraintSet where
    mempty = MetalConstraintSet [] [] []

emptyConstraints :: MetalConstraintSet
emptyConstraints = mempty

typeConstraints :: [MetalTypeConstraint] -> MetalConstraintSet
typeConstraints tcs = MetalConstraintSet tcs [] []

classConstraints :: [MetalClassConstraint] -> MetalConstraintSet
classConstraints ccs = MetalConstraintSet [] ccs []

declaredConstraints :: [Constraint] -> MetalConstraintSet
declaredConstraints = MetalConstraintSet [] []

runMetalGenM ::
    String ->
    String ->
    MetalTypeEnv ->
    MetalGenM a ->
    (a, MetalGenState, [InferenceError])
runMetalGenM pkg modName env (MetalGenM m) =
    let initialState = MetalGenState 0 Map.empty modName pkg
        ((result, finalState), errors) = runWriter (runReaderT (runStateT m initialState) env)
    in (result, finalState, errors)

reportError :: InferenceError -> MetalGenM ()
reportError = tell . (: [])

freshTyVar :: Kind -> MetalGenM TyVar
freshTyVar k = do
    n <- gets mgsCounter
    modify $ \s -> s{mgsCounter = n + 1}
    pure $ TypeVar (nameTmpPrefix ++ show n) k

freshSkolemVar :: String -> Kind -> MetalGenM SkolemVar
freshSkolemVar name k = do
    n <- gets mgsCounter
    modify $ \s -> s{mgsCounter = n + 1}
    pure $ SkolemVar (nameSkolemPrefix ++ show n) k n name Rigid

slotType :: TypeSlot -> Type
slotType (Known t) = t
slotType (Hole tv) = TVar tv

generateBindingConstraints ::
    Name ->
    InferenceExpr ->
    [Type] ->
    Type ->
    [TyVar] ->
    [Constraint] ->
    MetalGenM (TypeSlot, MetalConstraintSet)
generateBindingConstraints _name body paramTypes returnType tyVars annConstraints = do
    skVars <- mapM (\(TypeVar tyName kind) -> freshSkolemVar tyName kind) tyVars
    let skSubst = Map.fromList (zip tyVars (map TSkolem skVars))

    let skParamTypes = map (apply skSubst) paramTypes
    let skReturnType = apply skSubst returnType
    let skAnnConstraints = map (apply skSubst) annConstraints

    let expectedType = foldr TArrow skReturnType skParamTypes

    (bodySlot, bodyCs) <- generateConstraints body

    let sigConstraint =
            MetalTypeConstraint
                { mtcSpan = exprSpan body
                , mtcExpected = expectedType
                , mtcActual = slotType bodySlot
                , mtcPurpose = UnifyFunctionBody
                }

    let combinedConstraints =
            MetalConstraintSet
                { mcsTypeConstraints = sigConstraint : mcsTypeConstraints bodyCs
                , mcsClassConstraints = mcsClassConstraints bodyCs
                , mcsDeclaredConstraints = skAnnConstraints
                }

    pure (bodySlot, combinedConstraints)

generateInstanceConstraints ::
    Name ->
    InferenceExpr ->
    [Type] ->
    Type ->
    MetalGenM (TypeSlot, MetalConstraintSet)
generateInstanceConstraints _name body paramTypes returnType = do
    let expectedType = foldr TArrow returnType paramTypes

    (bodySlot, bodyCs) <- generateConstraints body

    let sigConstraint =
            MetalTypeConstraint
                { mtcSpan = exprSpan body
                , mtcExpected = expectedType
                , mtcActual = slotType bodySlot
                , mtcPurpose = UnifyFunctionBody
                }

    let combinedConstraints =
            MetalConstraintSet
                { mcsTypeConstraints = sigConstraint : mcsTypeConstraints bodyCs
                , mcsClassConstraints = mcsClassConstraints bodyCs
                , mcsDeclaredConstraints = []
                }

    pure (bodySlot, combinedConstraints)

generateConstraints :: InferenceExpr -> MetalGenM (TypeSlot, MetalConstraintSet)
generateConstraints expr = case expr of
    MVar name slot span' -> do
        env <- ask
        case Map.lookup name env of
            Just (Forall tvs cs t) -> do
                freshVars <- mapM (freshTyVar . tvKind) tvs
                let subst = Map.fromList (zip tvs (map TVar freshVars))
                let instType = apply subst t
                let instConstraints = map (apply subst) cs
                let instClassConstraints = map (`MetalClassConstraint` span') instConstraints

                let slotConstraint =
                        MetalTypeConstraint
                            { mtcSpan = span'
                            , mtcExpected = instType
                            , mtcActual = slotType slot
                            , mtcPurpose = UnifyFunctionApplication
                            }

                pure (slot, typeConstraints [slotConstraint] <> classConstraints instClassConstraints)
            Nothing -> do
                reportError (UnboundVariable (dummyExpr span') (nameToString name))
                pure (slot, emptyConstraints)
    MLit lit _ -> do
        let ty = literalType lit
        pure (Known ty, emptyConstraints)
    MCall func args resultSlot span' -> do
        (funcSlot, funcCs) <- generateConstraints func
        argResults <- mapM generateConstraints args
        let (argSlots, argCsList) = unzip argResults

        let expectedFuncType = foldr (TArrow . slotType) (slotType resultSlot) argSlots

        let callConstraint =
                MetalTypeConstraint
                    { mtcSpan = span'
                    , mtcExpected = expectedFuncType
                    , mtcActual = slotType funcSlot
                    , mtcPurpose = UnifyFunctionApplication
                    }

        pure (resultSlot, mconcat (funcCs : argCsList) <> typeConstraints [callConstraint])
    MTypeApp inner _typeArgs slot span' -> do
        (innerSlot, innerCs) <- generateConstraints inner

        let slotConstraint =
                MetalTypeConstraint
                    { mtcSpan = span'
                    , mtcExpected = slotType innerSlot
                    , mtcActual = slotType slot
                    , mtcPurpose = UnifyFunctionApplication
                    }

        pure (slot, innerCs <> typeConstraints [slotConstraint])
    MLambda params body funcSlot span' -> do
        let paramBindings = Map.fromList [(name, cleanQualified (slotType slot)) | (name, slot) <- params]

        (bodySlot, bodyCs) <- local (Map.union paramBindings) $ generateConstraints body

        let paramTypes = map (slotType . snd) params
        let expectedFuncType = foldr TArrow (slotType bodySlot) paramTypes

        let funcConstraint =
                MetalTypeConstraint
                    { mtcSpan = span'
                    , mtcExpected = expectedFuncType
                    , mtcActual = slotType funcSlot
                    , mtcPurpose = UnifyFunctionBody
                    }

        pure (funcSlot, bodyCs <> typeConstraints [funcConstraint])
    MClosure _name _captured slot _span -> do
        pure (slot, emptyConstraints)
    MLet name value body resultSlot span' -> do
        (valueSlot, valueCs) <- generateConstraints value

        let letBinding = Map.singleton name (cleanQualified (slotType valueSlot))
        (bodySlot, bodyCs) <- local (Map.union letBinding) $ generateConstraints body

        let resultConstraint =
                MetalTypeConstraint
                    { mtcSpan = span'
                    , mtcExpected = slotType bodySlot
                    , mtcActual = slotType resultSlot
                    , mtcPurpose = UnifyFunctionApplication
                    }

        pure (resultSlot, valueCs <> bodyCs <> typeConstraints [resultConstraint])
    MConstruct ctorName _tag args slot span' -> do
        env <- ask
        case Map.lookup ctorName env of
            Just (Forall tvs cs t) -> do
                freshVars <- mapM (freshTyVar . tvKind) tvs
                let subst = Map.fromList (zip tvs (map TVar freshVars))
                let instType = apply subst t
                let instConstraints = map (apply subst) cs
                let instClassConstraints = map (`MetalClassConstraint` span') instConstraints

                argResults <- mapM generateConstraints args
                let (argSlots, argCsList) = unzip argResults

                let (expectedArgTypes, expectedResultType) = splitFunctionType (length args) instType

                let argConstraints =
                        zipWith
                            ( \argSlot expectedTy ->
                                MetalTypeConstraint
                                    { mtcSpan = span'
                                    , mtcExpected = expectedTy
                                    , mtcActual = slotType argSlot
                                    , mtcPurpose = UnifyFunctionApplication
                                    }
                            )
                            argSlots
                            expectedArgTypes

                let resultConstraint =
                        MetalTypeConstraint
                            { mtcSpan = span'
                            , mtcExpected = expectedResultType
                            , mtcActual = slotType slot
                            , mtcPurpose = UnifyFunctionApplication
                            }

                pure
                    ( slot
                    , mconcat argCsList
                        <> typeConstraints (resultConstraint : argConstraints)
                        <> classConstraints instClassConstraints
                    )
            Nothing -> do
                argResults <- mapM generateConstraints args
                let argCsList = map snd argResults
                pure (slot, mconcat argCsList)
    MArrayLit elements slot span' -> do
        if null elements
            then do
                elemVar <- freshTyVar KindStar
                let arrType = arrayType (TVar elemVar)
                let slotConstraint =
                        MetalTypeConstraint
                            { mtcSpan = span'
                            , mtcExpected = arrType
                            , mtcActual = slotType slot
                            , mtcPurpose = UnifyFunctionApplication
                            }
                pure (slot, typeConstraints [slotConstraint])
            else do
                results <- mapM generateConstraints elements
                let (elemSlots, elemCsList) = unzip results
                let firstElemType = slotType (hardHead elemSlots)

                let elemConstraints =
                        [ MetalTypeConstraint
                            { mtcSpan = exprSpan el
                            , mtcExpected = firstElemType
                            , mtcActual = slotType elemSlot
                            , mtcPurpose = UnifyPatternMatchArms
                            }
                        | (el, elemSlot) <- zip (hardTail elements) (hardTail elemSlots)
                        ]

                let arrType = arrayType firstElemType
                let slotConstraint =
                        MetalTypeConstraint
                            { mtcSpan = span'
                            , mtcExpected = arrType
                            , mtcActual = slotType slot
                            , mtcPurpose = UnifyFunctionApplication
                            }

                pure (slot, mconcat elemCsList <> typeConstraints (slotConstraint : elemConstraints))
    MTuple elements slot span' -> do
        if null elements
            then do
                let slotConstraint =
                        MetalTypeConstraint
                            { mtcSpan = span'
                            , mtcExpected = unitType
                            , mtcActual = slotType slot
                            , mtcPurpose = UnifyFunctionApplication
                            }
                pure (slot, typeConstraints [slotConstraint])
            else do
                results <- mapM generateConstraints elements
                let (elemSlots, elemCsList) = unzip results
                let elemTypes = map slotType elemSlots

                let tupType = tupleType elemTypes
                let slotConstraint =
                        MetalTypeConstraint
                            { mtcSpan = span'
                            , mtcExpected = tupType
                            , mtcActual = slotType slot
                            , mtcPurpose = UnifyFunctionApplication
                            }

                pure (slot, mconcat elemCsList <> typeConstraints [slotConstraint])
    MIf cond thenBranch elseBranch slot span' -> do
        (condSlot, condCs) <- generateConstraints cond
        (thenSlot, thenCs) <- generateConstraints thenBranch
        (elseSlot, elseCs) <- generateConstraints elseBranch

        let condConstraint =
                MetalTypeConstraint
                    { mtcSpan = exprSpan cond
                    , mtcExpected = boolType
                    , mtcActual = slotType condSlot
                    , mtcPurpose = UnifyIfCondition
                    }

        let branchConstraint =
                MetalTypeConstraint
                    { mtcSpan = span'
                    , mtcExpected = slotType thenSlot
                    , mtcActual = slotType elseSlot
                    , mtcPurpose = UnifyIfElseBranches
                    }

        let resultConstraint =
                MetalTypeConstraint
                    { mtcSpan = span'
                    , mtcExpected = slotType thenSlot
                    , mtcActual = slotType slot
                    , mtcPurpose = UnifyFunctionApplication
                    }

        pure
            ( slot
            , condCs <> thenCs <> elseCs <> typeConstraints [condConstraint, branchConstraint, resultConstraint]
            )
    MCase scrutinees arms mDefault slot span' -> do
        scrutineeResults <- mapM generateConstraints scrutinees
        let (scrutineeSlots, scrutineeCsList) = unzip scrutineeResults
        let scrutineeTypes = map slotType scrutineeSlots

        armResults <- forM arms $ \(MCaseArm patterns armBody) -> do
            patternBindings <- generatePatternBindings span' patterns scrutineeTypes
            local (Map.union patternBindings) $ generateConstraints armBody

        let (armSlots, armCsList) = unzip armResults

        let firstArmType = case armSlots of
                (s : _) -> slotType s
                [] -> slotType slot

        let armTypeConstraints =
                [ MetalTypeConstraint
                    { mtcSpan = span'
                    , mtcExpected = firstArmType
                    , mtcActual = slotType armSlot
                    , mtcPurpose = UnifyPatternMatchArms
                    }
                | armSlot <- drop 1 armSlots
                ]

        (defaultCs, defaultConstraints) <- case mDefault of
            Just defaultExpr -> do
                (defaultSlot, defCs) <- generateConstraints defaultExpr
                let defConstraint =
                        MetalTypeConstraint
                            { mtcSpan = exprSpan defaultExpr
                            , mtcExpected = firstArmType
                            , mtcActual = slotType defaultSlot
                            , mtcPurpose = UnifyPatternMatchArms
                            }
                pure (defCs, [defConstraint])
            Nothing -> pure (emptyConstraints, [])

        let resultConstraint =
                MetalTypeConstraint
                    { mtcSpan = span'
                    , mtcExpected = firstArmType
                    , mtcActual = slotType slot
                    , mtcPurpose = UnifyFunctionApplication
                    }

        pure
            ( slot
            , mconcat scrutineeCsList
                <> mconcat armCsList
                <> defaultCs
                <> typeConstraints (resultConstraint : armTypeConstraints ++ defaultConstraints)
            )
    MFieldAccess inner _fieldIdx slot span' -> do
        (innerSlot, innerCs) <- generateConstraints inner

        let fieldConstraint =
                MetalTypeConstraint
                    { mtcSpan = span'
                    , mtcExpected = slotType innerSlot
                    , mtcActual = slotType slot
                    , mtcPurpose = UnifyFunctionApplication
                    }

        pure (slot, innerCs <> typeConstraints [fieldConstraint])
    MPanic _msg slot _span -> do
        pure (slot, emptyConstraints)

generatePatternBindings :: Span -> [ResolvedPattern] -> [Type] -> MetalGenM MetalTypeEnv
generatePatternBindings span' patterns types = do
    when (length patterns /= length types) $ reportError (PatternArityMismatch (dummyExpr span') (length patterns) (length types))

    bindings <- zipWithM (generatePatternBinding span') patterns types
    pure $ Map.unions bindings

generatePatternBinding :: Span -> ResolvedPattern -> Type -> MetalGenM MetalTypeEnv
generatePatternBinding _span (PVar name _) ty =
    pure $ Map.singleton name (cleanQualified ty)
generatePatternBinding span' (PAs name inner _) ty = do
    innerBindings <- generatePatternBinding span' inner ty
    pure $ Map.insert name (cleanQualified ty) innerBindings
generatePatternBinding span' (PConstructor ctorName innerPatterns _) _ = do
    env <- ask
    case Map.lookup ctorName env of
        Just (Forall tvs _cs t) -> do
            freshVars <- mapM (freshTyVar . tvKind) tvs
            let subst = Map.fromList (zip tvs (map TVar freshVars))
            let instType = apply subst t

            let (argTypes, _resultType) = splitFunctionType (length innerPatterns) instType

            innerBindings <- zipWithM (generatePatternBinding span') innerPatterns argTypes
            pure $ Map.unions innerBindings
        Nothing -> do
            reportError (UnknownTypeConstructor (dummyExpr span') (nameToString ctorName))
            pure Map.empty
generatePatternBinding span' (PTuple innerPatterns _) ty = do
    let elemTypes = extractTupleTypes ty
    when (length innerPatterns /= length elemTypes) $ reportError (PatternArityMismatch (dummyExpr span') (length innerPatterns) (length elemTypes))

    innerBindings <- zipWithM (generatePatternBinding span') innerPatterns elemTypes
    pure $ Map.unions innerBindings
generatePatternBinding span' (PArray innerPatterns _) ty = do
    let elemType = extractArrayElemType ty
    innerBindings <- mapM (\p -> generatePatternBinding span' p elemType) innerPatterns
    pure $ Map.unions innerBindings
generatePatternBinding _ PWildcard{} _ = pure Map.empty
generatePatternBinding _ PLit{} _ = pure Map.empty

extractTupleTypes :: Type -> [Type]
extractTupleTypes (TApp (TApp (TConstructor (TypeConstructor (TyPrim (TPTuple 2)) _)) t1) t2) = [t1, t2]
extractTupleTypes (TApp (TApp (TApp (TConstructor (TypeConstructor (TyPrim (TPTuple 3)) _)) t1) t2) t3) = [t1, t2, t3]
extractTupleTypes (TApp t1 t2) = extractTupleTypes t1 ++ [t2]
extractTupleTypes _ = []

extractArrayElemType :: Type -> Type
extractArrayElemType (TApp (TConstructor (TypeConstructor (TyPrim TPArray) _)) elemType) = elemType
extractArrayElemType _ = TVar (TypeVar "a" KindStar)

splitFunctionType :: Int -> Type -> ([Type], Type)
splitFunctionType 0 ty = ([], ty)
splitFunctionType n (TArrow argTy restTy) =
    let (args, ret) = splitFunctionType (n - 1) restTy
    in (argTy : args, ret)
splitFunctionType _ ty = ([], ty)

-- todo(magic-spans): remove workaround
dummyExpr :: Span -> Syntax.Tree.Expr
dummyExpr = Syntax.Tree.ExprNum "0"
