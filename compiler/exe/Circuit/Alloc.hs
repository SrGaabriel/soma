{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

{- | Allocation analysis for Circuit IR.

This pass determines whether each value should be stack or heap allocated.
The key insight is that after linearization, every value is used exactly once,
so we don't need GC - we know exactly when to free each value.

Stack-allocated (StackOnly):
  - Primitives: Int, Bool, Char, etc.
  - ADTs where all fields are StackOnly
  - Results of primitive operations

Heap-allocated (MaybeHeap):
  - Lambdas / closures (with captured environment)
  - Superpositions (SUP nodes)
  - Duplicated nodes whose payload is heap-allocated
  - ADTs with at least one MaybeHeap field
  - Polymorphic or unknown types

The analysis propagates allocation information through the term structure,
allowing the lowering pass to make precise stack vs heap decisions.
-}
module Circuit.Alloc (
    -- * Allocation Analysis
    AllocEnv,
    analyzeModule,
    analyzeFunction,
    analyzeTerm,

    -- * Environment operations
    emptyAllocEnv,
    lookupAlloc,
    extendAlloc,

    -- * Re-exports
    AllocKind (..),
) where

import Circuit.Ir
import Control.Monad (forM)
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Environment mapping variable names to their allocation kinds
type AllocEnv = Map Name AllocKind

-- | Empty allocation environment
emptyAllocEnv :: AllocEnv
emptyAllocEnv = Map.empty

-- | Look up a variable's allocation kind (defaults to MaybeHeap if unknown)
lookupAlloc :: Name -> AllocEnv -> AllocKind
lookupAlloc = Map.findWithDefault MaybeHeap

-- | Extend environment with a new binding
extendAlloc :: Name -> AllocKind -> AllocEnv -> AllocEnv
extendAlloc = Map.insert

-- | Analysis state
newtype AllocState = AllocState
    { asTypeEnv :: Map Name AllocKind
    -- ^ Known allocation kinds for ADT types
    }

-- | Analysis monad
type AllocM = ReaderT AllocEnv (State AllocState)

-- | Run allocation analysis
runAllocM :: AllocM a -> AllocEnv -> AllocState -> (a, AllocState)
runAllocM m env = runState (runReaderT m env)

-- | Analyze a complete module
analyzeModule :: CModule -> Map Name AllocKind
analyzeModule CModule{..} =
    let
        -- First, analyze type definitions to build type environment
        typeEnv = analyzeTypes cmTypes
        initState = AllocState{asTypeEnv = typeEnv}

        -- Then analyze each function
        funcResults = map (analyzeFunction' initState) cmFunctions
    in
        Map.unions funcResults

-- | Analyze type definitions to determine their allocation kinds
analyzeTypes :: [CTypeDef] -> Map Name AllocKind
analyzeTypes types =
    -- Fixed-point iteration: keep refining until stable
    let initEnv = Map.fromList [(ctName t, MaybeHeap) | t <- types]
    in fixpoint initEnv
  where
    fixpoint env =
        let env' = Map.fromList [(ctName t, analyzeTypeDef env t) | t <- types]
        in if env == env' then env else fixpoint env'

    analyzeTypeDef :: Map Name AllocKind -> CTypeDef -> AllocKind
    analyzeTypeDef _env CTypeDef{..} =
        -- A type is StackOnly if ALL constructors have only StackOnly fields
        -- For now, we're conservative: only nullary constructors are StackOnly
        if all isNullary ctConstructors
            then StackOnly
            else MaybeHeap
      where
        isNullary CConstructor{..} = ccArity == 0

-- | Analyze a function (internal helper)
analyzeFunction' :: AllocState -> CFunction -> Map Name AllocKind
analyzeFunction' initState CFunction{..} =
    let
        -- Parameters are assumed MaybeHeap (caller decides)
        paramEnv = Map.fromList [(p, MaybeHeap) | (p, _ty) <- cfParams]
        (result, _) = runAllocM (analyzeTerm' cfBody) paramEnv initState
    in
        result

-- | Analyze a function, returning allocation info for all bindings
analyzeFunction :: CFunction -> Map Name AllocKind
analyzeFunction = analyzeFunction' (AllocState Map.empty)

-- | Analyze a term and return allocation kinds for all introduced bindings
analyzeTerm :: AllocEnv -> CTerm -> Map Name AllocKind
analyzeTerm env term =
    let (result, _) = runAllocM (analyzeTerm' term) env (AllocState Map.empty)
    in result

-- | Internal term analysis
analyzeTerm' :: CTerm -> AllocM (Map Name AllocKind)
analyzeTerm' = \case
    -- Literals: no bindings introduced
    CInt _ -> pure Map.empty
    CBool _ -> pure Map.empty
    CStr _ -> pure Map.empty
    CEra -> pure Map.empty
    CRef _ _ -> pure Map.empty
    -- Variables: no new bindings
    CVar _ _ -> pure Map.empty
    CDp0 _ _ -> pure Map.empty
    CDp1 _ _ -> pure Map.empty
    -- Lambda: the parameter binding
    CLam name _paramTy body -> do
        -- Lambda parameter could be anything, default to MaybeHeap
        bodyBindings <- local (extendAlloc name MaybeHeap) $ analyzeTerm' body
        pure $ Map.insert name MaybeHeap bodyBindings

    -- Application: analyze both parts
    CApp f x _ -> do
        fBindings <- analyzeTerm' f
        xBindings <- analyzeTerm' x
        pure $ Map.union fBindings xBindings

    -- Let: the bound value determines the binding's allocation kind
    CLet name _ty val body -> do
        valBindings <- analyzeTerm' val
        let valKind = inferTermKind val
        bodyBindings <- local (extendAlloc name valKind) $ analyzeTerm' body
        pure $ Map.insert name valKind $ Map.union valBindings bodyBindings

    -- Superposition: analyze both branches
    CSup _ a b _ -> do
        aBindings <- analyzeTerm' a
        bBindings <- analyzeTerm' b
        pure $ Map.union aBindings bBindings

    -- Duplication: both projections get the same kind as the duplicated value
    CDup name _ty _ val body -> do
        valBindings <- analyzeTerm' val
        let valKind = inferTermKind val
        -- Both projections (name.0 and name.1) have the same kind
        let projKind = valKind
        bodyBindings <-
            local
                ( extendAlloc (name ++ ".0") projKind
                    . extendAlloc (name ++ ".1") projKind
                )
                $ analyzeTerm' body
        pure
            $ Map.insert (name ++ ".0") projKind
            $ Map.insert (name ++ ".1") projKind
            $ Map.union valBindings bodyBindings

    -- Tagged value: analyze all fields
    CTag _ fields _ -> do
        fieldBindings <- mapM analyzeTerm' fields
        pure $ Map.unions fieldBindings

    -- Case: analyze scrutinee and all branches
    CCase scrut arms mdef _ -> do
        scrutBindings <- analyzeTerm' scrut
        armBindings <- forM arms $ \(_, boundNamesWithTypes, body) -> do
            -- Each bound name gets the field's kind (conservative: MaybeHeap)
            let boundNames = map fst boundNamesWithTypes
            let extendAll = foldr (\n acc -> extendAlloc n MaybeHeap . acc) id boundNames
            bodyBindings <- local extendAll $ analyzeTerm' body
            pure $ foldr (`Map.insert` MaybeHeap) bodyBindings boundNames
        defBindings <- case mdef of
            Just def -> analyzeTerm' def
            Nothing -> pure Map.empty
        pure $ Map.unions (scrutBindings : defBindings : armBindings)

    -- Binary/unary ops: analyze operands
    CBinOp _ a b -> do
        aBindings <- analyzeTerm' a
        bBindings <- analyzeTerm' b
        pure $ Map.union aBindings bBindings
    CCmpOp _ a b -> do
        aBindings <- analyzeTerm' a
        bBindings <- analyzeTerm' b
        pure $ Map.union aBindings bBindings
    CUnaryOp _ a -> analyzeTerm' a
    -- Closures: no new bindings (captured vars already bound elsewhere)
    CClosure{} -> pure Map.empty
    -- Closure env access: analyze the closure term
    CClosureGetEnv closure _ _ -> analyzeTerm' closure
    -- Field projection: analyze the expression
    CProject expr _ _ -> analyzeTerm' expr
    -- Panic: no bindings to analyze (never returns)
    CPanic _ _ -> pure Map.empty
    -- Fork: analyze computation and body, task name is bound in body
    CFork taskName _ty comp body -> do
        compBindings <- analyzeTerm' comp
        -- The task handle is MaybeHeap (pointer to task struct)
        bodyBindings <- local (extendAlloc taskName MaybeHeap) $ analyzeTerm' body
        pure $ Map.insert taskName MaybeHeap $ Map.union compBindings bodyBindings
    -- Join: no new bindings, just returns the result
    CJoin _ _ -> pure Map.empty
    
-- | Infer the allocation kind of a term (without looking at bindings)
inferTermKind :: CTerm -> AllocKind
inferTermKind = \case
    -- Primitives are stack-only
    CInt _ -> StackOnly
    CBool _ -> StackOnly
    CStr _ -> StackOnly -- Note: might need heap for large strings

    -- Erasure produces nothing substantial
    CEra -> StackOnly
    -- Lambdas are closures -> heap
    CLam{} -> MaybeHeap
    -- Superpositions are heap
    CSup{} -> MaybeHeap
    -- Function references could be closures
    CRef _ _ -> MaybeHeap
    -- Variables: unknown, assume heap
    CVar _ _ -> MaybeHeap
    CDp0 _ _ -> MaybeHeap
    CDp1 _ _ -> MaybeHeap
    -- Application result: unknown
    CApp{} -> MaybeHeap
    -- Let/Dup: body determines kind
    CLet _ _ _ body -> inferTermKind body
    CDup _ _ _ _ body -> inferTermKind body
    -- Tagged values: if any field is heap, whole thing is heap
    CTag _ fields _ ->
        if any (\f -> inferTermKind f == MaybeHeap) fields
            then MaybeHeap
            else StackOnly
    -- Case: conservative - if any branch is heap, result is heap
    CCase _ arms mdef _ ->
        let armKinds = map (\(_, _, body) -> inferTermKind body) arms
            defKind = maybe StackOnly inferTermKind mdef
        in if MaybeHeap `elem` (defKind : armKinds)
            then MaybeHeap
            else StackOnly
    -- Primitive ops produce stack values
    CBinOp{} -> StackOnly
    CCmpOp{} -> StackOnly
    CUnaryOp _ _ -> StackOnly
    -- Closures are heap-allocated (contain environment)
    CClosure{} -> MaybeHeap
    -- Closure env access: depends on the extracted value type
    CClosureGetEnv _ _ ty -> classifyType ty
    -- Field projection: depends on the result type
    CProject _ _ ty -> classifyType ty
    -- Panic: never returns, use declared type
    CPanic _ ty -> classifyType ty
    -- Fork: body determines the kind (fork itself produces a task handle)
    CFork _ _ _ body -> inferTermKind body
    -- Join: result type determines the kind
    CJoin _ ty -> classifyType ty