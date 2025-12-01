{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

{- | Linearization pass for Circuit IR.

This pass transforms non-affine terms (where variables can be used
multiple times) into affine terms (where each variable is used exactly
once) by inserting explicit DUP (duplication) and ERA (erasure) nodes.

For example:
  λx. (x x)
becomes:
  λx. !y &0 = x; (y₀ y₁)

And:
  λx. 42
becomes:
  λx. !_ &0 = x; 42   (or we can just use the variable with ERA)

The algorithm:
1. For each binding (lambda, let), count uses of the bound variable
2. If used 0 times: insert erasure
3. If used 1 time: keep as-is (already linear)
4. If used n times: insert (n-1) DUP nodes to create n copies
-}
module Circuit.Linearize where

import Circuit.Ir
import Control.Monad (foldM)
import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Typing.Types (Type)

-- | State for linearization
data LinearState = LinearState
    { lsNextLabel :: !Label
    -- ^ Next fresh label for DUP/SUP pairs
    , lsNextName :: !Int
    -- ^ Counter for generating fresh names
    , lsTypeEnv :: !(Map Name Type)
    -- ^ Type environment for variables
    }
    deriving (Show)

-- | Initial linearization state
initLinearState :: LinearState
initLinearState =
    LinearState
        { lsNextLabel = 0
        , lsNextName = 0
        , lsTypeEnv = Map.empty
        }

type LinearM = State LinearState

-- | Generate a fresh label
freshLabel :: LinearM Label
freshLabel = do
    s <- get
    put s{lsNextLabel = lsNextLabel s + 1}
    pure (lsNextLabel s)

-- | Generate a fresh variable name
freshName :: String -> LinearM Name
freshName prefix = do
    s <- get
    put s{lsNextName = lsNextName s + 1}
    pure (prefix ++ "_" ++ show (lsNextName s))

-- | Look up a variable's type
lookupType :: Name -> LinearM (Maybe Type)
lookupType name = gets (Map.lookup name . lsTypeEnv)

-- | Add a variable to the type environment
addType :: Name -> Type -> LinearM ()
addType name ty = modify $ \s -> s{lsTypeEnv = Map.insert name ty (lsTypeEnv s)}

-- | Linearize a complete module
linearizeModule :: CModule -> CModule
linearizeModule m =
    m
        { cmFunctions = map linearizeFunction (cmFunctions m)
        , cmIsLinearized = True
        }

-- | Linearize a function
linearizeFunction :: CFunction -> CFunction
linearizeFunction f =
    let initState = initLinearState{lsTypeEnv = Map.fromList (cfParams f)}
        body' = evalState (linearizeFunctionBody (cfParams f) (cfBody f)) initState
    in f
        { cfBody = body'
        , cfMetadata = (cfMetadata f){cfmIsLinear = True}
        }

-- | Linearize a function body, handling parameter usage
linearizeFunctionBody :: [(Name, Type)] -> CTerm -> LinearM CTerm
linearizeFunctionBody params body = do
    -- First linearize the body itself
    body' <- linearizeTerm body
    -- Then insert DUPs for parameters used multiple times
    foldM linearizeParam body' params
  where
    linearizeParam :: CTerm -> (Name, Type) -> LinearM CTerm
    linearizeParam b (param, paramTy) = do
        let uses = countVarUses param b
        case uses of
            0 -> do
                -- Parameter unused: insert erasure
                label <- freshLabel
                tmpName <- freshName "era"
                pure $ CDup tmpName paramTy label (CVar param paramTy) b
            1 -> pure b -- Already linear
            _ -> linearizeBinding param paramTy uses b -- Insert DUP chain

-- | Linearize a term, inserting DUP/ERA nodes as needed
linearizeTerm :: CTerm -> LinearM CTerm
linearizeTerm = \case
    CVar n ty -> pure (CVar n ty)
    CLam n ty body -> do
        addType n ty
        -- Count how many times n is used in body
        let uses = countVarUses n body
        body' <- linearizeTerm body
        case uses of
            0 -> do
                -- Variable unused: we still need to consume it
                label <- freshLabel
                tmpName <- freshName "era"
                pure $ CLam n ty (CDup tmpName ty label (CVar n ty) body')
            1 -> do
                -- Already linear
                pure $ CLam n ty body'
            _ -> do
                -- Need to duplicate
                linearizeLam n ty uses body'
    CApp f x ty -> do
        f' <- linearizeTerm f
        x' <- linearizeTerm x
        pure $ CApp f' x' ty
    CLet n ty val body -> do
        addType n ty
        val' <- linearizeTerm val
        let uses = countVarUses n body
        body' <- linearizeTerm body
        case uses of
            0 -> do
                -- void freshLabel
                tmpName <- freshName "era"
                pure $ CLet tmpName ty val' body'
            1 -> pure $ CLet n ty val' body'
            _ -> linearizeLet n ty val' uses body'
    CSup l a b ty -> CSup l <$> linearizeTerm a <*> linearizeTerm b <*> pure ty
    CDup n ty l val body -> CDup n ty l <$> linearizeTerm val <*> linearizeTerm body
    CDp0 n ty -> pure $ CDp0 n ty
    CDp1 n ty -> pure $ CDp1 n ty
    CEra -> pure CEra
    CRef n ty -> pure $ CRef n ty
    CInt i -> pure $ CInt i
    CBool b -> pure $ CBool b
    CStr s -> pure $ CStr s
    CTag tag fields ty -> CTag tag <$> mapM linearizeTerm fields <*> pure ty
    CCase scrut arms mdef ty -> do
        scrut' <- linearizeTerm scrut
        arms' <-
            mapM
                ( \(tag, fieldsWithTypes, body) -> do
                    -- Add field types to environment
                    mapM_ (uncurry addType) fieldsWithTypes
                    -- For each field name, check usage and handle accordingly
                    (fieldsWithTypes', body') <- linearizeFieldBindings fieldsWithTypes body
                    pure (tag, fieldsWithTypes', body')
                )
                arms
        mdef' <- traverse linearizeTerm mdef
        pure $ CCase scrut' arms' mdef' ty
    CBinOp op a b -> CBinOp op <$> linearizeTerm a <*> linearizeTerm b
    CCmpOp op a b -> CCmpOp op <$> linearizeTerm a <*> linearizeTerm b
    CUnaryOp op a -> CUnaryOp op <$> linearizeTerm a
    CClosure liftedName capturedVars closureTy -> do
        -- For closures, we need to linearize the captured variables
        -- Each captured var is used exactly once in the closure
        pure $ CClosure liftedName capturedVars closureTy
    CClosureGetEnv closure idx ty -> do
        closure' <- linearizeTerm closure
        pure $ CClosureGetEnv closure' idx ty
    CProject expr idx ty -> do
        expr' <- linearizeTerm expr
        pure $ CProject expr' idx ty
    CPanic msg ty -> pure $ CPanic msg ty
    -- Fork/Join are inserted after linearization by the Parallel pass
    -- They should not appear in input, but if they do, just recurse
    CFork n ty comp body -> CFork n ty <$> linearizeTerm comp <*> linearizeTerm body
    CJoin n ty -> pure $ CJoin n ty

{- | Linearize field bindings in a case arm
Returns updated field names with types and linearized body
-}
linearizeFieldBindings :: [(Name, Type)] -> CTerm -> LinearM ([(Name, Type)], CTerm)
linearizeFieldBindings fieldsWithTypes body = do
    body' <- linearizeTerm body
    -- Process each field
    (fieldsWithTypes', body'') <- foldM processField ([], body') fieldsWithTypes
    pure (reverse fieldsWithTypes', body'')
  where
    processField :: ([(Name, Type)], CTerm) -> (Name, Type) -> LinearM ([(Name, Type)], CTerm)
    processField (accFields, accBody) (n, ty) = do
        let uses = countVarUses n accBody
        case uses of
            0 -> do
                -- Unused field: rename to era_*
                tmpName <- freshName "era"
                pure ((tmpName, ty) : accFields, accBody)
            1 ->
                -- Single use: keep as is
                pure ((n, ty) : accFields, accBody)
            _ -> do
                -- Multiple uses: insert DUP chain
                accBody' <- linearizeBinding n ty uses accBody
                pure ((n, ty) : accFields, accBody')

-- | Create DUP chain for a lambda with multiple uses
linearizeLam :: Name -> Type -> Int -> CTerm -> LinearM CTerm
linearizeLam origName ty uses body = do
    body' <- linearizeBinding origName ty uses body
    pure $ CLam origName ty body'

-- | Create DUP chain for a let with multiple uses
linearizeLet :: Name -> Type -> CTerm -> Int -> CTerm -> LinearM CTerm
linearizeLet origName ty val uses body = do
    body' <- linearizeBinding origName ty uses body
    pure $ CLet origName ty val body'

{- | Insert a chain of DUPs to make `uses` copies of variable `origName`
Returns the modified body where origName occurrences are replaced
with the appropriate dup projections.
-}
linearizeBinding :: Name -> Type -> Int -> CTerm -> LinearM CTerm
linearizeBinding origName ty uses body = do
    if uses <= 1
        then pure body
        else buildDupChain origName ty uses body

{- | Build a chain of DUP nodes for a variable used multiple times.

Strategy: right-leaning chain of DUPs
  - For 2 uses: !d &L = x; body[x₁ -> d₀, x₂ -> d₁]
  - For 3 uses: !d0 &L0 = x; !d1 &L1 = d0₁; body[x₁ -> d0₀, x₂ -> d1₀, x₃ -> d1₁]
  - For n uses: chain of n-1 DUPs
-}
buildDupChain :: Name -> Type -> Int -> CTerm -> LinearM CTerm
buildDupChain origName ty uses body = do
    go origName uses body
  where
    go :: Name -> Int -> CTerm -> LinearM CTerm
    go src 2 b = do
        -- Base case: one DUP producing two projections
        label <- freshLabel
        dupName <- freshName "dup"
        -- Replace first two occurrences of src with d₀ and d₁
        let b' = substituteNth src 0 (CDp0 dupName ty) ty $ substituteNth src 0 (CDp1 dupName ty) ty b
        pure $ CDup dupName ty label (CVar src ty) b'
    go src n b | n > 2 = do
        -- Recursive case: one DUP, dp0 goes to first use, dp1 continues chain
        label <- freshLabel
        dupName <- freshName "dup"
        -- First occurrence gets dp0
        let b' = substituteNth src 0 (CDp0 dupName ty) ty b
        -- Remaining (n-1) occurrences will be handled by recursion
        inner <- go src (n - 1) b'
        -- Now wrap with the DUP, but the inner chain uses src still
        -- We need to replace src with CDp1 in the inner result
        let inner' = substituteVar src (CDp1 dupName ty) ty inner
        pure $ CDup dupName ty label (CVar src ty) inner'
    go _ _ b = pure b

{- | Substitute the nth occurrence (0-indexed) of a variable.

Uses State monad to track the occurrence index during traversal.
This is binding-aware: occurrences under shadowing binders are skipped.
-}
substituteNth :: Name -> Int -> CTerm -> Type -> CTerm -> CTerm
substituteNth target n replacement _ty term =
    evalState (go term) n
  where
    -- Decrement counter and check if we should substitute
    trySubst :: CTerm -> State Int CTerm
    trySubst original = do
        idx <- get
        if idx == 0
            then put (-1) >> pure replacement
            else put (idx - 1) >> pure original

    go :: CTerm -> State Int CTerm
    go term' = case term' of
        -- Variable references: check for match
        CVar name varTy
            | name == target -> trySubst (CVar name varTy)
            | otherwise -> pure (CVar name varTy)
        CDp0 name dpTy
            | name == target -> trySubst (CDp0 name dpTy)
            | otherwise -> pure (CDp0 name dpTy)
        CDp1 name dpTy
            | name == target -> trySubst (CDp1 name dpTy)
            | otherwise -> pure (CDp1 name dpTy)
        -- Binding forms: check for shadowing
        CLam name lamTy body
            | name == target -> pure (CLam name lamTy body) -- Shadowed
            | otherwise -> CLam name lamTy <$> go body
        CLet name letTy val body
            | name == target -> CLet name letTy <$> go val <*> pure body -- Shadowed in body
            | otherwise -> CLet name letTy <$> go val <*> go body
        CDup name dupTy l val body
            | name == target -> CDup name dupTy l <$> go val <*> pure body -- Shadowed
            | otherwise -> CDup name dupTy l <$> go val <*> go body
        CCase scrut arms mdef caseTy -> do
            scrut' <- go scrut
            arms' <- traverse goArm arms
            mdef' <- traverse go mdef
            pure $ CCase scrut' arms' mdef' caseTy
          where
            goArm (tag, fieldsWithTypes, body)
                | target `elem` map fst fieldsWithTypes = pure (tag, fieldsWithTypes, body)
                | otherwise = (tag,fieldsWithTypes,) <$> go body
        -- CClosure: substitute in captured vars list
        CClosure liftedName capturedVars closureTy -> do
            capturedVars' <- goCaptured capturedVars
            pure $ CClosure liftedName capturedVars' closureTy
          where
            goCaptured [] = pure []
            goCaptured ((n', t) : rest)
                | n' == target = do
                    idx <- get
                    if idx == 0
                        then do
                            put (-1)
                            let newName = case replacement of
                                    CVar repName _ -> repName
                                    CDp0 repName _ -> repName ++ ".0"
                                    CDp1 repName _ -> repName ++ ".1"
                                    _ -> n'
                            rest' <- goCaptured rest
                            pure $ (newName, t) : rest'
                        else do
                            put (idx - 1)
                            rest' <- goCaptured rest
                            pure $ (n', t) : rest'
                | otherwise = ((n', t) :) <$> goCaptured rest
        -- All other nodes: traverse children using mapChildrenM
        _ -> mapChildrenM go term'

{- | Substitute a variable with a term.

This is binding-aware: substitution stops at binders that shadow the target.
Uses mapChildren for non-binding cases.
-}
substituteVar :: Name -> CTerm -> Type -> CTerm -> CTerm
substituteVar target replacement _ty = go
  where
    go term = case term of
        -- Variable references: substitute if matches
        CVar n _
            | n == target -> replacement
        CDp0 n _
            | n == target -> case replacement of
                CDp0 m mTy -> CDp0 m mTy
                CDp1 m mTy -> CDp1 m mTy
                _ -> replacement
        CDp1 n _
            | n == target -> case replacement of
                CDp0 m mTy -> CDp0 m mTy
                CDp1 m mTy -> CDp1 m mTy
                _ -> replacement
        -- Binding forms: check for shadowing
        CLam n lamTy body
            | n == target -> CLam n lamTy body -- Shadowed
            | otherwise -> CLam n lamTy (go body)
        CLet n letTy val body
            | n == target -> CLet n letTy (go val) body -- Shadowed in body
            | otherwise -> CLet n letTy (go val) (go body)
        CDup n dupTy l val body
            | n == target -> CDup n dupTy l (go val) body -- Shadowed
            | otherwise -> CDup n dupTy l (go val) (go body)
        CCase scrut arms mdef caseTy ->
            CCase
                (go scrut)
                [(tag, fts, if target `elem` map fst fts then body else go body) | (tag, fts, body) <- arms]
                (go <$> mdef)
                caseTy
        -- CClosure: substitute in captured vars list
        CClosure liftedName capturedVars closureTy ->
            let capturedVars' = [(if n == target then getReplacementName else n, t) | (n, t) <- capturedVars]
            in CClosure liftedName capturedVars' closureTy
          where
            getReplacementName = case replacement of
                CVar repName _ -> repName
                CDp0 repName _ -> repName ++ ".0"
                CDp1 repName _ -> repName ++ ".1"
                _ -> target -- fallback, keep original
                -- All other terms: just recurse into children
        _ -> mapChildren go term
