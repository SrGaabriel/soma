{- | Circuit IR Evaluator

Implements interaction net reduction for the Circuit IR.
This is a call-by-value evaluator that reduces terms to
weak head normal form (WHNF) or strong normal form (SNF).

Key reduction rules:
  APP-LAM: (λx. body) arg → body[x := arg]
  APP-SUP: (SUP a b) arg → SUP (a arg₀) (b arg₁)
  DUP-LAM: !d = λx.body → d₀ = λx₀.body₀, d₁ = λx₁.body₁
  DUP-SUP: !d = SUP a b → (same label: d₀=a, d₁=b) or (diff: commute)
  DUP-ERA: !d = * → d₀ = *, d₁ = *
-}
module Circuit.Eval (
    -- * Evaluation
    eval,
    evalWhnf,
    evalSnf,

    -- * Environment
    EvalEnv,
    emptyEnv,

    -- * Statistics
    EvalStats (..),
    evalWithStats,
) where

import Circuit.Ir
import Control.Monad.State
import Data.IORef
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Typing.Types (Kind (..), TyConstructor (..), Type (..))

-- | Substitution map: variable name → term it's bound to
type SubstMap = Map Name CTerm

-- | Duplication map: dup name → (label, value being duplicated)
type DupMap = Map Name (Label, CTerm)

-- | Evaluation environment
data EvalEnv = EvalEnv
    { envSubst :: !SubstMap
    -- ^ Pending substitutions for variables
    , envDups :: !DupMap
    -- ^ Pending duplications
    , envBook :: !(Map Name CTerm)
    -- ^ Top-level function definitions
    , envStats :: !(IORef EvalStats)
    -- ^ Reduction statistics
    }

-- | Evaluation statistics
data EvalStats = EvalStats
    { statInteractions :: !Int
    -- ^ Number of interaction steps
    , statBetaReductions :: !Int
    -- ^ Number of beta reductions (APP-LAM)
    , statDuplications :: !Int
    -- ^ Number of duplication steps
    }
    deriving (Show, Eq)

-- | Empty statistics
emptyStats :: EvalStats
emptyStats = EvalStats 0 0 0

-- | Create an empty environment
emptyEnv :: IO EvalEnv
emptyEnv = do
    stats <- newIORef emptyStats
    pure
        EvalEnv
            { envSubst = Map.empty
            , envDups = Map.empty
            , envBook = Map.empty
            , envStats = stats
            }

-- | Increment interaction counter
incInteractions :: EvalEnv -> IO ()
incInteractions env = modifyIORef' (envStats env) $ \s ->
    s{statInteractions = statInteractions s + 1}

-- | Increment beta reduction counter
incBeta :: EvalEnv -> IO ()
incBeta env = modifyIORef' (envStats env) $ \s ->
    s{statBetaReductions = statBetaReductions s + 1}

-- | Increment duplication counter
incDup :: EvalEnv -> IO ()
incDup env = modifyIORef' (envStats env) $ \s ->
    s{statDuplications = statDuplications s + 1}

-- | Add a substitution
addSubst :: Name -> CTerm -> EvalEnv -> EvalEnv
addSubst name term env = env{envSubst = Map.insert name term (envSubst env)}

-- | Look up and remove a substitution
takeSubst :: Name -> EvalEnv -> (Maybe CTerm, EvalEnv)
takeSubst name env =
    let (mval, subst') = Map.updateLookupWithKey (\_ _ -> Nothing) name (envSubst env)
    in (mval, env{envSubst = subst'})

-- | Add a duplication
addDup :: Name -> Label -> CTerm -> EvalEnv -> EvalEnv
addDup name label term env = env{envDups = Map.insert name (label, term) (envDups env)}

-- | Look up and remove a duplication
takeDup :: Name -> EvalEnv -> (Maybe (Label, CTerm), EvalEnv)
takeDup name env =
    let (mval, dups') = Map.updateLookupWithKey (\_ _ -> Nothing) name (envDups env)
    in (mval, env{envDups = dups'})

-- | Evaluation monad
type EvalM = StateT EvalEnv IO

-- | Run evaluation
runEvalM :: EvalM a -> EvalEnv -> IO (a, EvalEnv)
runEvalM = runStateT

-- | Generate a fresh name
freshName :: String -> EvalM Name
freshName prefix = do
    env <- get
    -- Use a simple counter based on current subst map size
    let n = Map.size (envSubst env) + Map.size (envDups env)
    pure $ prefix ++ "$" ++ show n

-- ============================================================================
-- Weak Head Normal Form
-- ============================================================================

{- | Reduce to weak head normal form
WHNF stops at lambdas, superpositions, and other value forms
-}
evalWhnf :: CTerm -> EvalM CTerm
evalWhnf term = do
    env <- get
    case term of
        -- Variable: look up substitution
        CVar name ty -> do
            let (mval, env') = takeSubst name env
            put env'
            case mval of
                Just val -> evalWhnf val
                Nothing -> pure (CVar name ty)

        -- Dup projections: look up the duplication
        CDp0 name ty -> do
            let (mdup, env') = takeDup name env
            put env'
            case mdup of
                Just (label, val) -> do
                    -- Evaluate the value and handle duplication
                    val' <- evalWhnf val
                    evalDup0 name ty label val'
                Nothing -> pure (CDp0 name ty)
        CDp1 name ty -> do
            let (mdup, env') = takeDup name env
            put env'
            case mdup of
                Just (label, val) -> do
                    val' <- evalWhnf val
                    evalDup1 name ty label val'
                Nothing -> pure (CDp1 name ty)

        -- Duplication: register it and continue with body
        CDup name ty label val body -> do
            modify $ addDup name label val
            evalWhnf body

        -- Application: evaluate function, then apply
        CApp fun arg ty -> do
            fun' <- evalWhnf fun
            evalApp fun' arg ty

        -- Let: strict evaluation, then substitute
        CLet name ty val body -> do
            val' <- evalWhnf val
            modify $ addSubst name val'
            evalWhnf body

        -- Reference: look up in book
        CRef name ty -> do
            book <- gets envBook
            case Map.lookup name book of
                Just def -> evalWhnf def
                Nothing -> pure (CRef name ty)

        -- Values: already in WHNF
        CLam{} -> pure term
        CSup{} -> pure term
        CEra -> pure term
        CInt _ -> pure term
        CBool _ -> pure term
        CStr _ -> pure term
        CTag{} -> pure term
        -- Case: evaluate scrutinee and dispatch
        CCase scrut arms mdef ty -> do
            scrut' <- evalWhnf scrut
            evalCase scrut' arms mdef ty

        -- Primitive operations: evaluate and compute
        CBinOp op a b -> do
            a' <- evalWhnf a
            b' <- evalWhnf b
            evalBinOp op a' b'
        CCmpOp op a b -> do
            a' <- evalWhnf a
            b' <- evalWhnf b
            evalCmpOp op a' b'
        CUnaryOp op a -> do
            a' <- evalWhnf a
            evalUnaryOp op a'

        -- Closure env access: evaluate closure, extract from captured vars
        CClosureGetEnv closure idx ty -> do
            closure' <- evalWhnf closure
            case closure' of
                CClosure _liftedName capturedVars _ ->
                    if idx < length capturedVars
                        then
                            let (varName, varTy) = capturedVars !! idx
                            in evalWhnf (CVar varName varTy)
                        else error $ "CClosureGetEnv: index " ++ show idx ++ " out of bounds"
                _ -> pure (CClosureGetEnv closure' idx ty)

-- | Evaluate application
evalApp :: CTerm -> CTerm -> Type -> EvalM CTerm
evalApp fun arg resultTy = do
    env <- get
    liftIO $ incInteractions env
    case fun of
        -- APP-LAM: beta reduction
        CLam name _paramTy body -> do
            liftIO $ incBeta env
            -- Strict: evaluate argument first
            arg' <- evalWhnf arg
            modify $ addSubst name arg'
            evalWhnf body

        -- APP-CLOSURE: apply closure by calling lifted function with captured args + arg
        CClosure liftedName capturedVars _closureTy -> do
            liftIO $ incBeta env
            -- Strict: evaluate argument first
            arg' <- evalWhnf arg
            -- Build call to lifted function: liftedName(captured..., arg)
            let capturedArgs = [CVar n ty | (n, ty) <- capturedVars]
            -- For now, create nested applications
            let call = foldl (\f a -> CApp f a resultTy) (CRef liftedName resultTy) (capturedArgs ++ [arg'])
            evalWhnf call

        -- APP-SUP: distribute application over superposition
        CSup label a b _supTy -> do
            -- Need to duplicate the argument
            dupName <- freshName "dup"
            let argTy = getTermType arg
            let arg0 = CDp0 dupName argTy
                arg1 = CDp1 dupName argTy
            modify $ addDup dupName label arg
            -- Create superposition of applications
            evalWhnf $ CSup label (CApp a arg0 resultTy) (CApp b arg1 resultTy) resultTy

        -- APP-ERA: erasure absorbs application
        CEra -> pure CEra
        -- Stuck: can't reduce further
        _ -> pure (CApp fun arg resultTy)

-- | Evaluate duplication (projection 0)
evalDup0 :: Name -> Type -> Label -> CTerm -> EvalM CTerm
evalDup0 dupName dupTy label val = do
    env <- get
    liftIO $ incInteractions env
    liftIO $ incDup env
    case val of
        -- DUP-LAM: duplicate lambda
        CLam lamName paramTy body -> do
            -- Create two new lambda parameters
            name0 <- freshName lamName
            name1 <- freshName lamName
            -- Create superposition of parameters for the body
            modify $ addSubst lamName (CSup label (CVar name0 paramTy) (CVar name1 paramTy) paramTy)
            -- Duplicate the body
            bodyDup <- freshName "body"
            let bodyTy = getTermType body
            modify $ addDup bodyDup label body
            -- Return first copy
            evalWhnf $ CLam name0 paramTy (CDp0 bodyDup bodyTy)

        -- DUP-SUP same label: annihilate
        CSup supLabel a b _ | label == supLabel -> do
            -- d₀ = a, d₁ = b
            modify $ addSubst dupName b -- Save b for d₁
            evalWhnf a

        -- DUP-SUP different label: commute
        CSup supLabel a b supTy -> do
            -- Duplicate both components
            dupA <- freshName "a"
            dupB <- freshName "b"
            let elemTy = supTy
            modify $ addDup dupA label a
            modify $ addDup dupB label b
            -- d₀ = SUP[supLabel]{a₀, b₀}
            evalWhnf $ CSup supLabel (CDp0 dupA elemTy) (CDp0 dupB elemTy) supTy

        -- DUP-ERA: erasure duplicates to erasure

        -- DUP-INT/BOOL/STR: values duplicate trivially
        CInt i -> pure (CInt i)
        CBool b -> pure (CBool b)
        -- DUP-TAG: duplicate tagged value (all fields)
        CTag tag fields tagTy -> do
            fieldDups <- mapM (\_ -> freshName "field") fields
            let fieldTypes = map getTermType fields
            mapM_ (\(dn, field) -> modify $ addDup dn label field) (zip fieldDups fields)
            evalWhnf $ CTag tag (zipWith CDp0 fieldDups fieldTypes) tagTy

        -- DUP-CLOSURE: duplicate closure (deep clone)
        CClosure liftedName capturedVars closureTy -> do
            -- Duplicate each captured variable
            captureDups <- mapM (\_ -> freshName "cap") capturedVars
            mapM_ (\(dn, (varName, varTy)) -> modify $ addDup dn label (CVar varName varTy)) (zip captureDups capturedVars)
            let newCaptured = [(dn ++ ".0", ty) | (dn, (_, ty)) <- zip captureDups capturedVars]
            evalWhnf $ CClosure liftedName newCaptured closureTy

        -- Otherwise: stuck
        _ -> do
            -- Re-register the duplication
            modify $ addDup dupName label val
            pure (CDp0 dupName dupTy)

-- | Evaluate duplication (projection 1)
evalDup1 :: Name -> Type -> Label -> CTerm -> EvalM CTerm
evalDup1 dupName dupTy label val = do
    env <- get
    liftIO $ incInteractions env
    liftIO $ incDup env
    case val of
        -- DUP-LAM: duplicate lambda (second copy)
        CLam lamName paramTy body -> do
            name0 <- freshName lamName
            name1 <- freshName lamName
            modify $ addSubst lamName (CSup label (CVar name0 paramTy) (CVar name1 paramTy) paramTy)
            bodyDup <- freshName "body"
            let bodyTy = getTermType body
            modify $ addDup bodyDup label body
            evalWhnf $ CLam name1 paramTy (CDp1 bodyDup bodyTy)

        -- DUP-SUP same label: annihilate
        CSup supLabel a b _ | label == supLabel -> do
            modify $ addSubst dupName a -- Save a for d₀
            evalWhnf b

        -- DUP-SUP different label: commute
        CSup supLabel a b supTy -> do
            dupA <- freshName "a"
            dupB <- freshName "b"
            let elemTy = supTy
            modify $ addDup dupA label a
            modify $ addDup dupB label b
            evalWhnf $ CSup supLabel (CDp1 dupA elemTy) (CDp1 dupB elemTy) supTy

        -- DUP-ERA

        -- DUP values
        CInt i -> pure (CInt i)
        CBool b -> pure (CBool b)
        -- DUP-TAG: duplicate tagged value (all fields)
        CTag tag fields tagTy -> do
            fieldDups <- mapM (\_ -> freshName "field") fields
            let fieldTypes = map getTermType fields
            mapM_ (\(dn, field) -> modify $ addDup dn label field) (zip fieldDups fields)
            evalWhnf $ CTag tag (zipWith CDp1 fieldDups fieldTypes) tagTy

        -- DUP-CLOSURE: duplicate closure (deep clone) - second projection
        CClosure liftedName capturedVars closureTy -> do
            captureDups <- mapM (\_ -> freshName "cap") capturedVars
            mapM_ (\(dn, (varName, varTy)) -> modify $ addDup dn label (CVar varName varTy)) (zip captureDups capturedVars)
            let newCaptured = [(dn ++ ".1", ty) | (dn, (_, ty)) <- zip captureDups capturedVars]
            evalWhnf $ CClosure liftedName newCaptured closureTy

        -- Stuck
        _ -> do
            modify $ addDup dupName label val
            pure (CDp1 dupName dupTy)

-- | Evaluate case expression
evalCase :: CTerm -> [(Int, [(Name, Type)], CTerm)] -> Maybe CTerm -> Type -> EvalM CTerm
evalCase scrut arms mdef resultTy =
    case scrut of
        -- Match on tag
        CTag tag fields _ -> do
            case lookup tag [(t, (ns, b)) | (t, ns, b) <- arms] of
                Just (bindings, body) -> do
                    -- Bind each field to its corresponding name
                    mapM_ (\((name, _ty), field) -> modify $ addSubst name field) (zip bindings fields)
                    evalWhnf body
                Nothing -> case mdef of
                    Just def -> evalWhnf def
                    Nothing -> pure $ CCase scrut arms mdef resultTy -- Stuck/error

        -- Match on bool (encoded as tag 0/1)
        CBool b -> do
            let tag = if b then 1 else 0
            case lookup tag [(t, (ns, body)) | (t, ns, body) <- arms] of
                Just (_, body) -> evalWhnf body
                Nothing -> case mdef of
                    Just def -> evalWhnf def
                    Nothing -> pure $ CCase scrut arms mdef resultTy

        -- Match on int (for simple switches)
        CInt i -> do
            case lookup i [(t, (ns, body)) | (t, ns, body) <- arms] of
                Just (_, body) -> evalWhnf body
                Nothing -> case mdef of
                    Just def -> evalWhnf def
                    Nothing -> pure $ CCase scrut arms mdef resultTy

        -- Superposition: distribute case
        CSup label a b _ -> do
            -- For each arm, we need to duplicate bindings
            -- Simplified: just create superposition of case results
            evalWhnf
                $ CSup
                    label
                    (CCase a arms mdef resultTy)
                    (CCase b arms mdef resultTy)
                    resultTy

        -- Stuck
        _ -> pure $ CCase scrut arms mdef resultTy

-- | Evaluate binary operation
evalBinOp :: BinOp -> CTerm -> CTerm -> EvalM CTerm
evalBinOp op (CInt a) (CInt b) = pure $ CInt $ case op of
    OpAdd -> a + b
    OpSub -> a - b
    OpMul -> a * b
    OpDiv -> a `div` b
    OpMod -> a `mod` b
    OpAnd -> a .&. b
    OpOr -> a .|. b
    OpXor -> a `xor` b
    OpShl -> a `shiftL` b
    OpShr -> a `shiftR` b
  where
    (.&.) x y = if x /= 0 && y /= 0 then 1 else 0 -- Simplified
    (.|.) x y = if x /= 0 || y /= 0 then 1 else 0
    xor x y = if (x /= 0) /= (y /= 0) then 1 else 0
    shiftL x n = x * (2 ^ n)
    shiftR x n = x `div` (2 ^ n)
evalBinOp op a b = pure $ CBinOp op a b

-- | Evaluate comparison operation
evalCmpOp :: CmpOp -> CTerm -> CTerm -> EvalM CTerm
evalCmpOp op (CInt a) (CInt b) = pure $ CBool $ case op of
    OpEq -> a == b
    OpNe -> a /= b
    OpLt -> a < b
    OpLe -> a <= b
    OpGt -> a > b
    OpGe -> a >= b
evalCmpOp op a b = pure $ CCmpOp op a b

-- | Evaluate unary operation
evalUnaryOp :: UnaryOp -> CTerm -> EvalM CTerm
evalUnaryOp OpNeg (CInt a) = pure $ CInt (-a)
evalUnaryOp OpNot (CBool b) = pure $ CBool (not b)
evalUnaryOp OpNot (CInt i) = pure $ CInt (if i == 0 then 1 else 0)
evalUnaryOp op a = pure $ CUnaryOp op a

-- ============================================================================
-- Strong Normal Form
-- ============================================================================

-- | Reduce to strong normal form (fully normalize)
evalSnf :: CTerm -> EvalM CTerm
evalSnf term = do
    whnf <- evalWhnf term
    case whnf of
        CLam name ty body -> do
            body' <- evalSnf body
            pure $ CLam name ty body'
        CApp f x ty -> do
            f' <- evalSnf f
            x' <- evalSnf x
            pure $ CApp f' x' ty
        CSup label a b ty -> do
            a' <- evalSnf a
            b' <- evalSnf b
            pure $ CSup label a' b' ty
        CDup name ty label val body -> do
            val' <- evalSnf val
            body' <- evalSnf body
            pure $ CDup name ty label val' body'
        CTag tag fields ty -> do
            fields' <- mapM evalSnf fields
            pure $ CTag tag fields' ty
        CCase scrut arms mdef ty -> do
            scrut' <- evalSnf scrut
            arms' <-
                mapM
                    ( \(t, ns, b) -> do
                        b' <- evalSnf b
                        pure (t, ns, b')
                    )
                    arms
            mdef' <- traverse evalSnf mdef
            pure $ CCase scrut' arms' mdef' ty
        CBinOp op a b -> do
            a' <- evalSnf a
            b' <- evalSnf b
            pure $ CBinOp op a' b'
        CCmpOp op a b -> do
            a' <- evalSnf a
            b' <- evalSnf b
            pure $ CCmpOp op a' b'
        CUnaryOp op a -> do
            a' <- evalSnf a
            pure $ CUnaryOp op a'
        CLet name ty val body -> do
            val' <- evalSnf val
            body' <- evalSnf body
            pure $ CLet name ty val' body'

        -- Values: already normal
        _ -> pure whnf

-- ============================================================================
-- Top-level API
-- ============================================================================

-- | Evaluate a term to strong normal form
eval :: CTerm -> IO CTerm
eval term = do
    env <- emptyEnv
    (result, _) <- runEvalM (evalSnf term) env
    pure result

-- | Evaluate with statistics
evalWithStats :: CTerm -> IO (CTerm, EvalStats)
evalWithStats term = do
    env <- emptyEnv
    (result, env') <- runEvalM (evalSnf term) env
    stats <- readIORef (envStats env')
    pure (result, stats)
