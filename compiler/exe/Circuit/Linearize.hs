{-# LANGUAGE LambdaCase #-}

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

-- | Substitute the nth occurrence (0-indexed) of a variable
substituteNth :: Name -> Int -> CTerm -> Type -> CTerm -> CTerm
substituteNth target n replacement _ty term =
    let (result, _) = go n term
    in result
  where
    go :: Int -> CTerm -> (CTerm, Int)
    go idx (CVar name varTy)
        | name == target && idx == 0 = (replacement, -1)
        | name == target = (CVar name varTy, idx - 1)
        | otherwise = (CVar name varTy, idx)
    go idx (CLam name lamTy b)
        | name == target = (CLam name lamTy b, idx) -- Shadowed
        | otherwise = let (b', idx') = go idx b in (CLam name lamTy b', idx')
    go idx (CApp f x appTy) =
        let (f', idx') = go idx f
            (x', idx'') = go idx' x
        in (CApp f' x' appTy, idx'')
    go idx (CLet name letTy val b)
        | name == target =
            let (val', idx') = go idx val
            in (CLet name letTy val' b, idx')
        | otherwise =
            let (val', idx') = go idx val
                (b', idx'') = go idx' b
            in (CLet name letTy val' b', idx'')
    go idx (CSup l a b supTy) =
        let (a', idx') = go idx a
            (b', idx'') = go idx' b
        in (CSup l a' b' supTy, idx'')
    go idx (CDup name dupTy l val b)
        | name == target =
            let (val', idx') = go idx val
            in (CDup name dupTy l val' b, idx')
        | otherwise =
            let (val', idx') = go idx val
                (b', idx'') = go idx' b
            in (CDup name dupTy l val' b', idx'')
    go idx (CDp0 name dpTy)
        | name == target && idx == 0 = (replacement, -1)
        | name == target = (CDp0 name dpTy, idx - 1)
        | otherwise = (CDp0 name dpTy, idx)
    go idx (CDp1 name dpTy)
        | name == target && idx == 0 = (replacement, -1)
        | name == target = (CDp1 name dpTy, idx - 1)
        | otherwise = (CDp1 name dpTy, idx)
    go idx CEra = (CEra, idx)
    go idx (CRef name refTy) = (CRef name refTy, idx)
    go idx (CInt i) = (CInt i, idx)
    go idx (CBool b) = (CBool b, idx)
    go idx (CStr s) = (CStr s, idx)
    go idx (CTag tag fields tagTy) =
        let (fields', idx') = goFields idx fields
        in (CTag tag fields' tagTy, idx')
      where
        goFields i [] = ([], i)
        goFields i (f : fs) =
            let (f', i') = go i f
                (fs', i'') = goFields i' fs
            in (f' : fs', i'')
    go idx (CCase scrut arms mdef caseTy) =
        let (scrut', idx') = go idx scrut
            (arms', idx'') = goArms idx' arms
            (mdef', idx''') = case mdef of
                Nothing -> (Nothing, idx'')
                Just d -> let (d', i) = go idx'' d in (Just d', i)
        in (CCase scrut' arms' mdef' caseTy, idx''')
      where
        goArms i [] = ([], i)
        goArms i ((tag, fieldsWithTypes, b) : rest)
            | target `elem` map fst fieldsWithTypes =
                let (rest', i') = goArms i rest
                in ((tag, fieldsWithTypes, b) : rest', i')
            | otherwise =
                let (b', i') = go i b
                    (rest', i'') = goArms i' rest
                in ((tag, fieldsWithTypes, b') : rest', i'')
    go idx (CBinOp op a b) =
        let (a', idx') = go idx a
            (b', idx'') = go idx' b
        in (CBinOp op a' b', idx'')
    go idx (CCmpOp op a b) =
        let (a', idx') = go idx a
            (b', idx'') = go idx' b
        in (CCmpOp op a' b', idx'')
    go idx (CUnaryOp op a) =
        let (a', idx') = go idx a
        in (CUnaryOp op a', idx')
    go idx (CClosure liftedName capturedVars closureTy) =
        -- Check if target is in captured vars
        let (capturedVars', idx') = goCaptured idx capturedVars
        in (CClosure liftedName capturedVars' closureTy, idx')
      where
        goCaptured i [] = ([], i)
        goCaptured i ((n', t) : rest)
            | n' == target && i == 0 =
                -- Replace this capture with the replacement's name if it's a var
                case replacement of
                    CVar repName _ -> ((repName, t) : fst (goCaptured (-1) rest), -1)
                    CDp0 repName _ -> ((repName ++ ".0", t) : fst (goCaptured (-1) rest), -1)
                    CDp1 repName _ -> ((repName ++ ".1", t) : fst (goCaptured (-1) rest), -1)
                    _ -> ((n', t) : fst (goCaptured (i - 1) rest), -1)
            | n' == target = ((n', t) : fst (goCaptured (i - 1) rest), i - 1)
            | otherwise =
                let (rest', i') = goCaptured i rest
                in ((n', t) : rest', i')
    go idx (CClosureGetEnv closure envIdx ty) =
        let (closure', idx') = go idx closure
        in (CClosureGetEnv closure' envIdx ty, idx')
    go idx (CProject expr projIdx ty) =
        let (expr', idx') = go idx expr
        in (CProject expr' projIdx ty, idx')
    go idx (CPanic msg ty) = (CPanic msg ty, idx)
    go idx (CFork n' forkTy comp body)
        | n' == target =
            let (comp', idx') = go idx comp
            in (CFork n' forkTy comp' body, idx')
        | otherwise =
            let (comp', idx') = go idx comp
                (body', idx'') = go idx' body
            in (CFork n' forkTy comp' body', idx'')
    go idx (CJoin n' joinTy)
        | n' == target && idx == 0 = (replacement, -1)
        | n' == target = (CJoin n' joinTy, idx - 1)
        | otherwise = (CJoin n' joinTy, idx)

-- | Substitute a variable with a term
substituteVar :: Name -> CTerm -> Type -> CTerm -> CTerm
substituteVar target replacement _ty = go
  where
    go (CVar n varTy)
        | n == target = replacement
        | otherwise = CVar n varTy
    go (CLam n lamTy body)
        | n == target = CLam n lamTy body
        | otherwise = CLam n lamTy (go body)
    go (CApp f x appTy) = CApp (go f) (go x) appTy
    go (CLet n letTy val body)
        | n == target = CLet n letTy (go val) body
        | otherwise = CLet n letTy (go val) (go body)
    go (CSup l a b supTy) = CSup l (go a) (go b) supTy
    go (CDup n dupTy l val body)
        | n == target = CDup n dupTy l (go val) body
        | otherwise = CDup n dupTy l (go val) (go body)
    go (CDp0 n dpTy)
        | n == target = case replacement of
            CDp0 m mTy -> CDp0 m mTy
            CDp1 m mTy -> CDp1 m mTy
            _ -> replacement
        | otherwise = CDp0 n dpTy
    go (CDp1 n dpTy)
        | n == target = case replacement of
            CDp0 m mTy -> CDp0 m mTy
            CDp1 m mTy -> CDp1 m mTy
            _ -> replacement
        | otherwise = CDp1 n dpTy
    go CEra = CEra
    go (CRef n refTy) = CRef n refTy
    go (CInt i) = CInt i
    go (CBool b) = CBool b
    go (CStr s) = CStr s
    go (CTag tag fields tagTy) = CTag tag (map go fields) tagTy
    go (CCase scrut arms mdef caseTy) =
        CCase
            (go scrut)
            [(tag, fts, if target `elem` map fst fts then body else go body) | (tag, fts, body) <- arms]
            (go <$> mdef)
            caseTy
    go (CBinOp op a b) = CBinOp op (go a) (go b)
    go (CCmpOp op a b) = CCmpOp op (go a) (go b)
    go (CUnaryOp op a) = CUnaryOp op (go a)
    go (CClosure liftedName capturedVars closureTy) =
        -- Substitute in captured vars list
        let capturedVars' = [(if n == target then getReplacementName else n, t) | (n, t) <- capturedVars]
        in CClosure liftedName capturedVars' closureTy
      where
        getReplacementName = case replacement of
            CVar repName _ -> repName
            CDp0 repName _ -> repName ++ ".0"
            CDp1 repName _ -> repName ++ ".1"
            _ -> target -- fallback, keep original
    go (CClosureGetEnv closure envIdx envTy) = CClosureGetEnv (go closure) envIdx envTy
    go (CProject expr projIdx projTy) = CProject (go expr) projIdx projTy
    go (CPanic msg ty) = CPanic msg ty
    go (CFork n forkTy comp body)
        | n == target = CFork n forkTy (go comp) body
        | otherwise = CFork n forkTy (go comp) (go body)
    go (CJoin n joinTy)
        | n == target = replacement
        | otherwise = CJoin n joinTy
