{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

{- | Circuit to Alloy lowering.

This module lowers linearized Circuit IR to Alloy MIR. The key challenges are:

1. Circuit uses lambda calculus; Alloy uses CFG with explicit control flow
2. DUP/SUP pairs in Circuit represent cloning; these need special lowering
3. Circuit is expression-based; Alloy uses SSA-style let bindings
4. Memory management: heap values need explicit allocation and ERA-triggered frees

Lowering strategy:
- Each Circuit function becomes an Alloy function with a single entry block
- Lambdas are eta-expanded into multi-arg functions where possible
- DUPs become explicit copy operations (or identity for affine values)
- SUPs create pairs that DUPs can destructure
- Tagged values (CTag) become OpConstruct
- Case expressions (CCase) become ASwitch terminators with join blocks

Memory management:
- StackOnly values: use stack allocation (OpConstruct, OpMakeTuple)
- MaybeHeap values: use heap allocation (OpAllocHeap)
- ERA nodes: emit EffDrop for heap values to trigger recursive free
-}
module Circuit.ToAlloy (
    lowerCircuitToAlloy,
) where

import Alloy.Build
import Circuit.Alloc (AllocEnv, AllocKind (..), analyzeFunction, lookupAlloc)
import Circuit.Escape (EscapeEnv, analyzeFunctionEscapes, canElideClone)
import Circuit.Constants (parallelWorkThreshold)
import qualified Circuit.Ir as C
import Control.Monad (forM, forM_, when)
import Data.List (isPrefixOf)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Typing.Types (Type (..), tupleType)

-- | Check if a type is a function type (closure)
isFunctionType :: Type -> Bool
isFunctionType (TArrow _ _) = True
isFunctionType _ = False

{- | Environment for lowering, containing:
  - Operand bindings (name -> Alloy operand)
  - Allocation info (name -> StackOnly/MaybeHeap)
  - Escape info (name -> escape status for clone elision)
  - Closure slot types (for closures we've seen, their captured var types)
  - Cloned closures (closures that came from OpDupClosureProj1 and have SUP slots)
-}
data LowerEnv = LowerEnv
    { leOperands :: Map C.Name AOperand
    , leAllocInfo :: AllocEnv
    , leEscapeInfo :: EscapeEnv -- escape analysis results for clone elision
    , leClosureSlotTypes :: Map C.Name SlotInfo -- name -> [(slotIdx, isClosureTyped)]
    , leClonedClosures :: Map C.Name () -- closures with SUP slots (from proj1)
    , leClosureEnvSizes :: Map C.Name Int -- name -> env size for closures
    }

-- | Empty lowering environment
emptyLowerEnv :: LowerEnv
emptyLowerEnv = LowerEnv Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty

-- | Look up an operand in the environment
lookupOperand :: C.Name -> LowerEnv -> Maybe AOperand
lookupOperand name = Map.lookup name . leOperands

-- | Extend environment with an operand binding
extendOperand :: C.Name -> AOperand -> LowerEnv -> LowerEnv
extendOperand name op env = env{leOperands = Map.insert name op (leOperands env)}

-- | Get allocation kind for a name
getAllocKind :: C.Name -> LowerEnv -> AllocKind
getAllocKind name env = lookupAlloc name (leAllocInfo env)

-- | Record closure slot types
recordClosureSlotTypes :: C.Name -> SlotInfo -> LowerEnv -> LowerEnv
recordClosureSlotTypes name slotInfo env =
    env{leClosureSlotTypes = Map.insert name slotInfo (leClosureSlotTypes env)}

-- | Look up closure slot types
lookupClosureSlotTypes :: C.Name -> LowerEnv -> Maybe SlotInfo
lookupClosureSlotTypes name = Map.lookup name . leClosureSlotTypes

-- | Mark a closure as cloned (has SUP slots)
markAsCloned :: C.Name -> LowerEnv -> LowerEnv
markAsCloned name env = env{leClonedClosures = Map.insert name () (leClonedClosures env)}

-- | Check if a closure is cloned
isClonedClosure :: C.Name -> LowerEnv -> Bool
isClonedClosure name env = Map.member name (leClonedClosures env)

-- | Record closure env size
recordClosureEnvSize :: C.Name -> Int -> LowerEnv -> LowerEnv
recordClosureEnvSize name size env =
    env{leClosureEnvSizes = Map.insert name size (leClosureEnvSizes env)}

-- | Look up closure env size
lookupClosureEnvSize :: C.Name -> LowerEnv -> Maybe Int
lookupClosureEnvSize name = Map.lookup name . leClosureEnvSizes

-- | Check if a type is a closure/function type
isClosureType :: Type -> Bool
isClosureType (TArrow _ _) = True
isClosureType _ = False

{- | Compute slot info from captured variables
Returns [(slotIdx, isClosureTyped)] for use with specialized DUP ops
-}
computeSlotInfo :: [(C.Name, Type)] -> SlotInfo
computeSlotInfo capturedVars =
    [(idx, isClosureType ty) | (idx, (_, ty)) <- zip [0 ..] capturedVars]

{- | Work estimation for parallel reduction.

Estimate the computational cost of reducing a value. This is used to decide
whether to emit parallel projection ops (OpParProj0/1) vs sequential ones.

Heuristic based on:
- Closure env_size: more captured vars = more complex computation
- Closure arity: more params = more applications to come
- Nested closures: closure-typed env slots suggest more parallel potential

Work threshold: 50 (matches SOMA_WORK_THRESHOLD in runtime)
-}
estimateWorkFromType :: Type -> Int -> SlotInfo -> Int
estimateWorkFromType ty envSize slotInfo =
    let baseWork = case ty of
            TArrow _ _ -> 10 -- Closure base cost
            _ -> 5 -- Other heap values
        envWork = envSize * 5 -- Each captured var adds complexity
        -- Count closure-typed slots (nested parallel potential)
        closureSlots = length [() | (_, True) <- slotInfo]
        nestedWork = closureSlots * 10
    in baseWork + envWork + nestedWork

-- | Check if work estimate justifies parallel reduction
shouldUseParallel :: Int -> Bool
shouldUseParallel workEstimate = workEstimate >= parallelWorkThreshold

-- | Lower a Circuit module to an Alloy module
lowerCircuitToAlloy :: C.CModule -> AlloyModule
lowerCircuitToAlloy cmod =
    let (_, alloyMod) = runAlloyBuilder (C.cmName cmod) [] $ do
            forM_ (C.cmFunctions cmod) lowerFunction
    in alloyMod

-- | Lower a Circuit function to Alloy
lowerFunction :: C.CFunction -> AlloyBuilder ()
lowerFunction cfun@C.CFunction{..} = do
    -- Analyze allocation kinds for all bindings in this function
    let allocInfo = analyzeFunction cfun
    -- Analyze escape status for clone elision optimization
    let escapeInfo = analyzeFunctionEscapes cfun

    -- Use typed parameters from the Circuit function
    beginFunction cfName cfParams cfReturnType
    entryBlock <- freshBlockName
    beginBlock entryBlock []

    -- Initialize environment with parameters and allocation info
    let env0 =
            LowerEnv
                { leOperands = Map.fromList [(p, OpVar p) | (p, _ty) <- cfParams]
                , leAllocInfo = allocInfo
                , leEscapeInfo = escapeInfo
                , leClosureSlotTypes = Map.empty
                , leClonedClosures = Map.empty
                , leClosureEnvSizes = Map.empty
                }

    -- Lower the body
    result <- lowerTerm env0 cfBody

    -- Return the result
    terminate (ARet (Just result))

    endFunction

-- | Lower a Circuit term to Alloy, returning the operand holding the result
lowerTerm :: LowerEnv -> C.CTerm -> AlloyBuilder AOperand
lowerTerm env term = case term of
    -- Variables: look up in environment, or treat as global reference
    C.CVar name _ ->
        case lookupOperand name env of
            Just op -> pure op
            -- Not in env - treat as a global function reference
            Nothing -> pure (OpVar name)
    -- Literals
    C.CInt n -> pure (OpConst (CInt n))
    C.CBool b -> pure (OpConst (CBool b))
    C.CStr s -> pure (OpConst (CString s))
    -- Function references
    C.CRef name _ -> pure (OpVar name)
    -- Erasure
    C.CEra -> pure (OpConst CUnit)
    -- Let bindings
    C.CLet name _ty val body -> do
        valOp <- lowerTerm env val
        let env' = case val of
                C.CClosure _ capturedVars _ ->
                    let slotInfo = computeSlotInfo capturedVars
                        envSize = length capturedVars
                    in recordClosureEnvSize name envSize
                        $ recordClosureSlotTypes name slotInfo
                        $ extendOperand name valOp env
                _ -> extendOperand name valOp env
        lowerTerm env' body

    -- Lambdas (should be hoisted)
    C.CLam{} ->
        error "Circuit.ToAlloy: first-class lambdas not yet supported (should be hoisted)"
    -- Closure allocation
    C.CClosure liftedName capturedVars closureTy -> do
        capturedOps <-
            mapM
                ( \(n, _) -> case lookupOperand n env of
                    Just op -> pure op
                    Nothing -> pure (OpVar n)
                )
                capturedVars
        let arity = countArityFromType closureTy
            envSize = length capturedVars
        closureName <- emitLetTmp closureTy (OpAllocClosure (OpVar liftedName) arity envSize)
        forM_ (zip [0 ..] capturedOps) $ \(idx, capturedOp) ->
            emitEffect (EffClosureSetEnv (OpVar closureName) idx capturedOp)
        pure (OpVar closureName)

    -- Application (uncurried)
    C.CApp{} -> do
        let (fun, args) = collectArgs term
            resultTy = C.getTermType term
        argOps <- mapM (lowerTerm env) args
        case fun of
            C.CRef fName _ -> do
                result <- emitLetTmp resultTy (OpCall (Direct fName) argOps)
                pure (OpVar result)
            C.CVar fName fTy ->
                case lookupOperand fName env of
                    Nothing -> do
                        result <- emitLetTmp resultTy (OpCall (Direct fName) argOps)
                        pure (OpVar result)
                    Just closureOp | isFunctionType fTy -> do
                        funcPtr <- emitLetTmp fTy (OpClosureGetFunc closureOp)
                        let fullArgs = closureOp : argOps
                        result <- emitLetTmp resultTy (OpCall (Indirect (OpVar funcPtr)) fullArgs)
                        pure (OpVar result)
                    Just op -> do
                        result <- emitLetTmp resultTy (OpCall (Indirect op) argOps)
                        pure (OpVar result)
            _ -> do
                fOp <- lowerTerm env fun
                let fTy = C.getTermType fun
                if isFunctionType fTy
                    then do
                        funcPtr <- emitLetTmp fTy (OpClosureGetFunc fOp)
                        let fullArgs = fOp : argOps
                        result <- emitLetTmp resultTy (OpCall (Indirect (OpVar funcPtr)) fullArgs)
                        pure (OpVar result)
                    else do
                        result <- emitLetTmp resultTy (OpCall (Indirect fOp) argOps)
                        pure (OpVar result)

    -- Superposition
    C.CSup _ a b elemTy -> do
        aOp <- lowerTerm env a
        bOp <- lowerTerm env b
        result <- emitLetTmp (tupleType [elemTy, elemTy]) (OpMakeTuple [aOp, bOp])
        pure (OpVar result)

    -- Duplication
    C.CDup name ty label val body -> do
        valOp <- lowerTerm env val
        -- Note: Alloc analysis stores kind under name.0/name.1, so look up projection
        let valKind = getAllocKind (name ++ ".0") env
            canElide = canElideClone name (leEscapeInfo env)
            isErasure = "era_" `isPrefixOf` name
        case valKind of
            StackOnly -> do
                let env' = extendOperand (name ++ ".0") valOp $ extendOperand (name ++ ".1") valOp env
                lowerTerm env' body
            MaybeHeap
                | isErasure -> do
                    emitEffect (EffDrop valOp)
                    lowerTerm env body
                | canElide -> do
                    let env' = extendOperand (name ++ ".0") valOp $ extendOperand (name ++ ".1") valOp env
                    lowerTerm env' body
                | isClosureType ty -> do
                    let valName = case val of
                            C.CVar n _ -> Just n
                            C.CDp0 n _ -> Just (n ++ ".0")
                            C.CDp1 n _ -> Just (n ++ ".1")
                            _ -> Nothing
                        slotInfo = fromMaybe [] (valName >>= (`lookupClosureSlotTypes` env))
                        envSize = fromMaybe 0 (valName >>= (`lookupClosureEnvSize` env))
                        -- Estimate work for parallel reduction decision
                        workEstimate = estimateWorkFromType ty envSize slotInfo
                        useParallel = shouldUseParallel workEstimate
                    supHandle <- emitLetTmp ty (OpDupClosure label valOp slotInfo)
                    -- Use parallel projections when work estimate is high enough
                    proj0 <-
                        emitLetTmp ty
                            $ if useParallel
                                then OpParClosureProj0 (OpVar supHandle) envSize slotInfo workEstimate
                                else OpDupClosureProj0 (OpVar supHandle) envSize slotInfo
                    proj1 <-
                        emitLetTmp ty
                            $ if useParallel
                                then OpParClosureProj1 (OpVar supHandle) envSize slotInfo workEstimate
                                else OpDupClosureProj1 (OpVar supHandle) envSize slotInfo
                    let env' =
                            markAsCloned (name ++ ".1")
                                $ recordClosureSlotTypes (name ++ ".0") slotInfo
                                $ recordClosureSlotTypes (name ++ ".1") slotInfo
                                $ recordClosureEnvSize (name ++ ".0") envSize
                                $ recordClosureEnvSize (name ++ ".1") envSize
                                $ extendOperand (name ++ ".0") (OpVar proj0)
                                $ extendOperand (name ++ ".1") (OpVar proj1) env
                    lowerTerm env' body
                | otherwise -> do
                    -- Non-closure heap types: use generic DUP with parallel support
                    let workEstimate = 20 -- Base work for non-closure heap values
                        useParallel = shouldUseParallel workEstimate
                    supHandle <- emitLetTmp ty (OpDup label valOp)
                    proj0 <-
                        emitLetTmp ty
                            $ if useParallel
                                then OpParProj0 (OpVar supHandle) workEstimate
                                else OpDupProj0 (OpVar supHandle)
                    proj1 <-
                        emitLetTmp ty
                            $ if useParallel
                                then OpParProj1 (OpVar supHandle) workEstimate
                                else OpDupProj1 (OpVar supHandle)
                    let env' =
                            extendOperand (name ++ ".0") (OpVar proj0)
                                $ extendOperand (name ++ ".1") (OpVar proj1) env
                    lowerTerm env' body

    -- Projections
    C.CDp0 name _ ->
        case lookupOperand (name ++ ".0") env of
            Just op -> pure op
            Nothing -> error $ "Circuit.ToAlloy: unbound projection: " ++ name ++ ".0"
    C.CDp1 name _ ->
        case lookupOperand (name ++ ".1") env of
            Just op -> pure op
            Nothing -> error $ "Circuit.ToAlloy: unbound projection: " ++ name ++ ".1"
    -- Tagged values (constructors)
    C.CTag tag fields resultTy -> do
        fieldOps <- mapM (lowerTerm env) fields
        result <- emitLetTmp resultTy (OpConstruct "Tag" tag fieldOps)
        pure (OpVar result)

    -- Case expressions
    C.CCase scrut arms mdef resultTy -> do
        scrutOp <- lowerTerm env scrut
        let scrutTy = C.getTermType scrut
        tagName <- emitLetTmp scrutTy (OpTagOf scrutOp)
        joinBlock <- freshBlockName
        resultName <- freshName
        armBlocks <- forM arms $ \(tag, boundNamesWithTypes, body) ->
            (tag,,boundNamesWithTypes,body) <$> freshBlockName
        defBlockM <- forM mdef $ \defBody -> (,defBody) <$> freshBlockName
        let switchArms = [(tag, blockName) | (tag, blockName, _, _) <- armBlocks]
            defTarget = fmap fst defBlockM
        terminate (ASwitch (OpVar tagName) switchArms defTarget)
        forM_ armBlocks $ \(_, blockName, boundNamesWithTypes, body) -> do
            beginBlock blockName []
            fieldBindings <- forM (zip [1 ..] boundNamesWithTypes) $ \(idx, (boundName, fieldTy)) -> do
                fieldName <- emitLetTmp fieldTy (OpProject scrutOp idx)
                when ("era_" `isPrefixOf` boundName && getAllocKind "scrut" env == MaybeHeap)
                    $ emitEffect (EffDrop (OpVar fieldName))
                pure (boundName, OpVar fieldName)
            let env' = foldr (uncurry extendOperand) env fieldBindings
            result <- lowerTerm env' body
            terminate (ABr joinBlock [result])
        forM_ defBlockM $ \(defBlock, defBody) -> do
            beginBlock defBlock []
            result <- lowerTerm env defBody
            terminate (ABr joinBlock [result])
        beginBlock joinBlock [(resultName, resultTy)]
        pure (OpVar resultName)

    -- Operations
    C.CBinOp op a b -> do
        aOp <- lowerTerm env a
        bOp <- lowerTerm env b
        let alloyOp = case op of
                C.OpAdd -> IAdd
                C.OpSub -> ISub
                C.OpMul -> IMul
                C.OpDiv -> IDiv
                C.OpMod -> IMod
                C.OpAnd -> And
                C.OpOr -> Or
                C.OpXor -> Xor
                C.OpShl -> Shl
                C.OpShr -> LShr
        let resultTy = C.getTermType term
        result <- emitLetTmp resultTy (OpBin alloyOp aOp bOp)
        pure (OpVar result)
    C.CCmpOp op a b -> do
        aOp <- lowerTerm env a
        bOp <- lowerTerm env b
        let alloyCmp = case op of
                C.OpEq -> CEq
                C.OpNe -> CNe
                C.OpLt -> CSlt
                C.OpLe -> CSle
                C.OpGt -> CSgt
                C.OpGe -> CSge
        let resultTy = C.getTermType term
        result <- emitLetTmp resultTy (OpCmp alloyCmp aOp bOp)
        pure (OpVar result)
    C.CUnaryOp op a -> do
        aOp <- lowerTerm env a
        let alloyOp = case op of C.OpNot -> Not; C.OpNeg -> Neg
        let resultTy = C.getTermType term
        result <- emitLetTmp resultTy (OpUnary alloyOp aOp)
        pure (OpVar result)

    -- Closure environment access
    C.CClosureGetEnv closure idx ty -> do
        closureOp <- lowerTerm env closure
        result <- emitLetTmp ty (OpClosureGetEnv closureOp idx)
        pure (OpVar result)

    -- Field projection from tagged values
    C.CProject expr idx ty -> do
        exprOp <- lowerTerm env expr
        -- OpProject uses 1-based indexing for fields (0 is tag)
        result <- emitLetTmp ty (OpProject exprOp (idx + 1))
        pure (OpVar result)

    -- Panic: emit call to soma_panic and unreachable
    C.CPanic msg ty -> do
        result <- emitLetTmp ty (OpPanic msg)
        pure (OpVar result)

    -- Fork: spawn a parallel task
    -- Use collectArgs to extract the function and all arguments from curried applications
    -- e.g., ((computeLevel 5) 8) becomes (computeLevel, [5, 8])
    C.CFork taskName ty comp body -> do
        let (fun, args) = collectArgs comp
        case fun of
            C.CRef fnName _ | not (null args) -> do
                -- Direct function reference with arguments - can be forked
                argOps <- mapM (lowerTerm env) args
                taskHandle <- emitLetTmp ty (OpFork (OpVar fnName) argOps)
                -- Store the task handle under a special name to mark it as a real fork
                let forkMarker = "_forked_" ++ taskName
                let env' =
                        extendOperand taskName (OpVar forkMarker)
                            $ extendOperand forkMarker (OpVar taskHandle) env
                lowerTerm env' body
            C.CVar fnName _ | not (null args) -> do
                -- Variable reference (could be local function) with arguments
                argOps <- mapM (lowerTerm env) args
                taskHandle <- emitLetTmp ty (OpFork (OpVar fnName) argOps)
                let forkMarker = "_forked_" ++ taskName
                let env' =
                        extendOperand taskName (OpVar forkMarker)
                            $ extendOperand forkMarker (OpVar taskHandle) env
                lowerTerm env' body
            _ -> do
                -- Not a simple function call - compute sequentially
                compOp <- lowerTerm env comp
                let env' = extendOperand taskName compOp env
                lowerTerm env' body

    -- Join: wait for a forked task and get result
    -- If the task was forked (OpFork was emitted), call soma_join
    -- If the task was computed sequentially (fallback), just return the value
    C.CJoin taskName ty -> do
        case lookupOperand taskName env of
            Just taskOp -> do
                -- Check if this is a real fork by looking for the marker
                let forkMarker = "_forked_" ++ taskName
                case lookupOperand forkMarker env of
                    Just taskHandleOp -> do
                        -- This came from OpFork - emit OpJoin to wait for the task
                        result <- emitLetTmp ty (OpJoin taskHandleOp)
                        pure (OpVar result)
                    Nothing -> do
                        -- Sequential fallback - the value is already computed
                        pure taskOp
            Nothing -> error $ "CJoin: unknown task " ++ taskName
  where
    countArityFromType :: Type -> Int
    countArityFromType (TArrow _ rest) = 1 + countArityFromType rest
    countArityFromType _ = 0

    -- Helper to collect function and arguments from nested CApp
    collectArgs :: C.CTerm -> (C.CTerm, [C.CTerm])
    collectArgs (C.CApp f x _) =
        let (fun, args) = collectArgs f
        in (fun, args ++ [x])
    collectArgs other = (other, [])
