{-# LANGUAGE NamedFieldPuns #-}

{- | Function Inlining Pass for Alloy IR

This module provides general-purpose function inlining infrastructure that can be
used for:

1. **User-annotated inline functions**: Functions marked with the `inline` modifier
   are always inlined at call sites.

2. **Closure inlining**: When a closure's target function is known statically and
   the closure is called, we can inline the function body directly, eliminating
   the closure allocation and indirect call overhead.

3. **Small function inlining**: Functions below a certain size threshold can be
   automatically inlined for performance.

The inliner works by:
1. Building a map of inlinable functions
2. Scanning for call sites that reference inlinable functions
3. Replacing the call with a copy of the function body, with appropriate
   variable renaming to avoid capture

Note: This is a conservative inliner that only inlines functions with a single
basic block (no control flow). More sophisticated inlining of multi-block
functions would require additional complexity.
-}
module Alloy.Inline (
    inlineModule,
    inlineFunction,
    InlineConfig (..),
    defaultInlineConfig,
) where

import Alloy.Ir
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Typing.Types (Type)

-- | Configuration for the inliner
data InlineConfig = InlineConfig
    { icInlineFunctions :: !(Set Name)
    -- ^ Functions explicitly marked for inlining (e.g., with `inline` modifier)
    , icMaxInlineSize :: !Int
    -- ^ Maximum number of instructions for auto-inlining (0 = disabled)
    , icInlineClosures :: !Bool
    -- ^ Whether to inline known closure calls
    }
    deriving (Show, Eq)

-- | Default configuration: only inline explicitly marked functions
defaultInlineConfig :: InlineConfig
defaultInlineConfig =
    InlineConfig
        { icInlineFunctions = Set.empty
        , icMaxInlineSize = 0
        , icInlineClosures = True
        }

-- | Information about an inlinable function
data InlinableFunc = InlinableFunc
    { ifParams :: ![(Name, Type)]
    -- ^ Function parameters
    , ifReturnType :: !Type
    -- ^ Return type
    , ifBody :: ![AInstr]
    -- ^ Instructions (must be single-block for now)
    , ifReturnValue :: !(Maybe AOperand)
    -- ^ The returned value (from ARet terminator)
    }
    deriving (Show, Eq)

-- | State for generating fresh names during inlining
data InlineState = InlineState
    { isCounter :: !Int
    -- ^ Counter for generating unique names
    , isFunctionMap :: !(Map Name InlinableFunc)
    -- ^ Map of inlinable functions
    , isClosureTargets :: !(Map Name Name)
    -- ^ Maps closure variables to their target functions
    , isFuncPtrs :: !(Map Name (Name, Name))
    -- ^ Maps func ptr variables to their target functions
    }
    deriving (Show)

-- | Run inlining on an entire module
inlineModule :: InlineConfig -> AlloyModule -> AlloyModule
inlineModule config m@AlloyModule{amFunctions} =
    let funcMap = buildInlinableMap config amFunctions
        fns' = map (inlineFunction config funcMap) amFunctions
    in m{amFunctions = fns'}

-- | Build a map of functions that can be inlined
buildInlinableMap :: InlineConfig -> [AlloyFunction] -> Map Name InlinableFunc
buildInlinableMap config funcs =
    Map.fromList
        [ (afName fn, inlinable)
        | fn <- funcs
        , Just inlinable <- [tryMakeInlinable config fn]
        ]

-- | Try to make a function inlinable (returns Nothing if not eligible)
tryMakeInlinable :: InlineConfig -> AlloyFunction -> Maybe InlinableFunc
tryMakeInlinable config fn@AlloyFunction{afName, afIsInline}
    -- Check if explicitly marked for inlining via IR flag
    | afIsInline = singleBlockInlinable fn
    -- Check if explicitly marked for inlining via config
    | afName `Set.member` icInlineFunctions config = singleBlockInlinable fn
    -- Check if small enough for auto-inlining
    | icMaxInlineSize config > 0 =
        case singleBlockInlinable fn of
            Just inf | length (ifBody inf) <= icMaxInlineSize config -> Just inf
            _ -> Nothing
    -- For closure inlining, we make all single-block functions available
    | icInlineClosures config = singleBlockInlinable fn
    | otherwise = Nothing
  where
    singleBlockInlinable :: AlloyFunction -> Maybe InlinableFunc
    singleBlockInlinable AlloyFunction{afParams = params, afReturnType = retTy, afEntry = entry, afBlocks = blocks} =
        case blocks of
            [ABlock{abName, abParams = [], abInstrs, abTerminator}]
                | abName == entry
                , ARet retVal <- abTerminator ->
                    Just
                        InlinableFunc
                            { ifParams = params
                            , ifReturnType = retTy
                            , ifBody = abInstrs
                            , ifReturnValue = retVal
                            }
            _ -> Nothing

-- | Inline calls within a single function
inlineFunction :: InlineConfig -> Map Name InlinableFunc -> AlloyFunction -> AlloyFunction
inlineFunction config funcMap fn@AlloyFunction{afBlocks} =
    let initialState =
            InlineState
                { isCounter = 0
                , isFunctionMap = funcMap
                , isClosureTargets = Map.empty
                , isFuncPtrs = Map.empty
                }
        (blocks', _) = foldl (processBlock config) ([], initialState) afBlocks
    in fn{afBlocks = reverse blocks'}

-- | Process a single block, inlining calls where appropriate
processBlock :: InlineConfig -> ([ABlock], InlineState) -> ABlock -> ([ABlock], InlineState)
processBlock config (accBlocks, state) block@ABlock{abInstrs} =
    let (instrs', state') = foldl (processInstr config) ([], state) abInstrs
        block' = block{abInstrs = reverse instrs'}
    in (block' : accBlocks, state')

-- | Process a single instruction, potentially inlining calls
processInstr :: InlineConfig -> ([AInstr], InlineState) -> AInstr -> ([AInstr], InlineState)
processInstr config (accInstrs, state) instr =
    case instr of
        -- Track closure allocations (handle both OpVar and direct name references)
        ILet name _ (OpAllocClosure funcOp _ _) ->
            case funcOp of
                OpVar funcName ->
                    let state' = state{isClosureTargets = Map.insert name funcName (isClosureTargets state)}
                    in (instr : accInstrs, state')
                _ -> (instr : accInstrs, state)
        -- Track closure wrapping (preserves target function knowledge)
        ILet name _ (OpWrapClosure (OpVar closureName)) ->
            case Map.lookup closureName (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isClosureTargets = Map.insert name targetFunc (isClosureTargets state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        -- Session 14: Track closure DUP operations (SUP creation preserves target)
        ILet name _ (OpDupClosure _ (OpVar closureName) _) ->
            case Map.lookup closureName (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isClosureTargets = Map.insert name targetFunc (isClosureTargets state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        -- Session 14: Track closure DUP projections (inherit target from SUP)
        ILet name _ (OpDupClosureProj0 (OpVar supHandle) _ _) ->
            case Map.lookup supHandle (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isClosureTargets = Map.insert name targetFunc (isClosureTargets state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        ILet name _ (OpDupClosureProj1 (OpVar supHandle) _ _) ->
            case Map.lookup supHandle (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isClosureTargets = Map.insert name targetFunc (isClosureTargets state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        -- Track generic DUP operations too (for non-closure SUPs that may contain closures)
        ILet name _ (OpDup _ (OpVar valName)) ->
            case Map.lookup valName (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isClosureTargets = Map.insert name targetFunc (isClosureTargets state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        ILet name _ (OpDupProj0 (OpVar supHandle)) ->
            case Map.lookup supHandle (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isClosureTargets = Map.insert name targetFunc (isClosureTargets state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        ILet name _ (OpDupProj1 (OpVar supHandle)) ->
            case Map.lookup supHandle (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isClosureTargets = Map.insert name targetFunc (isClosureTargets state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        -- Session 19: Track parallel projection ops
        ILet name _ (OpParProj0 (OpVar supHandle) _) ->
            case Map.lookup supHandle (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isClosureTargets = Map.insert name targetFunc (isClosureTargets state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        ILet name _ (OpParProj1 (OpVar supHandle) _) ->
            case Map.lookup supHandle (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isClosureTargets = Map.insert name targetFunc (isClosureTargets state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        ILet name _ (OpParClosureProj0 (OpVar supHandle) _ _ _) ->
            case Map.lookup supHandle (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isClosureTargets = Map.insert name targetFunc (isClosureTargets state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        ILet name _ (OpParClosureProj1 (OpVar supHandle) _ _ _) ->
            case Map.lookup supHandle (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isClosureTargets = Map.insert name targetFunc (isClosureTargets state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        -- Track function pointer extractions
        ILet name _ (OpClosureGetFunc (OpVar closureName)) ->
            case Map.lookup closureName (isClosureTargets state) of
                Just targetFunc ->
                    let state' = state{isFuncPtrs = Map.insert name (targetFunc, closureName) (isFuncPtrs state)}
                    in (instr : accInstrs, state')
                Nothing ->
                    (instr : accInstrs, state)
        -- Try to inline direct calls to functions marked for inlining
        ILet resultName resultTy (OpCall (Direct funcName) args) ->
            case Map.lookup funcName (isFunctionMap state) of
                Just inlinable ->
                    -- Function is in the inlinable map (marked inline or meets criteria)
                    -- inlineCall returns instructions in normal order
                    -- We need to recursively process them to handle nested opportunities
                    let (inlinedInstrs, state') = inlineCall state resultName resultTy inlinable args
                        -- Recursively process inlined instructions
                        (processedInstrs, state'') = foldl (processInstr config) (accInstrs, state') inlinedInstrs
                    in (processedInstrs, state'')
                Nothing ->
                    -- Not marked for inlining, keep as-is
                    (instr : accInstrs, state)
        -- Try to inline indirect calls through known closures
        ILet resultName resultTy (OpCall (Indirect (OpVar funcPtrName)) args)
            | icInlineClosures config ->
                case Map.lookup funcPtrName (isFuncPtrs state) of
                    Just (targetFunc, _) ->
                        case Map.lookup targetFunc (isFunctionMap state) of
                            Just inlinable ->
                                let (inlinedInstrs, state') = inlineCall state resultName resultTy inlinable args
                                    -- Recursively process inlined instructions
                                    (processedInstrs, state'') = foldl (processInstr config) (accInstrs, state') inlinedInstrs
                                in (processedInstrs, state'')
                            Nothing ->
                                (instr : accInstrs, state)
                    Nothing ->
                        (instr : accInstrs, state)
        -- Pass through other instructions
        _ ->
            (instr : accInstrs, state)

-- | Inline a function call, returning the replacement instructions
inlineCall :: InlineState -> Name -> Type -> InlinableFunc -> [AOperand] -> ([AInstr], InlineState)
inlineCall state resultName resultTy InlinableFunc{ifParams, ifBody, ifReturnValue} args =
    let
        -- Build substitution from parameters to arguments
        paramSubst = Map.fromList (zip (map fst ifParams) args)
        -- Generate fresh names for all let-bound variables in the body
        bodyNames = [n | ILet n _ _ <- ifBody]

        -- Find which body variable is returned (if any)
        returnedBodyVar = case ifReturnValue of
            Just (OpVar v) -> if v `elem` bodyNames then Just v else Nothing
            _ -> Nothing

        -- Generate fresh names, but use resultName for the returned variable
        (freshNames, counter') = generateFreshNamesExcept (isCounter state) bodyNames returnedBodyVar resultName
        nameSubst = Map.fromList (zip bodyNames (map OpVar freshNames))
        -- Combined substitution
        fullSubst = Map.union nameSubst paramSubst
        -- Rename instructions - process each instruction individually
        -- We need to track which let-binding we're on since effects don't have names
        renamedInstrs = renameInstrs fullSubst freshNames ifBody
        -- Handle return value - if return is a constant or parameter, we need extra instruction
        finalInstrs = case ifReturnValue of
            Just retOp ->
                case returnedBodyVar of
                    Just _ ->
                        -- Return value is a body variable, already renamed to resultName
                        renamedInstrs
                    Nothing ->
                        -- Return value is a constant or parameter, need to bind it
                        let retOp' = substOperand fullSubst retOp
                        in case retOp' of
                            OpConst c ->
                                ILet resultName resultTy (constOp c) : renamedInstrs
                            OpVar _ ->
                                -- It's a parameter reference, create identity binding
                                ILet resultName resultTy (identityOp retOp') : renamedInstrs
            Nothing ->
                renamedInstrs
        state' = state{isCounter = counter'}
    in
        (finalInstrs, state')

-- | Rename instructions, consuming fresh names only for ILet instructions
renameInstrs :: Map Name AOperand -> [Name] -> [AInstr] -> [AInstr]
renameInstrs _ _ [] = []
renameInstrs subst freshNames (instr : rest) =
    case instr of
        ILet _oldName ty op ->
            case freshNames of
                (newName : remainingNames) ->
                    ILet newName ty (substOp subst op) : renameInstrs subst remainingNames rest
                [] ->
                    -- This shouldn't happen if bodyNames was computed correctly
                    error "Alloy.Inline: ran out of fresh names"
        IEffect eff ->
            -- Effects don't consume fresh names, just substitute operands
            IEffect (substEffect subst eff) : renameInstrs subst freshNames rest

-- | Generate fresh names for a list of names, except use resultName for the returned var
generateFreshNamesExcept :: Int -> [Name] -> Maybe Name -> Name -> ([Name], Int)
generateFreshNamesExcept counter names returnedVar resultName =
    let makeFreshName (name, i) =
            if Just name == returnedVar
                then resultName
                else name ++ "_inl" ++ show (counter + i)
        freshNames = [makeFreshName (name, i) | (name, i) <- zip names [0 ..]]
    in (freshNames, counter + length names)

-- | Substitute operands in an operation
substOp :: Map Name AOperand -> AOp -> AOp
substOp subst op =
    case op of
        OpBin k a b -> OpBin k (substOperand subst a) (substOperand subst b)
        OpUnary k a -> OpUnary k (substOperand subst a)
        OpCmp k a b -> OpCmp k (substOperand subst a) (substOperand subst b)
        OpLoad a -> OpLoad (substOperand subst a)
        OpAllocStack t -> OpAllocStack t
        OpAllocHeap t -> OpAllocHeap t
        OpCall callee args -> OpCall (substCallable subst callee) (map (substOperand subst) args)
        OpConstruct tn tag fields -> OpConstruct tn tag (map (substOperand subst) fields)
        OpTagOf a -> OpTagOf (substOperand subst a)
        OpProject a i -> OpProject (substOperand subst a) i
        OpIndex a i -> OpIndex (substOperand subst a) (substOperand subst i)
        OpMakeArray xs -> OpMakeArray (map (substOperand subst) xs)
        OpMakeTuple xs -> OpMakeTuple (map (substOperand subst) xs)
        OpGetDict className ty -> OpGetDict className ty
        OpDictCall dict methodIdx method args ->
            OpDictCall (substOperand subst dict) methodIdx method (map (substOperand subst) args)
        OpDup label val -> OpDup label (substOperand subst val)
        OpDupProj0 handle -> OpDupProj0 (substOperand subst handle)
        OpDupProj1 handle -> OpDupProj1 (substOperand subst handle)
        OpWrapClosure fn -> OpWrapClosure (substOperand subst fn)
        OpAllocClosure fn arity envSz -> OpAllocClosure (substOperand subst fn) arity envSz
        OpClosureSetEnv closure idx val ->
            OpClosureSetEnv (substOperand subst closure) idx (substOperand subst val)
        OpClosureGetEnv closure idx -> OpClosureGetEnv (substOperand subst closure) idx
        OpClosureGetFunc closure -> OpClosureGetFunc (substOperand subst closure)
        -- Session 13: specialized closure duplication ops
        OpDupClosure label closure slotInfo -> OpDupClosure label (substOperand subst closure) slotInfo
        OpDupClosureProj0 handle envSz slotInfo -> OpDupClosureProj0 (substOperand subst handle) envSz slotInfo
        OpDupClosureProj1 handle envSz slotInfo -> OpDupClosureProj1 (substOperand subst handle) envSz slotInfo
        OpClosureGetEnvDirect closure idx -> OpClosureGetEnvDirect (substOperand subst closure) idx
        OpClosureGetEnvSUP closure idx -> OpClosureGetEnvSUP (substOperand subst closure) idx
        -- Session 19: parallel projection ops
        OpParProj0 handle workEst -> OpParProj0 (substOperand subst handle) workEst
        OpParProj1 handle workEst -> OpParProj1 (substOperand subst handle) workEst
        OpParClosureProj0 handle envSz slotInfo workEst -> OpParClosureProj0 (substOperand subst handle) envSz slotInfo workEst
        OpParClosureProj1 handle envSz slotInfo workEst -> OpParClosureProj1 (substOperand subst handle) envSz slotInfo workEst
        OpPanic msg -> OpPanic msg
        -- Session 27: graph reduction ops
        OpGraphInit n -> OpGraphInit n
        OpGraphShutdown -> OpGraphShutdown
        OpGraphNum v -> OpGraphNum (substOperand subst v)
        OpGraphAdd l r -> OpGraphAdd (substOperand subst l) (substOperand subst r)
        OpGraphSub l r -> OpGraphSub (substOperand subst l) (substOperand subst r)
        OpGraphMul l r -> OpGraphMul (substOperand subst l) (substOperand subst r)
        OpGraphCall fnIdx args -> OpGraphCall fnIdx (map (substOperand subst) args)
        OpGraphReduce root -> OpGraphReduce (substOperand subst root)
        OpGraphExtractNum term -> OpGraphExtractNum (substOperand subst term)
        OpGraphRegisterFunc name arity impl -> OpGraphRegisterFunc name arity (substOperand subst impl)
        -- Session 29: interaction net operations
        OpGraphDup label target -> OpGraphDup label (substOperand subst target)
        OpGraphSup label l r -> OpGraphSup label (substOperand subst l) (substOperand subst r)
        OpGraphLam varSlot body -> OpGraphLam (substOperand subst varSlot) (substOperand subst body)
        OpGraphApp fn arg -> OpGraphApp (substOperand subst fn) (substOperand subst arg)
        OpGraphEra -> OpGraphEra
        OpGraphRef name arg -> OpGraphRef name (substOperand subst arg)
        OpGraphDupProj0 target -> OpGraphDupProj0 (substOperand subst target)
        OpGraphDupProj1 target -> OpGraphDupProj1 (substOperand subst target)

-- | Substitute operands in an effect
substEffect :: Map Name AOperand -> AEffect -> AEffect
substEffect subst eff =
    case eff of
        EffStore p v -> EffStore (substOperand subst p) (substOperand subst v)
        EffStoreIndex a i v ->
            EffStoreIndex (substOperand subst a) (substOperand subst i) (substOperand subst v)
        EffDrop a -> EffDrop (substOperand subst a)
        EffClosureSetEnv closure idx val ->
            EffClosureSetEnv (substOperand subst closure) idx (substOperand subst val)
        EffGraphInit n -> EffGraphInit n
        EffGraphShutdown -> EffGraphShutdown
        EffGraphRegisterFunc name arity impl -> EffGraphRegisterFunc name arity (substOperand subst impl)

-- | Substitute an operand
substOperand :: Map Name AOperand -> AOperand -> AOperand
substOperand subst (OpVar n) = Map.findWithDefault (OpVar n) n subst
substOperand _ c@(OpConst _) = c

-- | Substitute in a callable
substCallable :: Map Name AOperand -> ACallable -> ACallable
substCallable _ (Direct n) = Direct n
substCallable subst (Indirect op) = Indirect (substOperand subst op)

-- | Create an identity operation for a variable (x + 0 for Int)
identityOp :: AOperand -> AOp
identityOp op = OpBin IAdd op (OpConst (CInt 0))

-- | Create an operation from a constant
constOp :: AConst -> AOp
constOp (CInt i) = OpBin IAdd (OpConst (CInt i)) (OpConst (CInt 0))
constOp (CBool b) = OpBin And (OpConst (CBool b)) (OpConst (CBool True))
constOp (CString _) = OpMakeArray [] -- Placeholder - string constants need special handling
constOp CUnit = OpMakeTuple []
