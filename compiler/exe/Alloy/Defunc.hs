{-# LANGUAGE NamedFieldPuns #-}

{- | Enhanced Defunctionalization / Closure Optimization Pass

This module performs closure-related optimizations on Alloy IR:

1. **Known Function Devirtualization**: Convert indirect calls to direct calls
   when the callee is a known function name.

2. **Closure Tracking**: Track which variables hold closures with known
   underlying functions (from OpAllocClosure).

3. **Closure Call Devirtualization**: When calling through a closure whose
   underlying function is known, replace:
   @
   t0 = closure_get_func closure
   t1 = *t0(closure, args...)
   @
   With:
   @
   t1 = lambda$N(closure, args...)  -- direct call
   @

4. **Func Ptr Tracking**: Track which variables hold function pointers
   extracted from known closures, enabling devirtualization even when
   the call is separated from the closure_get_func.

These optimizations eliminate indirect call overhead for closures when
the target function is statically determinable.
-}
module Alloy.Defunc (
    defunctionalizeModule,
    defunctionalizeFunction,
) where

import Alloy.Ir
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- | Information about a known closure
data ClosureInfo = ClosureInfo
    { ciTargetFunc :: !Name
    -- ^ The underlying lifted function (e.g., "lambda$0")
    , ciEnvSize :: !Int
    -- ^ Number of captured environment values
    }
    deriving (Show, Eq)

-- | Optimization environment tracking known values
data OptEnv = OptEnv
    { oeKnownFunctions :: !(Set Name)
    -- ^ Set of all function names in the module
    , oeClosures :: !(Map Name ClosureInfo)
    -- ^ Variables known to hold closures with specific underlying functions
    , oeFuncPtrs :: !(Map Name Name)
    {- ^ Variables holding function pointers extracted from known closures
    Maps: func_ptr_var -> target_function_name
    -}
    }
    deriving (Show)

emptyEnv :: Set Name -> OptEnv
emptyEnv knownFns =
    OptEnv
        { oeKnownFunctions = knownFns
        , oeClosures = Map.empty
        , oeFuncPtrs = Map.empty
        }

defunctionalizeModule :: AlloyModule -> AlloyModule
defunctionalizeModule m@AlloyModule{amFunctions} =
    let fnNames = Set.fromList (map afName amFunctions)
    in m{amFunctions = map (defunctionalizeFunction fnNames) amFunctions}

defunctionalizeFunction :: Set Name -> AlloyFunction -> AlloyFunction
defunctionalizeFunction knownFns fn@AlloyFunction{afBlocks} =
    let env = emptyEnv knownFns
        -- Process blocks in order, threading the environment
        -- Note: This is a simplified single-pass approach. For full dataflow
        -- analysis across branches, we'd need a proper fixpoint algorithm.
        (blocks', _) = foldl processBlock ([], env) afBlocks
    in fn{afBlocks = reverse blocks'}

processBlock :: ([ABlock], OptEnv) -> ABlock -> ([ABlock], OptEnv)
processBlock (accBlocks, env) block@ABlock{abInstrs, abTerminator} =
    let (instrs', env') = foldl processInstr ([], env) abInstrs
        term' = rewriteTerm env' abTerminator
        block' = block{abInstrs = reverse instrs', abTerminator = term'}
    in (block' : accBlocks, env')

processInstr :: ([AInstr], OptEnv) -> AInstr -> ([AInstr], OptEnv)
processInstr (accInstrs, env) instr =
    case instr of
        ILet name ty op ->
            let (op', env') = rewriteOp env name op
            in (ILet name ty op' : accInstrs, env')
        IEffect eff ->
            (IEffect eff : accInstrs, env)

rewriteOp :: OptEnv -> Name -> AOp -> (AOp, OptEnv)
rewriteOp env resultName op =
    case op of
        -- Track closure allocations
        OpAllocClosure (OpVar funcName) _arity envSize ->
            let info = ClosureInfo funcName envSize
                env' = env{oeClosures = Map.insert resultName info (oeClosures env)}
            in (op, env')
        -- Track function pointer extractions from known closures
        OpClosureGetFunc (OpVar closureName) ->
            case Map.lookup closureName (oeClosures env) of
                Just (ClosureInfo targetFunc _) ->
                    -- We know this func ptr points to targetFunc
                    let env' = env{oeFuncPtrs = Map.insert resultName targetFunc (oeFuncPtrs env)}
                    in (op, env')
                Nothing ->
                    (op, env)
        -- Devirtualize indirect calls
        OpCall (Indirect funcPtrOp) args ->
            case funcPtrOp of
                OpVar funcPtrName ->
                    -- Check if this func ptr was extracted from a known closure
                    case Map.lookup funcPtrName (oeFuncPtrs env) of
                        Just targetFunc ->
                            -- Devirtualize: indirect call -> direct call
                            (OpCall (Direct targetFunc) args, env)
                        Nothing ->
                            -- Check if it's a known function name directly
                            if funcPtrName `Set.member` oeKnownFunctions env
                                then (OpCall (Direct funcPtrName) args, env)
                                else (op, env)
                _ -> (op, env)
        -- Pass through other operations unchanged
        _ -> (op, env)

rewriteTerm :: OptEnv -> ATerminator -> ATerminator
rewriteTerm _ t = t
