{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Llvm.Gen.Intrinsics where

import Control.Monad.State (modify)
import Llvm.Dependencies (LlvmDependency (..))
import Llvm.Gen.Core (IrGen, IrGenState (irDependencies))
import Llvm.Instructions (LlvmInstruction (..))
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..))
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Gen.Context (GenValue (..), getGenValueType)

data IntrinsicImpl = IntrinsicImpl
    { intrinsicName :: String
    , intrinsicCodeGen :: [GenValue] -> IrGen LlvmInstruction
    }

addIntIntrinsic :: IntrinsicImpl
addIntIntrinsic =
    IntrinsicImpl
        { intrinsicName = "+"
        , intrinsicCodeGen = \case
            [lhs, rhs] ->
                let lhsType = getGenValueType lhs
                in pure $ LlvmAdd lhsType (gvw lhs) (gvw rhs)
            _ -> error "add_int intrinsic expects exactly 2 arguments"
        }

eqIntIntrinsic :: IntrinsicImpl
eqIntIntrinsic =
    IntrinsicImpl
        { intrinsicName = "=="
        , intrinsicCodeGen = \case
            [lhs, rhs] ->
                let lhsType = getGenValueType lhs
                in pure $ LlvmICmpEq lhsType (gvw lhs) (gvw rhs)
            _ -> error "eq_int intrinsic expects exactly 2 arguments"
        }

printIntrinsic :: IntrinsicImpl
printIntrinsic =
    IntrinsicImpl
        { intrinsicName = "print"
        , intrinsicCodeGen = \case
            [arg] -> do
                modify $ \state -> state{irDependencies = printfDependency : irDependencies state}
                pure $ LlvmCall (LlvmGlobal LlvmFn "printf") LlvmI32 [gvw arg]
            _ -> error "print intrinsic expects exactly 1 argument"
        }

printlnIntrinsic :: IntrinsicImpl
printlnIntrinsic =
    IntrinsicImpl
        { intrinsicName = "println"
        , intrinsicCodeGen = \case
            [arg] -> do
                case getGenValueType arg of
                    LlvmPointer LlvmI8 -> do
                        modify $ \state -> state{irDependencies = putsDependency : irDependencies state}
                        pure $ LlvmCall (LlvmGlobal LlvmFn "puts") LlvmI32 [gvw arg]
                    LlvmI32 -> do
                        formatStr <- newStrTemplate "%d\\0A" 3
                        modify $ \state -> state{irDependencies = printfDependency : irDependencies state}
                        pure $ LlvmCall (LlvmGlobal LlvmFn "printf") LlvmI32 [formatStr, gvw arg]
                    u -> error $ "println intrinsic does not support type: " ++ show u
            _ -> error "print intrinsic expects exactly 1 argument"
        }

getIntrinsic :: String -> IntrinsicImpl
getIntrinsic "==" = eqIntIntrinsic
getIntrinsic "+" = addIntIntrinsic
getIntrinsic "print" = printIntrinsic
getIntrinsic "println" = printlnIntrinsic
getIntrinsic u = error $ "Unknown intrinsic function: " ++ u

printfDependency :: LlvmDependency
printfDependency = LlvmFunctionDependency "printf" LlvmI32 [LlvmPointer LlvmI8, LlvmVararg]

putsDependency :: LlvmDependency
putsDependency = LlvmFunctionDependency "puts" LlvmI32 [LlvmPointer LlvmI8]
