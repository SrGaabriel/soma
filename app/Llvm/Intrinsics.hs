module Llvm.Intrinsics where

import qualified Data.Map as Map
import Llvm.Instructions (LlvmInstruction (..))
import Llvm.Values (LlvmValue (..), getValueType)

type IntrinsicRegistry = Map.Map String IntrinsicImpl

data IntrinsicImpl = IntrinsicImpl
    { intrinsicName :: String
    , intrinsicCodeGen :: [LlvmValue] -> LlvmInstruction
    }

createIntrinsicRegistry :: IntrinsicRegistry
createIntrinsicRegistry = Map.fromList
    [ ("+", addIntIntrinsic)
    , ("==", eqIntIntrinsic)
    ]

addIntIntrinsic :: IntrinsicImpl
addIntIntrinsic = IntrinsicImpl
    { intrinsicName = "+"
    , intrinsicCodeGen = \args -> case args of
        [lhs, rhs] -> 
            let lhsType = getValueType lhs
            in LlvmAdd lhsType lhs rhs
        _ -> error "add_int intrinsic expects exactly 2 arguments"
    }

eqIntIntrinsic :: IntrinsicImpl
eqIntIntrinsic = IntrinsicImpl
    { intrinsicName = "=="
    , intrinsicCodeGen = \args -> case args of
        [lhs, rhs] -> 
            let lhsType = getValueType lhs
            in LlvmICmpEq lhsType lhs rhs
        _ -> error "eq_int intrinsic expects exactly 2 arguments"
    }

isIntrinsic :: IntrinsicRegistry -> String -> Bool
isIntrinsic registry name = Map.member name registry

getIntrinsicNames :: IntrinsicRegistry -> [String]
getIntrinsicNames = Map.keys

getIntrinsic :: String -> IntrinsicImpl
getIntrinsic "==" = eqIntIntrinsic
getIntrinsic "+" = addIntIntrinsic
getIntrinsic u = error $ "Unknown intrinsic function: " ++ u