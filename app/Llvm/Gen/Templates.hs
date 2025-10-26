module Llvm.Gen.Templates where
import Llvm.Gen.Core (IrGen, IrGenState (..), saveInstruction)
import Llvm.Dependencies (LlvmDependency(..), LinkageType (..))
import Llvm.Values (LlvmValue (..), intLiteral)
import Data.Hashable (Hashable(hash))
import Llvm.Types (LlvmType(..))
import Control.Monad.State (modify)
import Llvm.Instructions (LlvmInstruction(..))
import Llvm.Gen.Context (GenValue, mkGlobalConstantAccess)

newStrTemplate :: String -> Int -> IrGen GenValue
newStrTemplate str lengthWithoutEndingChar = do
    let dpName = "str_" ++ show (hash str)
    let depType = LlvmArray (lengthWithoutEndingChar + 1) LlvmI8
    let dependency =
            LlvmConstantDependency
                { constantName = dpName
                , constantValue = LlvmLiteral depType ("c\"" ++ str ++ "\00\"")
                , constantLinkage = Just PrivateLinkage
                }
    modify $ \s -> s{irDependencies = dependency : irDependencies s}
    
    let ptrInstr = LlvmGetElementPtr depType (LlvmGlobal depType dpName) [intLiteral 0, intLiteral 0] True
    mkGlobalConstantAccess dpName depType [0, 0] True <$> saveInstruction ptrInstr (LlvmPointer LlvmI8)