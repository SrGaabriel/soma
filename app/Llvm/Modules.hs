module Llvm.Modules where
import Llvm.Values (LlvmValue)
import Llvm.Types (LlvmType)
import Llvm.Instructions (LlvmStatement)
import Data.Map (Map)

data LlvmFunction = LlvmFunction
  { functionName :: String
  , functionParams :: [LlvmValue]
  , functionReturnType :: LlvmType
  , functionBlocks :: Map String LlvmBlock
  , functionStatements :: [LlvmStatement]
  } deriving (Show)

data LlvmBlock = LlvmBlock
  { blockName :: String
  , blockStatements :: [LlvmStatement]
  } deriving (Show)