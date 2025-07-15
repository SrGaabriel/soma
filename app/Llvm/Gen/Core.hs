module Llvm.Gen.Core where

import Control.Monad.State (State, gets, modify)
import Llvm.Modules (LlvmFunction (..), LlvmBlock (LlvmBlock))
import Llvm.Instructions (LlvmStatement (..), LlvmInstruction (..))
import Llvm.Values (LlvmValue (..), getRegName)
import Llvm.Types (LlvmType (..))
import Data.Map (Map)
import qualified Data.Map as Map
import Inference.Core (TypeMap)

data IrGenState = IrGenState
  { nextRegister :: Int
  , nextBlock :: Int
  , typeMap :: TypeMap
  , currentBlock :: Maybe String
  , functions :: Map String LlvmFunction
  , currentFunction :: Maybe String
  , memoryReferences :: Map String (Map String LlvmValue)
  , statements :: [LlvmStatement]
  } deriving (Show)

type IrGen = State IrGenState

freshReg :: LlvmType -> IrGen LlvmValue
freshReg ty = do
  n <- gets nextRegister
  modify $ \s -> s { nextRegister = n + 1 }
  return $ LlvmRegister ty ("reg_" ++ show n)

emit :: LlvmStatement -> IrGen ()
emit stmt = modify $ \s -> s { statements = stmt : statements s }

addInstr :: LlvmValue -> LlvmValue -> IrGen LlvmValue
addInstr left right = do
  result <- freshReg LlvmI32
  emit $ LlvmAssign (getRegName result) (LlvmAdd left right)
  return result

callInstr :: String -> [LlvmValue] -> LlvmType -> IrGen LlvmValue
callInstr name args retType = do
  result <- freshReg retType
  emit $ LlvmAssign (getRegName result) (LlvmCall name args)
  return result

insertMemory :: String -> String -> LlvmValue -> IrGen ()
insertMemory scope name value = do
  refs <- gets memoryReferences
  let scopeMap = Map.findWithDefault Map.empty scope refs
  let newScopeMap = Map.insert name value scopeMap
  modify $ \s -> s { memoryReferences = Map.insert scope newScopeMap refs }

lookupMemory :: String -> String -> IrGen (Maybe LlvmValue)
lookupMemory scope name = do
  refs <- gets memoryReferences
  return $ Map.lookup scope refs >>= Map.lookup name

createBlock :: IrGen String
createBlock = do
  n <- gets nextBlock
  modify $ \s -> s { nextBlock = n + 1 }
  let blockName = "block_" ++ show n
  currentFunc <- gets currentFunction
  case currentFunc of
    Just funcName -> do
      funcs <- gets functions
      case Map.lookup funcName funcs of
        Just func -> do
          let newBlock = LlvmBlock blockName []
          let updatedFunc = func { functionBlocks = Map.insert blockName newBlock (functionBlocks func) }
          modify $ \s -> s { functions = Map.insert funcName updatedFunc funcs }
        Nothing -> return ()
    Nothing -> return ()
  return blockName

switchToBlock :: String -> IrGen ()
switchToBlock blockName = modify $ \s -> s { currentBlock = Just blockName }

branch :: String -> IrGen ()
branch blockName = emit $ LlvmBr blockName

branchCond :: LlvmValue -> String -> String -> IrGen ()
branchCond cond trueBlock falseBlock = 
  emit $ LlvmBrCond cond trueBlock falseBlock