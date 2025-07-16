{-# LANGUAGE FlexibleContexts #-}
module Llvm.Gen.Core where

import Control.Monad.Reader
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Inference.Core (TypeMap)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..), getRegName)
import Control.Monad.Writer

data IrGenEnv = IrGenEnv
    { currentScope :: MemoryScope
    , currentFunction :: Maybe String
    }

data IrGenState = IrGenState
    { nextRegister :: Int
    , nextBlock :: Int
    , typeMap :: TypeMap
    , currentBlock :: Maybe String
    }
    deriving (Show)

globalDefaultState :: IrGenState
globalDefaultState = IrGenState
    { nextRegister = 0
    , nextBlock = 0
    , typeMap = Map.empty
    , currentBlock = Nothing
    }

globalDefaultEnv :: IrGenEnv
globalDefaultEnv = IrGenEnv
    { currentScope = MemoryScope
        { blockName = "global"
        , blockValues = Map.empty
        , blockParent = Nothing
        }
    , currentFunction = Nothing
    }

type IrGen = ReaderT IrGenEnv (WriterT [LlvmStatement] (State IrGenState))

runIrGen :: IrGenEnv -> IrGenState -> IrGen a -> ((a, [LlvmStatement]), IrGenState)
runIrGen env st action =
  runState (runWriterT (runReaderT action env)) st

freshReg :: LlvmType -> IrGen LlvmValue
freshReg ty = do
    n <- gets nextRegister
    modify $ \s -> s { nextRegister = n + 1 }
    return $ LlvmRegister ty ("reg_" ++ show n)

addInstr :: LlvmValue -> LlvmValue -> IrGen LlvmStatement
addInstr left right = do
    result <- freshReg LlvmI32
    return $ LlvmAssign (getRegName result) (LlvmAdd left right)

callInstr :: String -> [LlvmValue] -> LlvmType -> IrGen LlvmStatement
callInstr name args retType = do
    result <- freshReg retType
    return $ LlvmAssign (getRegName result) (LlvmCall name args)

data MemoryScope = MemoryScope
    { blockName :: String
    , blockValues :: Map String LlvmValue
    , blockParent :: Maybe MemoryScope
    }
    deriving (Show)

insertMemory :: String -> LlvmValue -> IrGen ()
insertMemory name value = do
    env <- ask
    let scope = currentScope env
        newValues = Map.insert name value (blockValues scope)
        newScope = scope { blockValues = newValues }
    local (\e -> e { currentScope = newScope }) (return ())

lookupMemory :: MonadReader IrGenEnv m => String -> m (Maybe LlvmValue)
lookupMemory name = do
  scope <- asks currentScope
  return $ getMem scope name

freshScope :: String -> IrGen MemoryScope
freshScope name = do
    parent <- asks currentScope
    return MemoryScope
        { blockName = name
        , blockValues = Map.empty
        , blockParent = Just parent
        }

getMem :: MemoryScope -> String -> Maybe LlvmValue
getMem (MemoryScope _ values parent) name =
    case Map.lookup name values of
        Just v -> Just v
        Nothing -> case parent of
            Just p -> getMem p name
            Nothing -> Nothing

withScope :: MemoryScope -> IrGen a -> IrGen a
withScope newScope = local (\env -> env { currentScope = newScope })

scopedState :: IrGen a -> IrGen a
scopedState action = do
    st <- get
    result <- action
    put st
    return result