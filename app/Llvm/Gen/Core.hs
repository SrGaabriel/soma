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
import Llvm.Modules (LlvmFunction)
import Llvm.Dependencies (LlvmDependency)

data IrGenEnv = IrGenEnv
    { currentScope :: MemoryScope
    , currentFunction :: Maybe String
    }

data IrGenState = IrGenState
    { nextRegister :: Int
    , nextBlock :: Int
    , typeMap :: TypeMap
    , currentBlock :: Maybe String
    , irFunctions :: [LlvmFunction]
    , irDependencies :: [LlvmDependency]
    }
    deriving (Show)

globalDefaultState :: IrGenState
globalDefaultState = IrGenState
    { nextRegister = 0
    , nextBlock = 0
    , typeMap = Map.empty
    , currentBlock = Nothing
    , irFunctions = []
    , irDependencies = []
    }

cleanGlobalState :: TypeMap -> IrGenState
cleanGlobalState tM = IrGenState
    { nextRegister = 0
    , nextBlock = 0
    , typeMap = tM
    , currentBlock = Nothing
    , irFunctions = []
    , irDependencies = []
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

type IrGen a = ReaderT IrGenEnv (WriterT [LlvmStatement] (State IrGenState)) a

runIrGen :: IrGenEnv -> IrGenState -> IrGen a -> ((a, [LlvmStatement]), IrGenState)
runIrGen env st action =
  runState (runWriterT (runReaderT action env)) st

freshReg :: MonadState IrGenState m => LlvmType -> m LlvmValue
freshReg ty = do
    n <- gets nextRegister
    modify $ \s -> s { nextRegister = n + 1 }
    return $ LlvmRegister ty ("reg_" ++ show n)

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

saveInstruction :: MonadState IrGenState m => MonadWriter [LlvmStatement] m => LlvmInstruction -> LlvmType -> m LlvmValue
saveInstruction instr ty = do
    reg <- freshReg ty
    tell [LlvmAssign (getRegName reg) instr]
    return reg

scopedState :: IrGen a -> IrGen a
scopedState action = do
    st <- get
    result <- action
    put st
    return result