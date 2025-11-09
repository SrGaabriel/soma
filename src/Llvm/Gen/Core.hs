{-# LANGUAGE FlexibleContexts #-}

module Llvm.Gen.Core (
    IrGen,
    IrGenEnv (..),
    IrGenState (..),
    globalDefaultState,
    namedDefaultEnv,
    runIrGen,
    freshTmpReg,
    mkReg,
    saveToReg,
    saveTmp,
    scopedState,
    irGenToWriterOuter,
    writerOuterToIrGen,
    enterNewBlock,
    setNewBlock,
    mkFnCall,
    recordSubstitution,
    applySubstitutions,
    addDependency,
) where

import Control.Monad.Reader (MonadReader (local), ReaderT (..))
import Control.Monad.State (
    MonadState (get, put),
    State,
    StateT (StateT),
    gets,
    modify,
    runState,
 )
import Control.Monad.Writer (MonadWriter (tell), WriterT (..))
import qualified Data.Map as Map
import Llvm.Dependencies (LlvmDependency)
import Llvm.Gen.OperandPass (OperandTypeEnv)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))
import Llvm.Modules (LlvmFunction)
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..), getRegName, getValueType)
import Typing.Types (Type)

data IrGenEnv = IrGenEnv
    { currentFunction :: Maybe String
    , currentBlock :: Maybe String
    , currentPackage :: String
    , opTypeEnv :: OperandTypeEnv
    , dictMap :: Map.Map (String, Type) String
    }

data IrGenState = IrGenState
    { irFunctions :: [LlvmFunction]
    , irDependencies :: [LlvmDependency]
    , nextRegister :: Int
    , nextStringId :: Int
    , valueSubst :: Map.Map String LlvmValue
    }
    deriving (Show)

globalDefaultState :: IrGenState
globalDefaultState =
    IrGenState
        { nextRegister = 0
        , nextStringId = 0
        , irDependencies = []
        , irFunctions = []
        , valueSubst = Map.empty
        }

namedDefaultEnv :: String -> IrGenEnv
namedDefaultEnv name =
    IrGenEnv
        { currentFunction = Nothing
        , currentBlock = Nothing
        , currentPackage = name
        , opTypeEnv = Map.empty
        , dictMap = Map.empty
        }

type IrGen a = ReaderT IrGenEnv (WriterT [LlvmStatement] (State IrGenState)) a

runIrGen :: IrGenEnv -> IrGenState -> IrGen a -> ((a, [LlvmStatement]), IrGenState)
runIrGen env st action =
    runState (runWriterT (runReaderT action env)) st

freshTmpReg :: (MonadState IrGenState m) => LlvmType -> m LlvmValue
freshTmpReg ty = do
    n <- gets nextRegister
    modify $ \s -> s{nextRegister = n + 1}
    return $ LlvmRegister ty ("tmp_reg_" ++ show n)

mkReg :: String -> LlvmType -> LlvmValue
mkReg n t = LlvmRegister t n

saveToReg :: (MonadState IrGenState m) => (MonadWriter [LlvmStatement] m) => LlvmValue -> LlvmInstruction -> m LlvmValue
saveToReg reg instr = do
    tell [LlvmAssign (getRegName reg) instr]
    return reg

saveTmp :: (MonadState IrGenState m) => (MonadWriter [LlvmStatement] m) => LlvmInstruction -> LlvmType -> m LlvmValue
saveTmp instr ty = do
    reg <- freshTmpReg ty
    tell [LlvmAssign (getRegName reg) instr]
    return reg

scopedState :: IrGen a -> IrGen a
scopedState action = do
    st <- get
    result <- action
    put st
    return result

irGenToWriterOuter ::
    IrGen a ->
    WriterT [LlvmStatement] (ReaderT IrGenEnv (State IrGenState)) a
irGenToWriterOuter action = WriterT $ ReaderT $ \env -> StateT $ \st ->
    let ((result, stmts), st') = runState (runWriterT (runReaderT action env)) st
    in return ((result, stmts), st')

writerOuterToIrGen ::
    WriterT [LlvmStatement] (ReaderT IrGenEnv (State IrGenState)) a ->
    IrGen a
writerOuterToIrGen action = ReaderT $ \env -> WriterT $ StateT $ \st ->
    let ((result, stmts), st') = runState (runReaderT (runWriterT action) env) st
    in return ((result, stmts), st')

enterNewBlock :: String -> IrGen a -> IrGen a
enterNewBlock name generation = do
    tell [LlvmLabel name]
    local (\env -> env{currentBlock = Just name}) generation

setNewBlock :: String -> IrGen ()
setNewBlock name =
    tell [LlvmLabel name]

mkFnCall :: String -> [LlvmValue] -> LlvmType -> LlvmInstruction
mkFnCall name args retType =
    let argTypes = map getValueType args
    in LlvmCall (LlvmGlobal (LlvmFn retType argTypes) name) retType args

recordSubstitution :: (MonadState IrGenState m) => String -> LlvmValue -> m ()
recordSubstitution name val = do
    modify $ \s -> s{valueSubst = Map.insert name val (valueSubst s)}

applySubstitutions :: (MonadState IrGenState m) => LlvmValue -> m LlvmValue
applySubstitutions val@(LlvmRegister _ name) = do
    st <- get
    case Map.lookup name (valueSubst st) of
        Just substituted -> return substituted
        Nothing -> return val
applySubstitutions val = return val

addDependency ::
    LlvmDependency ->
    IrGen ()
addDependency dep = modify $ \s -> s{irDependencies = dep : irDependencies s}
