{-# LANGUAGE FlexibleContexts #-}

module Llvm.Gen.Core where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Inference.Core (TypeMap)
import Llvm.Dependencies (LlvmDependency)
import Llvm.Gen.Context (GenValue (..))
import Llvm.Gen.Metadata (ConstructorMetadata, InstanceMetadata, PolymorphicFunctionMetadata, TypeClassMetadata)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))
import Llvm.Modules (LlvmFunction, LlvmStruct)
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..), getRegName)
import Syntax.Tree (Expr)
import Typing.Types (QualifiedType)

data IrGenEnv = IrGenEnv
    { currentScope :: MemoryScope
    , currentFunction :: Maybe String
    , currentBlock :: Maybe String
    }

data IrGenState = IrGenState
    { nextRegister :: Int
    , nextBlock :: Int
    , typeMap :: TypeMap
    , irFunctions :: [LlvmFunction]
    , constructorMap :: Map String ConstructorMetadata
    , irStructs :: [LlvmStruct]
    , irDependencies :: [LlvmDependency]
    , typeclasses :: [TypeClassMetadata]
    , instances :: [InstanceMetadata]
    , polymorphicFunctions :: Map String PolymorphicFunctionMetadata
    , monomorphizedFunctions :: Set String
    }
    deriving (Show)

globalDefaultState :: IrGenState
globalDefaultState =
    IrGenState
        { nextRegister = 0
        , nextBlock = 0
        , typeMap = Map.empty
        , constructorMap = Map.empty
        , typeclasses = []
        , instances = []
        , irFunctions = []
        , irStructs = []
        , irDependencies = []
        , polymorphicFunctions = Map.empty
        , monomorphizedFunctions = Set.empty
        }

cleanGlobalState :: TypeMap -> IrGenState
cleanGlobalState tM =
    IrGenState
        { nextRegister = 0
        , nextBlock = 0
        , typeMap = tM
        , constructorMap = Map.empty
        , typeclasses = []
        , instances = []
        , irFunctions = []
        , irStructs = []
        , irDependencies = []
        , polymorphicFunctions = Map.empty
        , monomorphizedFunctions = Set.empty
        }

globalDefaultEnv :: IrGenEnv
globalDefaultEnv =
    IrGenEnv
        { currentScope =
            MemoryScope
                { blockName = "global"
                , blockValues = Map.empty
                , blockParent = Nothing
                }
        , currentFunction = Nothing
        , currentBlock = Nothing
        }

type IrGen a = ReaderT IrGenEnv (WriterT [LlvmStatement] (State IrGenState)) a

runIrGen :: IrGenEnv -> IrGenState -> IrGen a -> ((a, [LlvmStatement]), IrGenState)
runIrGen env st action =
    runState (runWriterT (runReaderT action env)) st

freshReg :: (MonadState IrGenState m) => LlvmType -> m LlvmValue
freshReg ty = do
    n <- gets nextRegister
    modify $ \s -> s{nextRegister = n + 1}
    return $ LlvmRegister ty ("reg_" ++ show n)

ctxFreshReg :: (MonadState IrGenState m) => (LlvmValue -> GenValue) -> LlvmType -> m GenValue
ctxFreshReg mkCtx ty = do
    fresh <- freshReg ty
    return $ mkCtx fresh

data MemoryScope = MemoryScope
    { blockName :: String
    , blockValues :: Map String GenValue
    , blockParent :: Maybe MemoryScope
    }
    deriving (Show)

insertMemory :: String -> GenValue -> IrGen ()
insertMemory name value = do
    env <- ask
    let scope = currentScope env
        newValues = Map.insert name value (blockValues scope)
        newScope = scope{blockValues = newValues}
    local (\e -> e{currentScope = newScope}) (return ())

lookupMemory :: (MonadReader IrGenEnv m) => String -> m (Maybe GenValue)
lookupMemory name = do
    scope <- asks currentScope
    return $ getMem scope name

freshScope :: String -> IrGen MemoryScope
freshScope name = do
    parent <- asks currentScope
    return
        MemoryScope
            { blockName = name
            , blockValues = Map.empty
            , blockParent = Just parent
            }

getMem :: MemoryScope -> String -> Maybe GenValue
getMem (MemoryScope _ values parent) name =
    case Map.lookup name values of
        Just v -> Just v
        Nothing -> case parent of
            Just p -> getMem p name
            Nothing -> Nothing

withScope :: MemoryScope -> IrGen a -> IrGen a
withScope newScope = local (\env -> env{currentScope = newScope})

saveInstruction :: (MonadState IrGenState m) => (MonadWriter [LlvmStatement] m) => LlvmInstruction -> LlvmType -> m LlvmValue
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

getType :: (MonadState IrGenState m) => Expr -> m QualifiedType
getType expr = do
    st <- get
    let tyMap = typeMap st
    case Map.lookup expr tyMap of
        Just ty -> return ty
        Nothing -> error $ "Type not found for expression: " ++ show expr

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
    newScope <- freshScope name
    local (\env -> env{currentScope = newScope, currentBlock = Just name}) generation
