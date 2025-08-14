module Llvm.Gen.Bindings where

import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Llvm.Gen.Core (IrGen, IrGenState (irFunctions), freshReg, freshScope, IrGenEnv (..), MemoryScope (..))
import Llvm.Gen.Types (toAllocationLlvmType)
import Llvm.Gen.Value (compileValue)
import Llvm.Instructions (LlvmStatement (LlvmRet))
import Llvm.Modules (LlvmFunction (..))
import Llvm.Types (LlvmType (LlvmVoid))
import Llvm.Values (getValueType, LlvmValue(..))
import Syntax.Tree (Expr (..))
import Typing.Currying (uncurryFunction)
import Typing.Types (QualifiedType (Forall))
import qualified Data.Map as Map

compileBindingDef :: Expr -> IrGen ()
compileBindingDef (ExprBindingDef name (Forall _ _ bindingTyp) body _ _) = do
    env <- ask
    let (fnArgs, fnRetType) = uncurryFunction bindingTyp
    fnArgRegs <- mapM (freshReg . toAllocationLlvmType) fnArgs
    newScope <- freshScope name
    st <- get

    let (newEnv, action) = case body of
            ExprLambda args lambdaBody _ -> do
                let argBindings = zip args fnArgRegs
                let updatedScope = newScope
                        { blockValues = Map.fromList (map (\(nam, val) -> (nam, val)) argBindings)
                                        `Map.union` blockValues newScope
                        }
                let updatedEnv = env { currentScope = updatedScope, currentFunction = Just name }
                (updatedEnv, compileValue lambdaBody)
            u -> error $ "Unsupported body expression: " ++ show u

    let ((retVal, stmts), st') = runState (runReaderT (runWriterT action) newEnv) st

    let llvmFnArgTypes = map toAllocationLlvmType fnArgs
    let llvmFnRetType = toAllocationLlvmType fnRetType
    let llvmFnArgs = Map.fromList [(case argName of LlvmRegister _ n -> n; _ -> error "Expected LlvmRegister", argType) | (argName, argType) <- (zip fnArgRegs llvmFnArgTypes)]

    let finalStatement =
            LlvmRet
                llvmFnRetType
                ( case getValueType retVal of
                    LlvmVoid -> Nothing
                    _ -> Just retVal
                )

    put st'
    let llvmFunction =
            LlvmFunction
                { functionName = name
                , functionParams = llvmFnArgs
                , functionReturnType = llvmFnRetType
                , functionBlocks = []
                , functionStatements = stmts ++ [finalStatement]
                }
    modify $ \s -> s { irFunctions = llvmFunction : irFunctions s }
compileBindingDef _ = error "Unsupported binding definition expression"