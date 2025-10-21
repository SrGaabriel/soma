module Llvm.Gen.Functions where

import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as Map
import Llvm.Gen.Context
import Llvm.Gen.Core (IrGen, IrGenEnv (..), IrGenState (..), MemoryScope (..), ctxFreshReg, freshScope)
import Llvm.Gen.Types (toAllocationLlvmType)
import Llvm.Instructions (LlvmInstruction (..), LlvmStatement (..))
import Llvm.Modules (LlvmFunction (..))
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..))
import Syntax.Tree (Expr (..))
import Typing.Currying (uncurryFunction)
import Typing.Types (Type)

compileFunction :: String -> Type -> Expr -> (Expr -> IrGen GenValue) -> IrGen ()
compileFunction name bindingTyp fn compileValueFunc = do
    env <- ask
    let (fnArgs, fnRetType) = uncurryFunction bindingTyp
    fnArgRegs <-
        sequence
            [ ctxFreshReg (mkFunctionArg pos (Just name)) (toAllocationLlvmType ty)
            | (pos, ty) <- zip [0 ..] fnArgs
            ]
    newScope <- freshScope name
    st <- get
    let (newEnv, action) = case fn of
            ExprLambda args body _ -> do
                let argBindings = zip args fnArgRegs
                let updatedScope =
                        newScope
                            { blockValues =
                                Map.fromList (map (\(nam, val) -> (nam, val)) argBindings)
                                    `Map.union` blockValues newScope
                            }
                let updatedEnv = env{currentScope = updatedScope, currentFunction = Just name}
                (updatedEnv, compileValueFunc body)
            _ -> (env, compileValueFunc fn)
    let ((retVal, stmts), st') = runState (runWriterT (runReaderT action newEnv)) st
    let llvmFnArgTypes = map toAllocationLlvmType fnArgs
    let llvmFnRetType = toAllocationLlvmType fnRetType
    let llvmFnArgs = Map.fromList [(case gvw argName of LlvmRegister _ n -> n; _ -> error "Expected LlvmRegister", argType) | (argName, argType) <- zip fnArgRegs llvmFnArgTypes]

    let (finalRetVal, additionalStmts) = case getGenValueType retVal of
            LlvmVoid -> (Nothing, [])
            LlvmPointer innerType@(LlvmNamedType _) ->
                if isADTReturnedByValue llvmFnRetType
                    then
                        let loadReg = LlvmRegister innerType ("reg_" ++ show (nextRegister st'))
                            loadStmt = LlvmAssign (getRegName loadReg) (LlvmLoad $ gvw retVal)
                            cLoadReg = mkStructValueLoad retVal loadReg
                        in (Just cLoadReg, [loadStmt])
                    else
                        (Just retVal, [])
            _ -> (Just retVal, [])

    let finalStatement = LlvmRet llvmFnRetType (gvw <$> finalRetVal)

    put st'{nextRegister = nextRegister st' + length additionalStmts}

    let llvmFunction =
            LlvmFunction
                { functionName = name
                , functionParams = llvmFnArgs
                , functionReturnType = llvmFnRetType
                , functionBlocks = []
                , functionStatements = stmts ++ additionalStmts ++ [finalStatement]
                }
    modify $ \s -> s{irFunctions = llvmFunction : irFunctions s}

isADTReturnedByValue :: LlvmType -> Bool
isADTReturnedByValue (LlvmNamedType _) = True
isADTReturnedByValue (LlvmPointer _) = False
isADTReturnedByValue _ = False

getRegName :: LlvmValue -> String
getRegName (LlvmRegister _ name) = name
getRegName _ = error "Expected register"
