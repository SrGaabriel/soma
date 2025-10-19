module Llvm.Gen.Bindings where

import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Llvm.Gen.Core (IrGen, IrGenState (..), freshReg, freshScope, IrGenEnv (..), MemoryScope (..))
import Llvm.Gen.Types (toAllocationLlvmType)
import Llvm.Gen.Value (compileValue)
import Llvm.Instructions (LlvmStatement (..), LlvmInstruction (..))
import Llvm.Modules (LlvmFunction (..))
import Llvm.Types (LlvmType (..))
import Llvm.Values (getValueType, LlvmValue(..))
import Syntax.Tree (Expr (..))
import Typing.Currying (uncurryFunction)
import Typing.Types (QualifiedType (Forall), Type)
import qualified Data.Map as Map

compileBindingDef :: Expr -> IrGen ()
compileBindingDef (ExprBindingDef name (Forall _ _ bindingTyp) body _ _) = do
    compileFunction name bindingTyp body
compileBindingDef _ = error "Unsupported binding definition expression"

compileFunction :: String -> Type -> Expr -> IrGen ()
compileFunction name bindingTyp body = do
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
            u -> (env, compileValue u)
    let ((retVal, stmts), st') = runState (runWriterT (runReaderT action newEnv)) st
    let llvmFnArgTypes = map toAllocationLlvmType fnArgs
    let llvmFnRetType = toAllocationLlvmType fnRetType
    let llvmFnArgs = Map.fromList [(case argName of LlvmRegister _ n -> n; _ -> error "Expected LlvmRegister", argType) | (argName, argType) <- (zip fnArgRegs llvmFnArgTypes)]
    
    let (finalRetVal, additionalStmts) = case getValueType retVal of
            LlvmVoid -> (Nothing, [])
            LlvmPointer innerType@(LlvmNamedType _) -> 
                if isADTReturnedByValue llvmFnRetType then
                    let loadReg = LlvmRegister innerType ("reg_" ++ show (nextRegister st'))
                        loadStmt = LlvmAssign (getRegName loadReg) (LlvmLoad retVal)
                    in (Just loadReg, [loadStmt])
                else
                    (Just retVal, [])
            _ -> (Just retVal, [])
    
    let finalStatement = LlvmRet llvmFnRetType finalRetVal
    
    put st' { nextRegister = nextRegister st' + length additionalStmts }
    
    let llvmFunction =
            LlvmFunction
                { functionName = name
                , functionParams = llvmFnArgs
                , functionReturnType = llvmFnRetType
                , functionBlocks = []
                , functionStatements = stmts ++ additionalStmts ++ [finalStatement]
                }
    modify $ \s -> s { irFunctions = llvmFunction : irFunctions s }

isADTReturnedByValue :: LlvmType -> Bool
isADTReturnedByValue (LlvmNamedType _) = True  
isADTReturnedByValue (LlvmPointer _) = False   
isADTReturnedByValue _ = False                 

getRegName :: LlvmValue -> String
getRegName (LlvmRegister _ name) = name
getRegName _ = error "Expected register"