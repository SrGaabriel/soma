module Llvm.Gen.Bindings where

import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Llvm.Gen.Core (IrGen)
import Llvm.Gen.Types (toAllocationLlvmType)
import Llvm.Gen.Value (compileValue)
import Llvm.Instructions (LlvmStatement (LlvmRet))
import Llvm.Modules (LlvmFunction (..))
import Llvm.Types (LlvmType (LlvmVoid))
import Llvm.Values (getValueType)
import Syntax.Tree (Expr (ExprBindingDef))
import Typing.Currying (uncurryFunction)
import Typing.Types (QualifiedType (Forall))
import qualified Data.Map as Map

compileBindingDef :: Expr -> IrGen LlvmFunction
compileBindingDef (ExprBindingDef name (Forall _ _ bindingTyp) body _ _) = do
    env <- ask
    st <- get
    let action = compileValue body

    let ((retVal, stmts), st') = runState (runReaderT (runWriterT action) env) st
    let (fnArgs, fnRetType) = uncurryFunction bindingTyp

    let finalStatement =
            LlvmRet
                ( case getValueType retVal of
                    LlvmVoid -> Nothing
                    _ -> Just retVal
                )

    let llvmFnArgs = map toAllocationLlvmType fnArgs
    let llvmFnRetType = toAllocationLlvmType fnRetType

    put st'
    return $
        LlvmFunction
            { functionName = name
            , functionParams = Map.empty -- todo:: 
            , functionReturnType = llvmFnRetType
            , functionBlocks = []
            , functionStatements = stmts ++ [finalStatement]
            }
compileBindingDef _ = error "Unsupported binding definition expression"