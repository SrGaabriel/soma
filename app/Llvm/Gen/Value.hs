module Llvm.Gen.Value where

import Llvm.Gen.Core (lookupMemory, IrGenEnv, IrGenState)
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..))
import Syntax.Tree (Expr (..))
import Control.Monad.Writer (WriterT)
import Llvm.Instructions (LlvmStatement)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (State)

compileValue :: Expr -> WriterT [LlvmStatement] (ReaderT IrGenEnv (State IrGenState)) LlvmValue
compileValue expr = case expr of
    ExprNum n _ -> return $ LlvmLiteral LlvmI32 n
    ExprVar name _ -> do
        maybeMem <- lookupMemory name
        case maybeMem of
            Just mem -> return mem
            Nothing -> error $ "Undefined variable: " ++ name
    
    _ -> error $ "Unsupported llvm value expression type: " ++ show expr