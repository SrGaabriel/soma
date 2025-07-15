module Llvm.Gen.Value where

import Llvm.Gen.Core (IrGen, lookupMemory, IrGenState (typeMap))
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..))
import Syntax.Tree (Expr (..))
import Control.Monad.RWS (gets)

compileExpr :: String -> Expr -> IrGen LlvmValue
compileExpr scope expr = case expr of
    ExprNum n _ ->
        return $ LlvmLiteral LlvmI32 n
    ExprVar name _ -> do
        maybeMem <- lookupMemory scope name
        case maybeMem of
            Just mem -> return mem
            Nothing -> error $ "Undefined variable: " ++ name
    
    _ -> error $ "Unsupported llvm value expression type: " ++ show expr