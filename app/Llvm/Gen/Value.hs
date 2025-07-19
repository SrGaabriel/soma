{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Llvm.Gen.Value where

import Llvm.Gen.Core (lookupMemory, IrGenEnv, IrGenState (typeMap), saveInstruction)
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..))
import Syntax.Tree (Expr (..), uncurryApp)
import Control.Monad.Writer (WriterT)
import Llvm.Instructions (LlvmStatement, LlvmInstruction (..))
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (State, gets)
import Llvm.Gen.Types (toAllocationLlvmType)
import qualified Data.Map as Map
import Typing.Types (QualifiedType(Forall))
import Typing.Currying (uncurryFunction)

compileValue :: Expr -> WriterT [LlvmStatement] (ReaderT IrGenEnv (State IrGenState)) LlvmValue
compileValue expr = case expr of
    ExprNum n _ -> return $ LlvmLiteral LlvmI32 n
    ExprVar name _ -> do
        maybeMem <- lookupMemory name
        case maybeMem of
            Just mem -> return mem
            Nothing -> error $ "Undefined variable: " ++ name
    ExprApp fn arg -> do
        tyMap <- gets typeMap
        let (callBase, nestedCallArgs) = uncurryApp fn
        let callArgs = arg : nestedCallArgs
        argVals <- mapM compileValue callArgs
        let Just (Forall _ _ refType) = Map.lookup callBase tyMap
        let (_fnIntermediateTys, fnRetType) = uncurryFunction refType
        let callName = getApplicableFnName callBase
        let llvmFnType = toAllocationLlvmType fnRetType
        let call = LlvmCall (LlvmGlobal LlvmFn callName) llvmFnType argVals
        saveInstruction call llvmFnType
    _ -> error $ "Unsupported llvm value expression type: " ++ show expr

getApplicableFnName :: Expr -> String
getApplicableFnName (ExprVar name _) = name
getApplicableFnName u = error (show u)