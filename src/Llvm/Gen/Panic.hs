module Llvm.Gen.Panic where

import Control.Monad.State (modify)
import Control.Monad.Writer (tell)
import Llvm.Dependencies (LlvmDependency (..))
import Llvm.Gen.Context (GenValue (..))
import Llvm.Gen.Core (IrGen, IrGenState (irDependencies))
import Llvm.Gen.Templates (newStrTemplate)
import Llvm.Instructions (LlvmStatement (..))
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (..))

panic :: String -> IrGen ()
panic msg = do
    let len = length msg
    str <- newStrTemplate msg len

    let putsDep = LlvmFunctionDependency "puts" LlvmI32 [LlvmPointer LlvmI8]
    modify $ \s -> s{irDependencies = putsDep : irDependencies s}

    tell [LlvmCallStmt (LlvmGlobal (LlvmFn LlvmI32 [LlvmPointer LlvmI8]) "puts") LlvmI32 [gvw str]]
    tell [LlvmUnreachable]
