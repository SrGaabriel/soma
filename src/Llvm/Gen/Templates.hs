module Llvm.Gen.Templates where

import Control.Monad.State (gets, modify)
import Llvm.Dependencies (LinkageType (PrivateLinkage), LlvmDependency (LlvmConstantDependency))
import Llvm.Gen.Core (IrGen, IrGenState (nextStringId), addDependency)
import Llvm.Types (LlvmType (LlvmArray, LlvmI8, LlvmPointer))
import Llvm.Values (LlvmValue (LlvmGlobal, LlvmLiteral))

newStrTemplate ::
    String ->
    IrGen LlvmValue
newStrTemplate template = do
    strNum <- gets nextStringId
    modify $ \s -> s{nextStringId = strNum + 1}
    let strName = "str_" ++ show strNum
    let strLen = length (processEscapes template) + 1 -- +1 for null terminator
    let strType = LlvmArray strLen LlvmI8
    let strDep =
            LlvmConstantDependency
                strName
                (LlvmLiteral strType ("c\"" ++ template ++ "\\00\""))
                (Just PrivateLinkage)
    addDependency strDep
    pure $ LlvmGlobal (LlvmPointer LlvmI8) strName
  where
    processEscapes :: String -> String
    processEscapes [] = []
    processEscapes ('\\' : '0' : 'A' : rest) = '\n' : processEscapes rest
    processEscapes ('\\' : 'n' : rest) = '\n' : processEscapes rest
    processEscapes (c : rest) = c : processEscapes rest
