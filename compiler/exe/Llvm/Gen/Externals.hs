module Llvm.Gen.Externals (
    putsDependency,
    printfDependency,
    memcpyDependency,
    mallocDependency,
    useDep
) where

import Llvm.Dependencies (LlvmDependency (..))
import Llvm.Gen.Core (IrGen, addDependency)
import Llvm.Types (LlvmType (..))
import Llvm.Values (LlvmValue (LlvmGlobal))

putsDependency :: LlvmDependency
putsDependency =
    LlvmFunctionDependency
        { depName = "puts"
        , depReturnType = LlvmI32
        , depParams = [LlvmPointer LlvmI8]
        }

printfDependency :: LlvmDependency
printfDependency =
    LlvmFunctionDependency
        { depName = "printf"
        , depReturnType = LlvmI32
        , depParams = [LlvmPointer LlvmI8, LlvmVararg]
        }

memcpyDependency :: LlvmDependency
memcpyDependency =
    LlvmFunctionDependency
        { depName = "memcpy"
        , depReturnType = LlvmPointer LlvmI8
        , depParams = [LlvmPointer LlvmI8, LlvmPointer LlvmI8, LlvmI64, LlvmI32, LlvmI1]
        }

mallocDependency :: LlvmDependency
mallocDependency =
    LlvmFunctionDependency
        { depName = "malloc"
        , depReturnType = LlvmPointer LlvmI8
        , depParams = [LlvmI64]
        }

useDep :: LlvmDependency -> IrGen LlvmValue
useDep dep = do
    addDependency dep
    pure $ mkValue dep

mkValue :: LlvmDependency -> LlvmValue
mkValue (LlvmFunctionDependency name retType argTypes) =
    LlvmGlobal (LlvmFn retType argTypes) name
mkValue (LlvmGlobalDependency name depType) =
    LlvmGlobal depType name
mkValue u = error $ "useDep: unsupported dependency " ++ show u
