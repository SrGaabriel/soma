module Llvm.Gen.Externals where

import Control.Monad.State (modify)
import Llvm.Dependencies (LlvmDependency (..))
import Llvm.Gen.Core (IrGen, IrGenState (irDependencies))
import Llvm.Gen.Types (toAllocationLlvmType)
import Project.Symbols (Symbol (..), SymbolKind (..))
import Typing.Currying (uncurryFunction)
import Typing.Types (QualifiedType (..))

importExternalDependency :: Symbol -> IrGen ()
importExternalDependency sym = do
    case resolvedSymbolKind sym of
        BindingSymbol (Forall _ _ bindingTyp) -> do
            let (fnArgs, fnRetType) = uncurryFunction bindingTyp
            let llvmFnArgTypes = map toAllocationLlvmType fnArgs
            let llvmFnRetType = toAllocationLlvmType fnRetType
            let dependency =
                    LlvmFunctionDependency
                        { depName = resolvedSymbolName sym
                        , depParams = llvmFnArgTypes
                        , depReturnType = llvmFnRetType
                        }
            modify $ \s -> s{irDependencies = dependency : irDependencies s}
        _ -> error $ "Unsupported symbol kind for external dependency: " ++ show sym
