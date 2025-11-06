module Llvm.Gen.TypeConversion where
import Typing.Types
import Llvm.Types

convertType :: Type -> LlvmType
convertType (TConstructor (TypeConstructor "String" _)) = LlvmPointer LlvmI8
convertType (TConstructor (TypeConstructor "Bool" _)) = LlvmPointer LlvmI1
convertType u = error $ "Unsupported type for conversion to LLVM: " ++ show u