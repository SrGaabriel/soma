module Llvm.Gen.TypeConversion where
import Typing.Types
import Llvm.Types

convertType :: Type -> LlvmType
convertType (TConstructor (TypeConstructor "String" _)) = LlvmPointer LlvmI8
convertType (TConstructor (TypeConstructor "Bool" _)) = LlvmI1
convertType (TConstructor (TypeConstructor "Int" _)) = LlvmI32
convertType (TConstructor (TypeConstructor "Float" _)) = LlvmFloat
convertType (TConstructor (TypeConstructor "Double" _)) = LlvmDouble
convertType (TConstructor (TypeConstructor "Long" _)) = LlvmI64
convertType (TConstructor (TypeConstructor "Byte" _)) = LlvmI8
convertType (TConstructor (TypeConstructor "Short" _)) = LlvmI16
convertType u = error $ "Unsupported LLVM IR type: " ++ show u