module Llvm.Gen.Types where
import Llvm.Types (LlvmType (..))
import Typing.Types (Type(..), TyConstructor (TypeConstructor))

toAllocationLlvmType :: Type -> LlvmType
toAllocationLlvmType (TConstructor (TypeConstructor name _)) =
    case name of
        "Int" -> LlvmI32
        "String" -> LlvmArray 0 LlvmI8
        "Bool" -> LlvmI1
toAllocationLlvmType (TSkolem _) = LlvmI32