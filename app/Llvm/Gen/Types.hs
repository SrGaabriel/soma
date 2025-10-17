module Llvm.Gen.Types where
import Llvm.Types (LlvmType (..))
import Typing.Types (Type(..), TyConstructor (TypeConstructor))
import Logging.PrettyTrees (TreeShow(treeShow))

-- todo remake this whole thing

toAllocationLlvmType :: Type -> LlvmType
toAllocationLlvmType (TConstructor (TypeConstructor name _)) =
    case name of
        "Int" -> LlvmI32
        "Float" -> LlvmFloat
        "String" -> LlvmArray 0 LlvmI8
        "Bool" -> LlvmI1
        u -> LlvmNamedType u
toAllocationLlvmType (TArrow _ _) = LlvmPtr
toAllocationLlvmType u = error $ "Unsupported type for allocation: " ++ show u ++ " | " ++ treeShow u

getTypeSize :: Type -> Int
getTypeSize (TConstructor (TypeConstructor name _)) =
    case name of
        "Int" -> 4
        "Float" -> 4
        "String" -> 0
        "Bool" -> 1
        u -> error $ "Unsupported type for allocation: " ++ show u
getTypeSize (TArrow _ _) = 0
getTypeSize u = error $ "Unsupported type for allocation: " ++ show u ++ " | " ++ treeShow u
