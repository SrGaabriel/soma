module Llvm.Gen.Types where
import Llvm.Types (LlvmType (..))
import Typing.Types (Type(..), TyConstructor (TypeConstructor), TyVar (TypeVar), SkolemVar (SkolemVar))

toAllocationLlvmType :: Type -> LlvmType
toAllocationLlvmType t = case flattenTypeApp t of
    (TConstructor (TypeConstructor "IO" _), [innerType]) -> 
        toAllocationLlvmType innerType
    (TConstructor (TypeConstructor "Unit" _), []) -> LlvmVoid
    (TConstructor (TypeConstructor "Int" _), []) -> LlvmI32
    (TConstructor (TypeConstructor "Float" _), []) -> LlvmFloat
    (TConstructor (TypeConstructor "String" _), []) -> LlvmArray 0 LlvmI8
    (TConstructor (TypeConstructor "Bool" _), []) -> LlvmI1

    (TConstructor (TypeConstructor baseName _), args) | not (null args) ->
        let argNames = map typeToMonomorphicName args
            monomorphicName = baseName ++ concatMap ("_" ++) argNames
        in LlvmNamedType monomorphicName

    (TConstructor (TypeConstructor name _), []) -> LlvmNamedType name

    (TArrow _ _, _) -> LlvmPtr

    (TVar (TypeVar varName _), _) ->
        error $ "Uninstantiated type variable in codegen: " ++ varName
    (TSkolem (SkolemVar _ _ _ name _), _) ->
        error $ "Skolem variable in codegen: " ++ name
    (TUnresolved name, _) ->
        error $ "Unresolved type in codegen: " ++ name

    _ -> error $ "Unsupported type for allocation: " ++ show t

flattenTypeApp :: Type -> (Type, [Type])
flattenTypeApp (TApp t1 t2) =
    let (base, args) = flattenTypeApp t1
    in (base, args ++ [t2])
flattenTypeApp t = (t, [])

typeToMonomorphicName :: Type -> String
typeToMonomorphicName t = case flattenTypeApp t of
    (TConstructor (TypeConstructor name _), []) -> name
    (TConstructor (TypeConstructor baseName _), args) ->
        baseName ++ concatMap (("_" ++) . typeToMonomorphicName) args
    (TVar (TypeVar name _), _) -> name
    u -> "Unknown: " ++ show u

llvmTypeToMonomorphicName :: LlvmType -> String
llvmTypeToMonomorphicName LlvmI32 = "Int"
llvmTypeToMonomorphicName LlvmI64 = "Int64"
llvmTypeToMonomorphicName LlvmFloat = "Float"
llvmTypeToMonomorphicName LlvmDouble = "Double"
llvmTypeToMonomorphicName LlvmI1 = "Bool"
llvmTypeToMonomorphicName LlvmI8 = "Byte"
llvmTypeToMonomorphicName (LlvmNamedType name) = name
llvmTypeToMonomorphicName (LlvmPointer _) = "Ptr"
llvmTypeToMonomorphicName (LlvmArray _ _) = "Array"
llvmTypeToMonomorphicName _ = "Unknown"