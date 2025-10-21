module Llvm.Gen.Types where

import Llvm.Types (LlvmType (..))
import Typing.Types (SkolemVar (SkolemVar), TyConstructor (TypeConstructor), TyVar (TypeVar), Type (..))
import Typing.Currying (uncurryFunction)

toAllocationLlvmType :: Type -> LlvmType
toAllocationLlvmType t = case flattenTypeApp t of
    (TConstructor (TypeConstructor "IO" _), [innerType]) ->
        toAllocationLlvmType innerType
    (TConstructor (TypeConstructor "Unit" _), []) -> LlvmVoid
    (TConstructor (TypeConstructor "Int" _), []) -> LlvmI32
    (TConstructor (TypeConstructor "Float" _), []) -> LlvmFloat
    (TConstructor (TypeConstructor "String" _), []) -> LlvmPointer LlvmI8
    (TConstructor (TypeConstructor "Bool" _), []) -> LlvmI1
    (TConstructor (TypeConstructor "Array" _), _) -> sliceType
    (TConstructor (TypeConstructor baseName _), args)
        | not (null args) ->
            let argNames = map typeToMonomorphicName args
                monomorphicName = baseName ++ concatMap ("_" ++) argNames
            in LlvmNamedType monomorphicName
    (TConstructor (TypeConstructor name _), []) -> LlvmNamedType name
    (TArrow _ _, _) ->
        let (args, base) = uncurryFunction t
            baseLlvm = toAllocationLlvmType base
            argLlvmTypes = map toAllocationLlvmType args
            funcType = LlvmFn baseLlvm argLlvmTypes
        in LlvmPointer funcType
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
    (TConstructor (TypeConstructor "Array" _), [elemType]) ->
        "Array_" ++ typeToMonomorphicName elemType
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

sliceType :: LlvmType
sliceType = LlvmAnonymous [LlvmPointer LlvmI8, LlvmI32]

getArrayElementType :: Type -> Type
getArrayElementType t = case flattenTypeApp t of
    (TConstructor (TypeConstructor "Array" _), [elemType]) -> elemType
    _ -> error $ "Not an array type: " ++ show t