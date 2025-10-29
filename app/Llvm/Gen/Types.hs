module Llvm.Gen.Types where

import Data.Hashable (Hashable (hash))
import Llvm.Gen.Mangling (mangleDataTypeName, mangleMonomorphizedName)
import Llvm.Types (LlvmType (..))
import Typing.Currying (uncurryFunction)
import Typing.Types (SkolemVar (SkolemVar), TyConstructor (TypeConstructor), TyVar (TypeVar), Type (..))

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
            let monomorphicName = mangleMonomorphizedName baseName (map toAllocationLlvmType args) -- todo: review this
            in LlvmNamedType monomorphicName
    (TConstructor (TypeConstructor name _), []) ->
        LlvmNamedType $ mangleDataTypeName name
    (TArrow _ _, _) ->
        let (args, base) = uncurryFunction t
            baseLlvm = toAllocationLlvmType base
            argLlvmTypes = map toAllocationLlvmType args
            funcType = LlvmFn baseLlvm argLlvmTypes
        in LlvmPointer funcType
    (TVar (TypeVar _ _), _) -> LlvmPointer LlvmSkolem
    (TSkolem (SkolemVar {}), _) -> LlvmPointer LlvmSkolem
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
llvmTypeToMonomorphicName = show . hash

sliceType :: LlvmType
sliceType = LlvmAnonymous [LlvmPointer LlvmI8, LlvmI32]

getArrayElementType :: Type -> Type
getArrayElementType t = case flattenTypeApp t of
    (TConstructor (TypeConstructor "Array" _), [elemType]) -> elemType
    _ -> error $ "Not an array type: " ++ show t
