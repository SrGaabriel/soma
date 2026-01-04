module Llvm.Gen.TypeConversion (
    convertType,
    convertTypeWithStructs,
    convertTypeWithStructInfo,
    getConstructorTag,
) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Llvm.Types
import Project.Unique (Unique)
import Typing.Types

-- | Convert a type to LLVM type, treating all user-defined types as ADTs
convertType :: Type -> LlvmType
convertType = convertTypeWithStructs Set.empty

convertTypeWithStructs :: Set Unique -> Type -> LlvmType
convertTypeWithStructs structs = convertTypeWithStructInfo structs Map.empty

convertTypeWithStructInfo :: Set Unique -> Map Unique String -> Type -> LlvmType
convertTypeWithStructInfo structs structNames = go
  where
    go (TApp (TConstructor (TypeConstructor (TyPrim TPRef) _)) innerTy) =
        LlvmPointer (go innerTy)
    go (TApp (TConstructor (TypeConstructor (TyPrim TPIO) _)) innerTy) =
        go innerTy
    go (TApp (TConstructor (TypeConstructor (TyPrim TPArray) _)) innerTy) =
        LlvmPointer (go innerTy)
    go (TApp (TConstructor (TypeConstructor tyId _)) _arg) =
        convertUserType tyId
    go (TApp (TApp (TConstructor (TypeConstructor tyId _)) _leftArg) _rightArg) =
        convertUserType tyId
    go (TArrow argTy retTy) =
        let argTypes = collectArgTypes argTy
            retType = go retTy
        in LlvmPointer (LlvmFn retType argTypes)
      where
        collectArgTypes (TArrow a b) = go a : collectArgTypes b
        collectArgTypes t = [go t]
    go (TSkolem _) =
        LlvmPointer LlvmI8
    go (TVar _) =
        LlvmPointer LlvmI8
    go (TUnresolved name) =
        error $ "Unresolved type " ++ name ++ " encountered during LLVM codegen."
    go (TApp constructor arg) =
        error $ "Unsupported complex type application in LLVM codegen: " ++ show constructor ++ " applied to " ++ show arg
    go (TConstructor (TypeConstructor tyId _)) =
        case tyId of
            TyPrim TPString -> LlvmPointer LlvmI8
            TyPrim TPBool -> LlvmI1
            TyPrim TPInt -> LlvmI32
            TyPrim TPFloat -> LlvmFloat
            TyPrim TPDouble -> LlvmDouble
            TyPrim TPLong -> LlvmI64
            TyPrim TPByte -> LlvmI8
            TyPrim TPShort -> LlvmI16
            TyPrim TPUnit -> LlvmVoid
            TyPrim TPClosurePtr -> LlvmPointer LlvmI8
            TyPrim TPPtr -> LlvmPointer LlvmI8
            TyPrim TPArray -> LlvmPointer LlvmI8
            TyPrim TPRef -> LlvmPointer LlvmI8
            TyPrim TPIO -> LlvmVoid
            TyPrim (TPTuple _) -> LlvmAnonymous [LlvmI8, LlvmI64]
            TyUserDefined u -> convertUserType (TyUserDefined u)

    convertUserType :: TyUnique -> LlvmType
    convertUserType (TyUserDefined u)
        | Set.member u structs =
            case Map.lookup u structNames of
                Just llvmName -> LlvmPointer (LlvmNamedType llvmName)
                Nothing -> LlvmPointer LlvmI8 -- Fallback for structs without name info
        | otherwise = LlvmAnonymous [LlvmI8, LlvmI64] -- ADTs have tag + payload
    convertUserType _ = LlvmAnonymous [LlvmI8, LlvmI64]

-- todo(urgent): proper implementation would use constructor metadata
getConstructorTag :: String -> Int -> Int
getConstructorTag _name defaultTag = defaultTag
