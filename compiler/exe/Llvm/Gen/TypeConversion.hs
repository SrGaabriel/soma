module Llvm.Gen.TypeConversion (
    convertType,
    getConstructorTag,
) where

import Llvm.Types
import Typing.Types

convertType :: Type -> LlvmType
convertType (TApp (TConstructor (TypeConstructor (TyPrim TPRef) _)) innerTy) =
    LlvmPointer (convertType innerTy)
convertType (TApp (TConstructor (TypeConstructor (TyPrim TPIO) _)) innerTy) =
    convertType innerTy
convertType (TApp (TConstructor (TypeConstructor (TyPrim TPArray) _)) innerTy) =
    LlvmPointer (convertType innerTy)
convertType (TApp (TConstructor (TypeConstructor _tyId _)) _arg) =
    LlvmAnonymous [LlvmI8, LlvmI64]
convertType (TApp (TApp (TConstructor (TypeConstructor _tyId _)) _leftArg) _rightArg) =
    LlvmAnonymous [LlvmI8, LlvmI64]
convertType (TArrow argTy retTy) =
    let argTypes = collectArgTypes argTy
        retType = convertType retTy
    in LlvmPointer (LlvmFn retType argTypes)
  where
    collectArgTypes (TArrow a b) = convertType a : collectArgTypes b
    collectArgTypes t = [convertType t]
convertType (TSkolem _) =
    -- todo(review): maybe throw an error here?
    LlvmPointer LlvmI8
convertType (TVar _) =
    -- todo(review): maybe throw an error here?
    LlvmPointer LlvmI8
convertType (TUnresolved name) =
    error $ "Unresolved type " ++ name ++ " encountered during LLVM codegen."
convertType (TApp constructor arg) =
    error $ "Unsupported complex type application in LLVM codegen: " ++ show constructor ++ " applied to " ++ show arg
convertType (TConstructor (TypeConstructor tyId _)) =
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
        TyPrim TPArray -> LlvmPointer LlvmI8 -- Should not happen, handled above
        TyPrim TPRef -> LlvmPointer LlvmI8 -- Should not happen, handled above
        TyPrim TPIO -> LlvmVoid -- Should not happen, handled above
        TyPrim (TPTuple _) -> LlvmAnonymous [LlvmI8, LlvmI64]
        TyUserDefined _ -> LlvmAnonymous [LlvmI8, LlvmI64]

-- todo(urgent): proper implementation would use constructor metadata
getConstructorTag :: String -> Int -> Int
getConstructorTag _name defaultTag = defaultTag
