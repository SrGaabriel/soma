module Llvm.Gen.TypeConversion where

import Alloy.Naming (nameDictSuffix)
import Data.List (isSuffixOf)
import Llvm.Types
import Typing.Types

convertType :: Type -> LlvmType
convertType (TApp (TConstructor (TypeConstructor "Ref" _)) innerTy) =
    LlvmPointer (convertType innerTy)
convertType (TApp (TConstructor (TypeConstructor "IO" _)) innerTy) =
    convertType innerTy
convertType (TApp (TConstructor (TypeConstructor "Array" _)) innerTy) =
    LlvmPointer (convertType innerTy)
convertType (TApp (TConstructor (TypeConstructor _name _)) _arg) =
    LlvmAnonymous [LlvmI8, LlvmI64]
convertType (TApp (TApp (TConstructor (TypeConstructor _name _)) _leftArg) _rightArg) =
    LlvmAnonymous [LlvmI8, LlvmI64]
convertType (TArrow argTy retTy) =
    let argTypes = collectArgTypes argTy
        retType = convertType retTy
    in LlvmPointer (LlvmFn retType argTypes)
  where
    collectArgTypes (TArrow a b) = convertType a : collectArgTypes b
    collectArgTypes t = [convertType t]
convertType (TSkolem _) =
    -- Skolem types are erased to generic pointers at runtime
    LlvmPointer LlvmI8
convertType (TVar _) =
    -- Type variables are erased to generic pointers at runtime
    LlvmPointer LlvmI8
convertType (TUnresolved name) =
    error $ "Unresolved type " ++ name ++ " encountered during LLVM codegen."
convertType (TApp constructor arg) =
    error $ "Unsupported complex type application in LLVM codegen: " ++ show constructor ++ " applied to " ++ show arg
convertType (TConstructor (TypeConstructor name _)) =
    case name of
        "String" -> LlvmPointer LlvmI8
        "Bool" -> LlvmI1
        "Int" -> LlvmI32
        "Float" -> LlvmFloat
        "Double" -> LlvmDouble
        "Long" -> LlvmI64
        "Byte" -> LlvmI8
        "Short" -> LlvmI16
        "Unit" -> LlvmVoid
        "()" -> LlvmVoid
        _ ->
            --
            if nameDictSuffix `isSuffixOf` name
                then LlvmPointer (LlvmNamedType name)
                else LlvmAnonymous [LlvmI8, LlvmI64]

sizeOfType :: LlvmType -> Int
sizeOfType LlvmVoid = 0
sizeOfType LlvmI1 = 1
sizeOfType LlvmI8 = 1
sizeOfType LlvmI16 = 2
sizeOfType LlvmI32 = 4
sizeOfType LlvmI64 = 8
sizeOfType LlvmFloat = 4
sizeOfType LlvmDouble = 8
sizeOfType (LlvmPointer _) = 8 -- todo: platform specific pointer size
sizeOfType (LlvmArray n elemTy) = n * sizeOfType elemTy
sizeOfType (LlvmAnonymous fields) = sum (map sizeOfType fields)
sizeOfType (LlvmFn _ _) = 8 -- todo: platform specific pointer size
sizeOfType (LlvmFunctionPtr _ _) = 8 -- function pointers are pointer-sized
sizeOfType (LlvmNamedType _) = 8 -- todo: remove estimation
sizeOfType LlvmVararg = 0
sizeOfType LlvmSkolem = 0

getConstructorTag :: String -> Int -> Int
getConstructorTag "Some" _ = 0
getConstructorTag "None" _ = 1
getConstructorTag "Left" _ = 0
getConstructorTag "Right" _ = 1
getConstructorTag _ tag = tag

constructorSignature :: String -> [Type] -> (Int, [LlvmType])
constructorSignature ctorName fieldTypes =
    let tag = getConstructorTag ctorName 0 -- todo: get actual tag from type system
        fieldLlvmTypes = map convertType fieldTypes
    in (tag, fieldLlvmTypes)
