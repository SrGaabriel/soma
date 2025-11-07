{-# LANGUAGE LambdaCase #-}

module Llvm.Gen.TypeConversion where

import Llvm.Types
import Typing.Types

convertType :: Type -> LlvmType
convertType (TConstructor (TypeConstructor "String" _)) = LlvmPointer LlvmI8
convertType (TConstructor (TypeConstructor "Bool" _)) = LlvmI1
convertType (TConstructor (TypeConstructor "Int" _)) = LlvmI32
convertType (TConstructor (TypeConstructor "Float" _)) = LlvmFloat
convertType (TConstructor (TypeConstructor "Double" _)) = LlvmDouble
convertType (TConstructor (TypeConstructor "Long" _)) = LlvmI64
convertType (TConstructor (TypeConstructor "Byte" _)) = LlvmI8
convertType (TConstructor (TypeConstructor "Short" _)) = LlvmI16
convertType (TConstructor (TypeConstructor "Unit" _)) = LlvmVoid
convertType (TConstructor (TypeConstructor "()" _)) = LlvmVoid
convertType (TApp (TConstructor (TypeConstructor "Ref" _)) innerTy) =
    LlvmPointer (convertType innerTy)
convertType (TApp (TConstructor (TypeConstructor "IO" _)) innerTy) =
    convertType innerTy
convertType (TApp (TConstructor (TypeConstructor "Option" _)) _innerTy) =
    LlvmAnonymous [LlvmI8, LlvmI64]
convertType (TApp (TApp (TConstructor (TypeConstructor "Either" _)) _leftTy) _rightTy) =
    LlvmAnonymous [LlvmI8, LlvmI64]
convertType (TArrow argTy retTy) =
    let argTypes = collectArgTypes argTy
        retType = convertType retTy
    in LlvmPointer (LlvmFn retType argTypes)
  where
    collectArgTypes (TArrow a b) = convertType a : collectArgTypes b
    collectArgTypes t = [convertType t]
convertType (TSkolem _) =
    error "Skolem type encountered during LLVM codegen. Types should be monomorphized first."
convertType tv@(TVar (TypeVar vid _)) =
    error $ "Type variable '" ++ vid ++ "' encountered during LLVM codegen. Types should be monomorphized first. Full type: " ++ show tv
convertType (TUnresolved name) =
    error $ "Unresolved type " ++ name ++ " encountered during LLVM codegen."
convertType (TApp constructor arg) =
    case constructor of
        TConstructor (TypeConstructor name _) ->
            error $ "Unsupported type constructor in LLVM codegen: " ++ name ++ " applied to " ++ show arg
        _ -> error $ "Unsupported complex type application in LLVM codegen: " ++ show (TApp constructor arg)
convertType (TConstructor (TypeConstructor name _)) =
    error $ "Unsupported type constructor in LLVM codegen: " ++ name

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
