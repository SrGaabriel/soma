module Llvm.Gen.Mangling where

import Data.Hashable (Hashable (hash))
import Llvm.Types (LlvmType)
import Typing.Types (TyConstructor (tcName), Type (TApp, TConstructor))

mangleDataTypeName :: String -> String
mangleDataTypeName typeName = typeName ++ "_dt" -- todo mangle

mangleMonomorphizedName :: String -> [LlvmType] -> String
mangleMonomorphizedName baseName typeArgs =
    "mono_" ++ baseName ++ concatMap (("_" ++) . show . hash) typeArgs

mangleInstanceMethod :: String -> LlvmType -> String -> String
mangleInstanceMethod className concreteType methodName =
    className ++ "_" ++ llvmTypeToMonomorphicName concreteType ++ "_" ++ methodName

extractConstraintParts :: Type -> (String, Type)
extractConstraintParts (TApp (TConstructor tc) concreteType) = (tcName tc, concreteType)
extractConstraintParts t = error $ "Invalid constraint type: " ++ show t

llvmTypeToMonomorphicName :: LlvmType -> String
llvmTypeToMonomorphicName = show . hash
