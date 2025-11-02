module Llvm.Gen.Mangling where

import Data.Hashable (Hashable (hash))
import Llvm.Types (LlvmType)
import Typing.Types (TyConstructor (tcName), Type (TApp, TConstructor))
import qualified Debug.Trace as Debug

mangleDataTypeName :: String -> String
mangleDataTypeName typeName = typeName ++ "_dt" -- todo mangle

mangleMonomorphizedName :: String -> [LlvmType] -> String
mangleMonomorphizedName baseName typeArgs =
    "mono_" ++ baseName ++ concatMap (("_" ++) . show . hash) typeArgs

mangleInstanceMethod :: String -> LlvmType -> String -> String
mangleInstanceMethod className concreteType methodName =
    let res = className ++ "_" ++ llvmTypeToMonomorphicName concreteType ++ "_" ++ methodName in
    Debug.trace ("Mangled instance method from class '" ++ className ++
                 "', type '" ++ show concreteType ++
                 "', method '" ++ methodName ++
                 "' to '" ++ res ++ "'") res

extractConstraintParts :: Type -> (String, Type)
extractConstraintParts (TApp (TConstructor tc) concreteType) = (tcName tc, concreteType)
extractConstraintParts t = error $ "Invalid constraint type: " ++ show t

llvmTypeToMonomorphicName :: LlvmType -> String
llvmTypeToMonomorphicName = show . hash
