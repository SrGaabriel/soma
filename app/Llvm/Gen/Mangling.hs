module Llvm.Gen.Mangling where
import Typing.Types (Type (TConstructor, TApp), TyConstructor (tcName))
import Llvm.Gen.Types (typeToMonomorphicName)

mangleInstanceMethod :: String -> Type -> String -> String
mangleInstanceMethod className concreteType methodName =
    className ++ "_" ++ typeToMonomorphicName concreteType ++ "_" ++ methodName

extractConstraintParts :: Type -> (String, Type)
extractConstraintParts (TApp (TConstructor tc) concreteType) = (tcName tc, concreteType)
extractConstraintParts t = error $ "Invalid constraint type: " ++ show t