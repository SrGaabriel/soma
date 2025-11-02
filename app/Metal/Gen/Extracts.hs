module Metal.Gen.Extracts where
import Typing.Types
import Syntax.Tree

extractParamNames :: Expr -> Int -> [String]
extractParamNames (ExprLambda params _ _) _ = params
extractParamNames _ n = ["arg" ++ show i | i <- [0..n-1]]

extractInstanceInfo :: Type -> (String, Type)
extractInstanceInfo (TApp (TConstructor (TypeConstructor className _)) instanceType) = (className, instanceType)
extractInstanceInfo ty = error $ "Invalid instance constraint: " ++ show ty