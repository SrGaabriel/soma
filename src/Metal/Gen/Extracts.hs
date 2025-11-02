module Metal.Gen.Extracts where
import Typing.Types
import Syntax.Tree
import Data.Map (Map)
import Metal.Module (MetallicInstance (..))
import Metal.Function (MetallicFunction)
import qualified Data.Map as Map

extractParamNames :: Expr -> Int -> [String]
extractParamNames (ExprLambda params _ _) _ = params
extractParamNames _ n = ["arg" ++ show i | i <- [0..n-1]]

extractInstanceInfo :: Type -> (String, Type)
extractInstanceInfo (TApp (TConstructor (TypeConstructor className _)) instanceType) = (className, instanceType)
extractInstanceInfo ty = error $ "Invalid instance constraint: " ++ show ty

groupInstanceMethods :: Map (String, Type, String) MetallicFunction -> [MetallicInstance]
groupInstanceMethods methodMap = 
    Map.elems $ Map.fromListWith (\(MetallicInstance cn it ms1) (MetallicInstance _ _ ms2) -> 
                                    MetallicInstance cn it (ms1 ++ ms2))
        [ (key, MetallicInstance className instanceType [method])
        | ((className, instanceType, _), method) <- Map.toList methodMap
        , let key = (className, instanceType)
        ]