
module Analysis.Generics where
import Parsing.Type (Type(..), StructVariant (variantFields))
import qualified Data.Map as Map

collectGenerics :: Type -> [String]
collectGenerics (GenericType g) = [g]
collectGenerics (TupleType ts) = concatMap collectGenerics ts
collectGenerics (FunctionType args ret) = concatMap collectGenerics args ++ collectGenerics ret
collectGenerics (StructType _ variants mgs) = 
    concatMap (collectGenerics . snd) (concatMap Map.toList (Prelude.map variantFields variants)) ++ 
    maybe [] (concatMap collectGenerics) mgs
collectGenerics (UnresolvedStructType _ mgs) = maybe [] (concatMap collectGenerics) mgs
collectGenerics _ = []

replaceGenerics :: Map.Map String Type -> Type -> Type
replaceGenerics subst (GenericType g) = Map.findWithDefault (GenericType g) g subst
replaceGenerics subst (TupleType ts) = TupleType (Prelude.map (replaceGenerics subst) ts)
replaceGenerics subst (FunctionType args ret) = 
    FunctionType (Prelude.map (replaceGenerics subst) args) (replaceGenerics subst ret)
replaceGenerics subst (StructType n variants mgs) = 
    StructType n 
               (Prelude.map (\v -> v { variantFields = Map.map (replaceGenerics subst) (variantFields v) }) variants)
               (fmap (Prelude.map (replaceGenerics subst)) mgs)
replaceGenerics subst (UnresolvedStructType n mgs) = 
    UnresolvedStructType n (fmap (Prelude.map (replaceGenerics subst)) mgs)
replaceGenerics _ t = t