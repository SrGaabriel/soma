
module Analysis.Generics where
import Parsing.Type (Type(..), StructVariant (variantFields, StructVariant))
import qualified Data.Map as Map

collectGenerics :: Type -> [String]
collectGenerics (GenericType g) = [g]
collectGenerics (TupleType ts) = concatMap collectGenerics ts
collectGenerics (FunctionType arg ret) = collectGenerics arg ++ collectGenerics ret
collectGenerics (StructType _ variants mgs) = 
    concatMap (collectGenerics . snd) (concatMap Map.toList (Prelude.map variantFields variants)) ++ 
    maybe [] (concatMap collectGenerics) mgs
collectGenerics (UnresolvedStructType _ mgs) = maybe [] (concatMap collectGenerics) mgs
collectGenerics _ = []

replaceGenerics :: Map.Map String Type -> Type -> Type
replaceGenerics subst (GenericType g) = Map.findWithDefault (GenericType g) g subst
replaceGenerics subst (TupleType ts) = TupleType (Prelude.map (replaceGenerics subst) ts)
replaceGenerics subst (FunctionType arg ret) = 
    FunctionType (replaceGenerics subst arg) (replaceGenerics subst ret)
replaceGenerics subst (StructType n variants mgs) = 
    StructType n 
               (Prelude.map (\v -> v { variantFields = Map.map (replaceGenerics subst) (variantFields v) }) variants)
               (fmap (Prelude.map (replaceGenerics subst)) mgs)
replaceGenerics subst (UnresolvedStructType n mgs) = 
    UnresolvedStructType n (fmap (Prelude.map (replaceGenerics subst)) mgs)
replaceGenerics _ t = t

replaceGeneric :: Type -> Type -> Type -> Type
replaceGeneric genType@(GenericType generic) newType ty = case ty of
    GenericType g | g == generic -> newType
    FunctionType arg ret -> FunctionType (replaceGeneric genType newType arg) (replaceGeneric genType newType ret)
    StructType name variants (Just gs) | GenericType generic `elem` gs ->
        StructType name (Prelude.map (replaceInVariant genType newType) variants) (Just $ Prelude.map (replaceGeneric genType newType) gs)
    _ -> ty
replaceGeneric _ _ ty = ty

replaceInVariant :: Type -> Type -> StructVariant -> StructVariant
replaceInVariant generic newType (StructVariant vName fields) =
    StructVariant vName (Map.map (replaceGeneric generic newType) fields)