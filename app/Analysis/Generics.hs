module Analysis.Generics where

import qualified Data.Map as Map
import Parsing.Type (StructConstructor (StructConstructor, constructorFields), Type (..))

collectGenerics :: Type -> [String]
collectGenerics (GenericType g _) = [g]
collectGenerics (TupleType ts) = concatMap collectGenerics ts
collectGenerics (FunctionType arg ret) = collectGenerics arg ++ collectGenerics ret
collectGenerics (StructType _ variants mgs) =
    concatMap (collectGenerics . snd) (concatMap Map.toList (Prelude.map constructorFields variants))
        ++ maybe [] (concatMap collectGenerics) mgs
collectGenerics (UnresolvedStructType _ mgs) = maybe [] (concatMap collectGenerics) mgs
collectGenerics _ = []

replaceGenerics :: Map.Map String Type -> Type -> Type
replaceGenerics subst (GenericType g c) = Map.findWithDefault (GenericType g c) g subst
replaceGenerics subst (TupleType ts) = TupleType (Prelude.map (replaceGenerics subst) ts)
replaceGenerics subst (FunctionType arg ret) =
    FunctionType (replaceGenerics subst arg) (replaceGenerics subst ret)
replaceGenerics subst (StructType n variants mgs) =
    StructType
        n
        (Prelude.map (\v -> v{constructorFields = Map.map (replaceGenerics subst) (constructorFields v)}) variants)
        (fmap (Prelude.map (replaceGenerics subst)) mgs)
replaceGenerics subst (UnresolvedStructType n mgs) =
    UnresolvedStructType n (fmap (Prelude.map (replaceGenerics subst)) mgs)
replaceGenerics _ t = t

replaceGeneric :: Type -> Type -> Type -> Type
replaceGeneric genType@(GenericType generic _) newType ty = case ty of
    GenericType g _ | g == generic -> newType
    FunctionType arg ret -> FunctionType (replaceGeneric genType newType arg) (replaceGeneric genType newType ret)
    TupleType ts -> TupleType (map (replaceGeneric genType newType) ts)
    StructType name variants generics ->
        StructType
            name
            (map (replaceInVariant genType newType) variants)
            (fmap (map (replaceGeneric genType newType)) generics)
    UnresolvedStructType name generics ->
        UnresolvedStructType name (fmap (map (replaceGeneric genType newType)) generics)
    IntType -> IntType
    StringType -> StringType
    BoolType -> BoolType
    _ -> ty
replaceGeneric _ _ ty = ty

data Constraint = ClassConstraint String

replaceInVariant :: Type -> Type -> StructConstructor -> StructConstructor
replaceInVariant generic newType (StructConstructor vName fields) =
    StructConstructor vName (Map.map (replaceGeneric generic newType) fields)
