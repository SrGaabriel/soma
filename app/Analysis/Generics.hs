module Analysis.Generics where

import Control.Monad.Writer (Writer, execWriter, tell)
import Data.Maybe (fromMaybe)
import Parsing.Type (StructConstructor (StructConstructor), Type (..), mapType, mapTypeM)

collectGenerics :: Type -> [String]
collectGenerics t = execWriter (mapTypeM collect t)
  where
    collect :: Type -> Writer [String] Type
    collect ty@(GenericType g _) = tell [g] >> return ty
    collect ty = return ty

replaceGenerics :: [(String, Type)] -> Type -> Type
replaceGenerics subst = mapType f
  where
    f (GenericType g c) = fromMaybe (GenericType g c) (lookup g subst)
    f t = t

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
    StructConstructor vName (map (\(name, typ) -> (name, replaceGeneric generic newType typ)) fields)
