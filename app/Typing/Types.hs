module Typing.Types where

import Project.Name (Name)

data Kind
    = KindStar
    | KindArrow Kind Kind
    deriving (Show, Eq, Ord)

data TyVar = TypeVar
    { tvName :: String
    , tvKind :: Kind
    }
    deriving (Show, Eq, Ord)

data TyConstructor = TypeConstructor
    { tcName :: String
    , tcKind :: Kind
    }
    deriving (Show, Eq, Ord)

data Type
    = TVar TyVar
    | TConstructor TyConstructor
    | TApp Type Type
    | TArrow Type Type
    deriving (Show, Eq, Ord)

data Constraint = Constraint Name [Type] deriving (Show, Eq, Ord)

data QualifiedType = Forall [TyVar] [Constraint] Type
    deriving (Show, Eq, Ord)

intType, strType, boolType :: Type
intType = TConstructor (TypeConstructor "Int" KindStar)
strType = TConstructor (TypeConstructor "String" KindStar)
boolType = TConstructor (TypeConstructor "Bool" KindStar)

arrayType :: Type -> Type
arrayType elemType = TApp (TConstructor (TypeConstructor "Array" (KindArrow KindStar KindStar))) elemType

tupleType :: [Type] -> Type
tupleType [] = TConstructor (TypeConstructor "Unit" KindStar)
tupleType types = foldr1 TApp (map (\t -> TApp (TConstructor (TypeConstructor "Tuple" KindStar)) t) types)

assignConstraints :: QualifiedType -> Type -> QualifiedType
assignConstraints (Forall vars constraints _) t =
    Forall vars constraints t
