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
    { tcName :: String -- todo: use better names
    , tcKind :: Kind
    }
    deriving (Show, Eq, Ord)

data Type
    = TVar TyVar
    | TConstructor TyConstructor
    | TApp Type Type
    | TArrow Type Type
    | TForall TyVar Type
    | TTuple [Type]
    | TConstrained [Constraint] Type
    | TUnresolved String Kind
    deriving (Show, Eq, Ord)

data Constraint = Constraint Name [Type] deriving (Show, Eq, Ord)

intType :: Type
intType = TConstructor (TypeConstructor "Int" (KindStar))

strType :: Type
strType = TConstructor (TypeConstructor "String" (KindStar))

boolType :: Type
boolType = TConstructor (TypeConstructor "Bool" (KindStar))

isFunc :: Type -> Bool
isFunc (TArrow _ _) = True
isFunc (TConstrained _ (TArrow _ _)) = True
isFunc _ = False

extractFunc :: Type -> Type
extractFunc (TArrow t1 t2) = TArrow t1 t2
extractFunc (TConstrained _ (TArrow t1 t2)) = TArrow t1 t2
extractFunc t = error $ "Expected function type, got: " ++ show t
