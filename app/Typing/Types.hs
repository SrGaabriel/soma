module Typing.Types where

data Kind
    = KindStar -- 
    | KindArrow Kind Kind
    deriving (Show, Eq, Ord)

data TyVar = TypeVar
    { tvName :: String
    , tvKind :: Kind
    } deriving (Show, Eq, Ord)

data TyConstructor = TypeConstructor
    { tcName :: String -- todo: use better names
    , tcKind :: Kind
    } deriving (Show, Eq, Ord)

data Type
    = TVar TyVar
    | TConstructor TyConstructor
    | TApp Type Type
    | TArrow Type Type
    | TForall TyVar Type
    deriving (Show, Eq, Ord)

intType :: Type
intType = TConstructor (TypeConstructor "Int" (KindStar))

newtype Planet x = Planet Type 