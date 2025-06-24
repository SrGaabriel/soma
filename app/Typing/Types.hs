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
    | TUnresolved String
    deriving (Show, Eq, Ord)

data Constraint = Constraint Name [Type] deriving (Show, Eq, Ord)

data QualifiedType = Forall [TyVar] [Constraint] Type
    deriving (Show, Eq, Ord)

intType, strType, boolType :: Type
intType = TConstructor (TypeConstructor "Int" KindStar)
strType = TConstructor (TypeConstructor "String" KindStar)
boolType = TConstructor (TypeConstructor "Bool" KindStar)

cleanQualified :: Type -> QualifiedType
cleanQualified t = Forall [] [] t

arrayType :: Type -> Type
arrayType = TApp (TConstructor (TypeConstructor "Array" (KindArrow KindStar KindStar)))

tupleType :: [Type] -> Type
tupleType [] = TConstructor (TypeConstructor "Unit" KindStar)
tupleType types = foldr1 TApp (map (TApp (TConstructor (TypeConstructor "Tuple" KindStar))) types)

assignConstraints :: QualifiedType -> Type -> QualifiedType
assignConstraints (Forall vars constraints _) =
    Forall vars constraints

sumQualifiedTypes :: QualifiedType -> [QualifiedType] -> QualifiedType
sumQualifiedTypes original [] = original
sumQualifiedTypes (Forall vars constraints t) others =
    let newVars = vars ++ concatMap (\(Forall v _ _) -> v) others
        newConstraints = constraints ++ concatMap (\(Forall _ c _) -> c) others
    in Forall newVars newConstraints t

substituteReturnType :: Type -> Type -> Type
substituteReturnType (TArrow arg ret@(TArrow _ _)) new =
    TArrow arg (substituteReturnType ret new)
substituteReturnType (TArrow arg _) new =
    TArrow arg new
substituteReturnType t _ = t

substituteReturnTypeQualified :: QualifiedType -> Type -> QualifiedType
substituteReturnTypeQualified (Forall vars constraints t) new =
    Forall vars constraints (substituteReturnType new t)