{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}

module Typing.Types where

import GHC.Generics (Generic)

data Kind
    = KindStar
    | KindArrow Kind Kind
    deriving (Generic, Show, Eq, Ord)

data TyVar = TypeVar
    { tvId :: String
    , tvKind :: Kind
    }
    deriving (Generic, Show, Eq, Ord)

data TyConstructor = TypeConstructor
    { tcName :: String
    , tcKind :: Kind
    }
    deriving (Generic, Show, Eq, Ord)

data SkolemVar = SkolemVar
    { skId :: String
    , skKind :: Kind
    , skUnique :: Int
    , skName :: String
    , skRigidity :: Rigidity
    }
    deriving (Generic, Eq, Ord, Show)

data Rigidity
    = Rigid
    | Flexible FlexInfo
    deriving (Generic, Eq, Ord, Show)

data FlexInfo = FlexInfo
    { flexLevel :: Int
    , flexOrigin :: String
    }
    deriving (Generic, Eq, Ord, Show)

data Type
    = TVar TyVar
    | TSkolem SkolemVar
    | TConstructor TyConstructor
    | TApp Type Type
    | TArrow Type Type
    | TUnresolved String
    deriving (Generic, Show, Eq, Ord)

newtype Constraint = Constraint Type deriving (Generic, Show, Eq, Ord)

mkConstraint :: String -> [Type] -> Constraint
mkConstraint className typs =
    let classKind = foldr (const $ KindArrow KindStar) KindStar typs
        classCon = TConstructor (TypeConstructor className classKind)
        appliedType = foldl TApp classCon typs
    in Constraint appliedType

constraintClassName :: Constraint -> String
constraintClassName (Constraint typ) = getClassName typ
  where
    getClassName (TConstructor tc) = tcName tc
    getClassName (TApp t _) = getClassName t
    getClassName (TUnresolved name) = name
    getClassName _ = error "Invalid constraint type"

constraintTypes :: Constraint -> [Type]
constraintTypes (Constraint typ) = getTypes typ []
  where
    getTypes (TApp l r) acc = getTypes l (r : acc)
    getTypes (TConstructor _) acc = acc
    getTypes _ acc = acc

constraintType :: Constraint -> Type
constraintType (Constraint t) = t

data QualifiedType = Forall [TyVar] [Constraint] Type
    deriving (Generic, Show, Eq, Ord)

intType, strType, boolType, byteType, closurePtrType :: Type
intType = TConstructor (TypeConstructor "Int" KindStar)
strType = TConstructor (TypeConstructor "String" KindStar)
boolType = TConstructor (TypeConstructor "Bool" KindStar)
byteType = TConstructor (TypeConstructor "Byte" KindStar)

{- | Opaque pointer to a SomaClosure runtime structure
Used for uniform closure calling convention where all lifted functions
take closure_self as their first parameter
-}
closurePtrType = TConstructor (TypeConstructor "ClosurePtr" KindStar)

cleanQualified :: Type -> QualifiedType
cleanQualified = Forall [] []

cleanQualifiedCollectingTyvars :: Type -> QualifiedType
cleanQualifiedCollectingTyvars t =
    let tyVars = extractTyVars t
    in Forall tyVars [] t

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

vectorize :: Type -> Type -> Type
vectorize (TArrow arg ret) newRet = TArrow arg (vectorize ret newRet)
vectorize t newRet = TArrow t newRet

vectorizeAll :: [Type] -> Type
vectorizeAll [] = error "Cannot vectorize an empty list of types"
vectorizeAll [t] = t
vectorizeAll types = foldr1 TArrow types

vectorizeQualified :: QualifiedType -> QualifiedType -> QualifiedType
vectorizeQualified (Forall vars constraints t) (Forall vars' constraints' t') =
    let newVars = vars ++ vars'
        newConstraints = constraints ++ constraints'
    in Forall newVars newConstraints (TArrow t t')

vectorizeAllQualified :: [QualifiedType] -> QualifiedType
vectorizeAllQualified [] = error "Cannot vectorize an empty list of types"
vectorizeAllQualified [t] = t
vectorizeAllQualified types =
    let allVars = concatMap (\(Forall vars _ _) -> vars) types
        allConstraints = concatMap (\(Forall _ constraints _) -> constraints) types
        typesList = map (\(Forall _ _ t) -> t) types
        arrowType = foldr1 TArrow typesList
    in Forall allVars allConstraints arrowType

extractTyVars :: Type -> [TyVar]
extractTyVars t = nubTyVars (extractTyVars' t)
  where
    extractTyVars' (TVar tv) = [tv]
    extractTyVars' (TSkolem _) = []
    extractTyVars' (TApp t1 t2) = extractTyVars' t1 ++ extractTyVars' t2
    extractTyVars' (TArrow t1 t2) = extractTyVars' t1 ++ extractTyVars' t2
    extractTyVars' (TConstructor _) = []
    extractTyVars' (TUnresolved _) = []

    nubTyVars [] = []
    nubTyVars (x : xs) = x : nubTyVars (filter (/= x) xs)

isPolymorphic :: Type -> Bool
isPolymorphic (TVar _) = True
isPolymorphic (TSkolem _) = False
isPolymorphic (TApp t1 t2) = isPolymorphic t1 || isPolymorphic t2
isPolymorphic (TArrow t1 t2) = isPolymorphic t1 || isPolymorphic t2
isPolymorphic (TConstructor _) = False
isPolymorphic (TUnresolved _) = False

errType :: Type
errType = TUnresolved "ERROR"

errQualifiedType :: QualifiedType
errQualifiedType = Forall [] [] errType

getUnknownTypeConstructorName :: QualifiedType -> Maybe String
getUnknownTypeConstructorName (Forall _ _ t) = getConstructorName t
  where
    getConstructorName (TConstructor tc) = Just $ tcName tc
    getConstructorName (TUnresolved name) = Just name
    getConstructorName (TApp t' _) = getConstructorName t'
    getConstructorName _ = Nothing

typesMatch :: Type -> Type -> Bool
typesMatch (TConstructor tc1) (TConstructor tc2) = tc1 == tc2
typesMatch (TApp f1 a1) (TApp f2 a2) = typesMatch f1 f2 && typesMatch a1 a2
typesMatch _ _ = False
