{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}

module Typing.Types (
    Kind (..),

    TyVar (..),
    SkolemVar (..),
    Rigidity (..),
    FlexInfo (..),

    TyConstructor (..),
    tyUniqueName,

    TyUnique (..),
    TyPrimitive (..),
    primitiveName,
    isPrimitive,
    primitiveFromName,

    Type (..),
    Constraint (..),
    QualifiedType (..),

    intType,
    strType,
    boolType,
    byteType,
    closurePtrType,
    unitType,
    longType,
    shortType,
    floatType,
    doubleType,

    arrayType,
    tupleType,
    mkPrimTyCon,
    mkUserTyCon,
    mkConstraint,
    constraintClassName,
    constraintTypes,
    constraintType,
    cleanQualified,
    cleanQualifiedCollectingTyvars,
    assignConstraints,
    sumQualifiedTypes,
    substituteReturnType,
    substituteReturnTypeQualified,
    vectorize,
    vectorizeAll,
    vectorizeQualified,
    vectorizeAllQualified,
    extractTyVars,
    isPolymorphic,
    errType,
    errQualifiedType,
    getUnknownTypeConstructorName,
    typesMatch,
    isFunctionType,
) where

import Data.Hashable (Hashable (..))
import GHC.Generics (Generic)
import Project.Unique (Unique (..))

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
    { tcId :: !TyUnique
    , tcKind :: Kind
    }
    deriving (Generic, Show, Eq, Ord)

tyUniqueName :: TyUnique -> String
tyUniqueName (TyPrim p) = primitiveName p
tyUniqueName (TyUserDefined u) = uniqueOriginal u

data TyUnique
    = TyPrim !TyPrimitive
    | TyUserDefined !Unique
    deriving (Show, Eq, Ord, Generic)

instance Hashable TyUnique where
    hashWithSalt salt (TyPrim p) = salt `hashWithSalt` (0 :: Int) `hashWithSalt` p
    hashWithSalt salt (TyUserDefined u) = salt `hashWithSalt` (1 :: Int) `hashWithSalt` u

data TyPrimitive
    = TPInt
    | TPLong
    | TPShort
    | TPByte
    | TPFloat
    | TPDouble
    | TPBool
    | TPString
    | TPUnit
    | TPArray
    | TPTuple !Int
    | TPClosurePtr
    | TPPtr
    | TPRef
    | TPIO
    deriving (Show, Eq, Ord, Generic)

instance Hashable TyPrimitive where
    hashWithSalt salt p = hashWithSalt salt (fromEnum p)

instance Enum TyPrimitive where
    fromEnum TPInt = 0
    fromEnum TPLong = 1
    fromEnum TPShort = 2
    fromEnum TPByte = 3
    fromEnum TPFloat = 4
    fromEnum TPDouble = 5
    fromEnum TPBool = 6
    fromEnum TPString = 7
    fromEnum TPUnit = 8
    fromEnum TPArray = 9
    fromEnum (TPTuple n) = 10 + n -- Tuples get 10+arity (todo: review)
    fromEnum TPClosurePtr = 100
    fromEnum TPPtr = 101
    fromEnum TPRef = 102
    fromEnum TPIO = 103

    toEnum 0 = TPInt
    toEnum 1 = TPLong
    toEnum 2 = TPShort
    toEnum 3 = TPByte
    toEnum 4 = TPFloat
    toEnum 5 = TPDouble
    toEnum 6 = TPBool
    toEnum 7 = TPString
    toEnum 8 = TPUnit
    toEnum 9 = TPArray
    toEnum 100 = TPClosurePtr
    toEnum 101 = TPPtr
    toEnum 102 = TPRef
    toEnum 103 = TPIO
    toEnum n
        | n >= 10 && n < 100 = TPTuple (n - 10)
        | otherwise = error $ "Invalid TyPrimitive enum value: " ++ show n

primitiveName :: TyPrimitive -> String
primitiveName TPInt = "Int"
primitiveName TPLong = "Long"
primitiveName TPShort = "Short"
primitiveName TPByte = "Byte"
primitiveName TPFloat = "Float"
primitiveName TPDouble = "Double"
primitiveName TPBool = "Bool"
primitiveName TPString = "String"
primitiveName TPUnit = "Unit"
primitiveName TPArray = "Array"
primitiveName (TPTuple 0) = "Unit"
primitiveName (TPTuple n) = "Tuple" ++ show n
primitiveName TPClosurePtr = "ClosurePtr"
primitiveName TPPtr = "Ptr"
primitiveName TPRef = "Ref"
primitiveName TPIO = "IO"

isPrimitive :: TyUnique -> Bool
isPrimitive (TyPrim _) = True
isPrimitive (TyUserDefined _) = False

primitiveFromName :: String -> Maybe TyPrimitive
primitiveFromName "Int" = Just TPInt
primitiveFromName "Long" = Just TPLong
primitiveFromName "Short" = Just TPShort
primitiveFromName "Byte" = Just TPByte
primitiveFromName "Float" = Just TPFloat
primitiveFromName "Double" = Just TPDouble
primitiveFromName "Bool" = Just TPBool
primitiveFromName "String" = Just TPString
primitiveFromName "Unit" = Just TPUnit
primitiveFromName "()" = Just TPUnit
primitiveFromName "Array" = Just TPArray
primitiveFromName "ClosurePtr" = Just TPClosurePtr
primitiveFromName "Ptr" = Just TPPtr
primitiveFromName "Ref" = Just TPRef
primitiveFromName "IO" = Just TPIO
primitiveFromName _ = Nothing

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

mkConstraint :: TyUnique -> [Type] -> Constraint
mkConstraint classId typs =
    let classKind = foldr (const $ KindArrow KindStar) KindStar typs
        classCon = TConstructor (TypeConstructor classId classKind)
        appliedType = foldl TApp classCon typs
    in Constraint appliedType

constraintClassName :: Constraint -> String
constraintClassName (Constraint typ) = getClassName typ
  where
    getClassName (TConstructor tc) = tyUniqueName (tcId tc)
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
intType = TConstructor (TypeConstructor (TyPrim TPInt) KindStar)
strType = TConstructor (TypeConstructor (TyPrim TPString) KindStar)
boolType = TConstructor (TypeConstructor (TyPrim TPBool) KindStar)
byteType = TConstructor (TypeConstructor (TyPrim TPByte) KindStar)
closurePtrType = TConstructor (TypeConstructor (TyPrim TPClosurePtr) KindStar)

unitType :: Type
unitType = TConstructor (TypeConstructor (TyPrim TPUnit) KindStar)

longType :: Type
longType = TConstructor (TypeConstructor (TyPrim TPLong) KindStar)

shortType :: Type
shortType = TConstructor (TypeConstructor (TyPrim TPShort) KindStar)

floatType :: Type
floatType = TConstructor (TypeConstructor (TyPrim TPFloat) KindStar)

doubleType :: Type
doubleType = TConstructor (TypeConstructor (TyPrim TPDouble) KindStar)

cleanQualified :: Type -> QualifiedType
cleanQualified = Forall [] []

cleanQualifiedCollectingTyvars :: Type -> QualifiedType
cleanQualifiedCollectingTyvars t =
    let tyVars = extractTyVars t
    in Forall tyVars [] t

arrayType :: Type -> Type
arrayType = TApp (TConstructor (TypeConstructor (TyPrim TPArray) (KindArrow KindStar KindStar)))

tupleType :: [Type] -> Type
tupleType [] = unitType
tupleType types =
    let n = length types
    in foldr1 TApp (map (TApp (TConstructor (TypeConstructor (TyPrim (TPTuple n)) KindStar))) types)

mkPrimTyCon :: TyPrimitive -> Kind -> TyConstructor
mkPrimTyCon prim kind = TypeConstructor (TyPrim prim) kind

mkUserTyCon :: Unique -> Kind -> TyConstructor
mkUserTyCon u kind = TypeConstructor (TyUserDefined u) kind

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
    getConstructorName (TConstructor tc) = Just $ tyUniqueName (tcId tc)
    getConstructorName (TUnresolved name) = Just name
    getConstructorName (TApp t' _) = getConstructorName t'
    getConstructorName _ = Nothing

typesMatch :: Type -> Type -> Bool
typesMatch (TConstructor tc1) (TConstructor tc2) = tc1 == tc2
typesMatch (TApp f1 a1) (TApp f2 a2) = typesMatch f1 f2 && typesMatch a1 a2
typesMatch _ _ = False

isFunctionType :: Type -> Bool
isFunctionType (TArrow _ _) = True
isFunctionType _ = False
