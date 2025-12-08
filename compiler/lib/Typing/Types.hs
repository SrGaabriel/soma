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
    arrayType,
    constraintClassName,
    constraintTypes,
    constraintType,
    cleanQualified,
    assignConstraints,
    sumQualifiedTypes,
    extractTyVars,
    getUnknownTypeConstructorName,
    isFunctionType,
    tupleType,
    splitFunctionType,
    countArityFromType,
    extractTupleTypes,
    extractArrayElemType,
    extractTypeArgs,
) where

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

intType, strType, boolType, byteType, closurePtrType, unitType :: Type
intType = TConstructor (TypeConstructor (TyPrim TPInt) KindStar)
strType = TConstructor (TypeConstructor (TyPrim TPString) KindStar)
boolType = TConstructor (TypeConstructor (TyPrim TPBool) KindStar)
byteType = TConstructor (TypeConstructor (TyPrim TPByte) KindStar)
closurePtrType = TConstructor (TypeConstructor (TyPrim TPClosurePtr) KindStar)
unitType = TConstructor (TypeConstructor (TyPrim TPUnit) KindStar)

cleanQualified :: Type -> QualifiedType
cleanQualified = Forall [] []

arrayType :: Type -> Type
arrayType = TApp (TConstructor (TypeConstructor (TyPrim TPArray) (KindArrow KindStar KindStar)))

tupleType :: [Type] -> Type
tupleType [] = unitType
tupleType types =
    let n = length types
    in foldr1 TApp (map (TApp (TConstructor (TypeConstructor (TyPrim (TPTuple n)) KindStar))) types)

assignConstraints :: QualifiedType -> Type -> QualifiedType
assignConstraints (Forall vars constraints _) =
    Forall vars constraints

sumQualifiedTypes :: QualifiedType -> [QualifiedType] -> QualifiedType
sumQualifiedTypes original [] = original
sumQualifiedTypes (Forall vars constraints t) others =
    let newVars = vars ++ concatMap (\(Forall v _ _) -> v) others
        newConstraints = constraints ++ concatMap (\(Forall _ c _) -> c) others
    in Forall newVars newConstraints t

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

getUnknownTypeConstructorName :: QualifiedType -> Maybe String
getUnknownTypeConstructorName (Forall _ _ t) = getConstructorName t
  where
    getConstructorName (TConstructor tc) = Just $ tyUniqueName (tcId tc)
    getConstructorName (TUnresolved name) = Just name
    getConstructorName (TApp t' _) = getConstructorName t'
    getConstructorName _ = Nothing

isFunctionType :: Type -> Bool
isFunctionType (TArrow _ _) = True
isFunctionType _ = False

splitFunctionType :: Int -> Type -> ([Type], Type)
splitFunctionType 0 ty = ([], ty)
splitFunctionType n (TArrow argTy restTy) =
    let (args, ret) = splitFunctionType (n - 1) restTy
    in (argTy : args, ret)
splitFunctionType _ ty = ([], ty)

countArityFromType :: Type -> Int
countArityFromType (TArrow _ rest) = 1 + countArityFromType rest
countArityFromType _ = 0

extractTupleTypes :: Type -> [Type]
extractTupleTypes (TApp (TApp (TConstructor (TypeConstructor (TyPrim (TPTuple 2)) _)) t1) t2) = [t1, t2]
extractTupleTypes (TApp (TApp (TApp (TConstructor (TypeConstructor (TyPrim (TPTuple 3)) _)) t1) t2) t3) = [t1, t2, t3]
extractTupleTypes (TApp t1 t2) = extractTupleTypes t1 ++ [t2]
extractTupleTypes _ = []

extractArrayElemType :: Type -> Type
extractArrayElemType (TApp (TConstructor (TypeConstructor (TyPrim TPArray) _)) elemTy) = elemTy
extractArrayElemType ty = ty

extractTypeArgs :: Type -> [Type]
extractTypeArgs (TApp f arg) = extractTypeArgs f ++ [arg]
extractTypeArgs _ = []
