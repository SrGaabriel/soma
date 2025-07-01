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

data SkolemVar = SkolemVar
  { skName :: String
  , skKind :: Kind
  , skUnique :: Int
  , skRigidity :: Rigidity
  } deriving (Eq, Ord, Show)

data Rigidity 
  = Rigid
  | Flexible FlexInfo
  deriving (Eq, Ord, Show)

data FlexInfo = FlexInfo
  { flexLevel :: Int
  , flexOrigin :: String
  } deriving (Eq, Ord, Show)

data Type
    = TVar TyVar
    | TSkolem SkolemVar
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
cleanQualified = Forall [] []

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
extractTyVars (TVar tv) = [tv]
extractTyVars (TSkolem _) = []  -- skolem variables are not considered type variables
extractTyVars (TApp t1 t2) = extractTyVars t1 ++ extractTyVars t2
extractTyVars (TArrow t1 t2) = extractTyVars t1 ++ extractTyVars t2
extractTyVars (TConstructor _) = []
extractTyVars (TUnresolved _) = []