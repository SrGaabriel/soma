module Parsing.Type (Type (..), TypeVar (..), StructVariant (..), GenericConstraint (..), mapType, mapTypeM) where

import qualified Data.Map as Map

data Type
    = IntType
    | StringType
    | BoolType
    | TupleType [Type]
    | FunctionType
        { functionTypeArg :: Type
        , functionTypeReturn :: Type
        }
    | GenericType
        { genericName :: String
        , genericConstraints :: [String]
        }
    | StructType
        { structName :: String
        , structVariants :: [StructVariant]
        , structGenerics :: Maybe [Type]
        }
    | ClassType String -- todo: maybe revise this approach later?
    | UnresolvedStructType String (Maybe [Type])
    | UnresolvedVarType TypeVar
    deriving (Eq, Ord)

data TypeVar = TypeVar String Int
    deriving (Show, Eq, Ord)

data TypeStruct = TypeStruct String Int
    deriving (Show, Eq, Ord)

instance Show Type where
    show IntType = "Int"
    show StringType = "String"
    show BoolType = "Bool"
    show (TupleType ts) = "(" ++ unwords (map show ts) ++ ")"
    show (FunctionType arg ret) = "(" ++ show arg ++ " -> " ++ show ret ++ ")"
    show (GenericType name constraints) = "'" ++ name ++ unwords (map (\c -> " : " ++ c) constraints)
    show (StructType name _ generics) = name ++ maybe "" (\g -> "[" ++ unwords (map show g) ++ "]") generics
    show (UnresolvedVarType v) = show v
    show (UnresolvedStructType name generics) = "@" ++ name ++ maybe "" (\g -> "[" ++ unwords (map show g) ++ "]") generics
    show (ClassType name) = name

mapType :: (Type -> Type) -> Type -> Type
mapType f (TupleType ts) = TupleType (map (mapType f) ts)
mapType f (FunctionType arg ret) = FunctionType (mapType f arg) (mapType f ret)
mapType f (StructType name variants mgs) =
    StructType
        name
        (map (\v -> v{variantFields = Map.map (mapType f) (variantFields v)}) variants)
        (fmap (map (mapType f)) mgs)
mapType f (UnresolvedStructType name mgs) = UnresolvedStructType name (fmap (map (mapType f)) mgs)
mapType f t = f t

mapTypeM :: (Monad m) => (Type -> m Type) -> Type -> m Type
mapTypeM f (TupleType ts) = do
    ts' <- mapM (mapTypeM f) ts
    f (TupleType ts')
mapTypeM f (FunctionType arg ret) = do
    arg' <- mapTypeM f arg
    ret' <- mapTypeM f ret
    f (FunctionType arg' ret')
mapTypeM f (StructType name variants mgs) = do
    variants' <-
        mapM
            ( \v -> do
                newFields <- traverse (mapTypeM f) (variantFields v)
                return v{variantFields = newFields}
            )
            variants
    mgs' <- mapM (mapM (mapTypeM f)) mgs
    f (StructType name variants' mgs')
mapTypeM f (UnresolvedStructType name mgs) = do
    mgs' <- mapM (mapM (mapTypeM f)) mgs
    f (UnresolvedStructType name mgs')
mapTypeM f t = f t

data StructVariant = StructVariant
    { variantName :: String
    , variantFields :: Map.Map String Type
    }
    deriving (Show, Eq, Ord)

data GenericConstraint = GenericConstraint
    { constraintGenericName :: String
    , constraintClassName :: String
    }
    deriving (Show, Eq, Ord)
