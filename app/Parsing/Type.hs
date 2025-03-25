module Parsing.Type (Type(..), TypeVar(..), StructVariant(..)) where
import qualified Data.Map as Map

data Type
    = IntType
    | StringType
    | BoolType
    | TupleType [Type]
    | FunctionType
        { functionTypeArgs :: [Type]
        , functionTypeReturn :: Type
        }
    | GenericType String
    | StructType
        { structName :: String
        , structVariants :: [StructVariant]
        }
    | UnboundedStructType String
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
    show (FunctionType args ret) = "(" ++ unwords (map show args) ++ " -> " ++ show ret ++ ")"
    show (GenericType n) = "<" ++ n ++ ">"
    show (StructType name _) = name
    show (UnresolvedVarType v) = show v
    show (UnboundedStructType s) = show s

data StructVariant = StructVariant
    { variantName :: String
    , variantFields :: Map.Map String Type
    } deriving (Show, Eq, Ord)