module Metal.Metadata where
import Typing.Types

data MetallicConstructorMetadata = MetallicConstructorMetadata
    { mcmTypeName :: String
    , mcmTag :: Int
    , mcmFields :: [Type]
    }
    deriving (Show, Eq)

data MetallicTypeClassMetadata = MetallicTypeClassMetadata
    { mtcName :: String
    , mtcTypeVars :: [TyVar]
    , mtcMethods :: [(String, QualifiedType)]
    }
    deriving (Show)