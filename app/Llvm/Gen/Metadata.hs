module Llvm.Gen.Metadata where
import Typing.Types (Type)

data ConstructorMetadata = ConstructorMetadata
    {
    constructorMetadataTypeName :: String,
    constructorMetadataTag :: Int,
    constructorMetadataArgs :: [Type]
    } deriving (Show, Eq)