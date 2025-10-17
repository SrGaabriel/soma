module Llvm.Gen.Metadata where
import Typing.Types (Type)

data ConstructorMetadata = ConstructorMetadata
    {
    typeName :: String,
    tag :: Int,
    args :: [Type]
    } deriving (Show, Eq)