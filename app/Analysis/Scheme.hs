module Analysis.Scheme (TypeScheme(..)) where

import Parsing.Type

data TypeScheme
    = Concrete Type
    | TypeVar Int
    | TypeLambda TypeScheme TypeScheme