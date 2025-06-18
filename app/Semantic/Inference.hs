module Semantic.Inference where

import qualified Data.Map as Map
import Typing.Types (QualifiedType)

type TypeEnv = Map.Map String QualifiedType
