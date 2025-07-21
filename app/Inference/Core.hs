module Inference.Core where

import Syntax.Tree (Expr)
import Typing.Types (QualifiedType, Type)

import qualified Data.Map as Map
import Project.Symbols (Symbol)

type TypeEnv = Map.Map Symbol QualifiedType
type TypeMap = Map.Map Expr QualifiedType

type InstanceEnv = Map.Map (String, Type) Bool

data UnificationPurpose
    = UnifyFunctionBody
    | UnifyFunctionApplication
    | UnifyPatternMatchArmBody
    | UnifyPatternMatchArms
    deriving (Show, Eq)
