module Inference.Core where

import qualified Data.Map as Map
import Project.Symbols (Symbol)
import Syntax.Tree (Expr)
import Typing.Types (QualifiedType)

type TypeEnv = Map.Map Symbol QualifiedType

type TypeMap = Map.Map Expr QualifiedType

type InstanceEnv = Map.Map QualifiedType Bool

data UnificationPurpose
    = UnifyFunctionBody
    | UnifyFunctionApplication
    | UnifyPatternMatchArmBody
    | UnifyPatternMatchArms
    | UnifyPatternConstructor
    | UnifyIfCondition
    | UnifyIfElseBranches
    deriving (Show, Eq)
