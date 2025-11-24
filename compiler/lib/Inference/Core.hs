module Inference.Core where

import qualified Data.Map as Map
import Project.Symbols (Symbol)
import Syntax.Tree (Expr)
import Typing.Types (QualifiedType, Type)

type TypeEnv = Map.Map Symbol QualifiedType

type TypeMap = Map.Map Expr QualifiedType

type InstanceEnv = Map.Map Type Bool

data UnificationPurpose
    = UnifyFunctionBody
    | UnifyFunctionApplication
    | UnifyPatternMatchArmBody
    | UnifyPatternMatchArms
    | UnifyIfCondition
    | UnifyIfElseBranches
    deriving (Show, Eq)
