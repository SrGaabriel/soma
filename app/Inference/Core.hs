module Inference.Core where

import Project.Name (Name)
import Syntax.Tree (Expr)
import Typing.Types (QualifiedType, Type)

import qualified Data.Map as Map

type TypeEnv = Map.Map Name QualifiedType
type TypeMap = Map.Map Expr QualifiedType
type ClassEnv = Map.Map Name QualifiedType

type InstanceEnv = Map.Map (String, Type) Bool

data UnificationPurpose
    = UnifyFunctionBody
    | UnifyFunctionApplication
    | UnifyPatternMatchArmBody
    | UnifyPatternMatchArms
    deriving (Show, Eq)
