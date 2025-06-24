module Inference.Core where

import Project.Name (Name)
import Typing.Types (QualifiedType)
import Syntax.Tree (Expr)

import qualified Data.Map as Map

type TypeEnv = Map.Map Name QualifiedType
type TypeMap = Map.Map Expr QualifiedType
type ClassEnv = Map.Map Name QualifiedType