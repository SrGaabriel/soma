module Inference.Core where

import qualified Data.Map as Map
import Metal.Expr (TypedExpr)
import Metal.Metadata (FunctionAttributes)
import Project.Symbols (Symbol)
import Syntax.Tree (Expr)
import Typing.Types (Constraint, QualifiedType, TyVar, Type)

type TypeEnv = Map.Map Symbol QualifiedType

type TypeMap = Map.Map Expr QualifiedType

type InstanceEnv = Map.Map QualifiedType Bool

type TypedBinding = (String, TypedExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)

data UnificationPurpose
    = UnifyFunctionBody
    | UnifyFunctionApplication
    | UnifyPatternMatchArmBody
    | UnifyPatternMatchArms
    | UnifyPatternConstructor
    | UnifyIfCondition
    | UnifyIfElseBranches
    deriving (Show, Eq)
