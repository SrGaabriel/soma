module Inference.Core where

import qualified Data.Map as Map
import Metal.Expr (TypedExpr)
import Metal.Metadata (FunctionAttributes)
import Project.Name (Name)
import Project.Symbols (Symbol)
import Syntax.Tree (Expr)
import Typing.Types (Constraint, QualifiedType, TyVar, Type)

type TypeEnv = Map.Map Symbol QualifiedType

type TypeMap = Map.Map Expr QualifiedType

type InstanceEnv = Map.Map QualifiedType Bool

type TypedBinding = (Name, TypedExpr, [Type], Type, [TyVar], [Constraint], FunctionAttributes)

type TypedInstanceMethod = (Name, TypedExpr, [Type], Type)

type TypedInstance = (QualifiedType, [TypedInstanceMethod])

data UnificationPurpose
    = UnifyFunctionBody
    | UnifyFunctionApplication
    | UnifyPatternMatchArmBody
    | UnifyPatternMatchArms
    | UnifyPatternConstructor
    | UnifyIfCondition
    | UnifyIfElseBranches
    deriving (Show, Eq)
