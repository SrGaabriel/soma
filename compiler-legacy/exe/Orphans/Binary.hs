{-# OPTIONS_GHC -Wno-orphans #-}

module Orphans.Binary where

import Alloy.Ir
import Data.Binary (Binary)
import Metal.Metadata (FunctionAttributes, MetallicTypeClassMetadata)
import Project.Name (DictId, DictKind, Intrinsic, LocalId, LocalPrefix, PrimOp, Projection, RuntimeFn, SyntheticId, SyntheticKind)
import Project.Unique (Unique)
import Typing.Types

instance Binary Unique

instance Binary LocalPrefix

instance Binary LocalId

instance Binary SyntheticKind

instance Binary SyntheticId

instance Binary RuntimeFn

instance Binary PrimOp

instance Binary Intrinsic

instance Binary Projection

instance Binary DictKind

instance Binary DictId

instance Binary Name

instance Binary TyPrimitive

instance Binary TyUnique

instance Binary FlexInfo

instance Binary Rigidity

instance Binary SkolemVar

instance Binary TyConstructor

instance Binary TyVar

instance Binary Kind

instance Binary Type

instance Binary Constraint

instance Binary QualifiedType

instance Binary MetallicTypeClassMetadata

instance Binary FunctionAttributes

instance Binary AlloyModule

instance Binary AlloyTypeDef

instance Binary AlloyConstructor

instance Binary DictionaryDef

instance Binary AlloyFunction

instance Binary ABlock

instance Binary AInstr

instance Binary AOperand

instance Binary AConst

instance Binary ACallable

instance Binary AOp

instance Binary AEffect

instance Binary ATerminator

instance Binary ABinOpKind

instance Binary AUnaryOpKind

instance Binary ACmpOp
