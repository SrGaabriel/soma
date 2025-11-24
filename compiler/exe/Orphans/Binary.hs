{-# OPTIONS_GHC -Wno-orphans #-}

module Orphans.Binary where

import Alloy.Ir
import Data.Binary (Binary)
import Metal.Metadata (MetallicTypeClassMetadata)
import Typing.Types

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

instance Binary AlloyModule

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
