{-# LANGUAGE LambdaCase #-}

{- | Substitution utilities for Alloy IR.

This module provides functions for substituting operands in Alloy IR constructs.
These are used by various optimization passes (Simplify, Inline, CSE, etc.)
to avoid code duplication.
-}
module Alloy.Subst (
    -- * Type aliases
    Subst,

    -- * Substitution functions
    substOperand,
    substCallable,
    substOp,
    substEffect,
    substTerminator,
    substInstr,
    substBlock,

    -- * Variable extraction
    operandVars,
    opVars,
    effectVars,
    terminatorVars,
    instrVars,
) where

import Alloy.Ir
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Substitution map from variable names to operands
type Subst = Map Name AOperand

-- ============================================================================
-- Substitution Functions
-- ============================================================================

-- | Substitute a variable in an operand
substOperand :: Map Name AOperand -> AOperand -> AOperand
substOperand env (OpVar n) = Map.findWithDefault (OpVar n) n env
substOperand _ c@(OpConst _) = c

-- | Substitute a variable in a callable
substCallable :: Map Name AOperand -> ACallable -> ACallable
substCallable _ (Direct n) = Direct n
substCallable env (Indirect a) = Indirect (substOperand env a)

-- | Substitute variables in an operation
substOp :: Map Name AOperand -> AOp -> AOp
substOp env = \case
    OpBin k a b -> OpBin k (sub a) (sub b)
    OpUnary k a -> OpUnary k (sub a)
    OpCmp k a b -> OpCmp k (sub a) (sub b)
    OpLoad a -> OpLoad (sub a)
    OpAllocStack t -> OpAllocStack t
    OpAllocHeap t -> OpAllocHeap t
    OpCall callee args -> OpCall (substCallable env callee) (map sub args)
    OpConstruct tn tag fields -> OpConstruct tn tag (map sub fields)
    OpTagOf a -> OpTagOf (sub a)
    OpProject a i -> OpProject (sub a) i
    OpIndex a i -> OpIndex (sub a) (sub i)
    OpMakeArray xs -> OpMakeArray (map sub xs)
    OpMakeTuple xs -> OpMakeTuple (map sub xs)
    OpGetDict className ty -> OpGetDict className ty
    OpDictCall dict methodIdx method args ->
        OpDictCall (sub dict) methodIdx method (map sub args)
    -- Lazy duplication operations
    OpDup label val -> OpDup label (sub val)
    OpDupProj0 handle -> OpDupProj0 (sub handle)
    OpDupProj1 handle -> OpDupProj1 (sub handle)
    -- Closure operations
    OpWrapClosure fn -> OpWrapClosure (sub fn)
    OpAllocClosure fn arity envSz -> OpAllocClosure (sub fn) arity envSz
    OpClosureSetEnv closure idx val -> OpClosureSetEnv (sub closure) idx (sub val)
    OpClosureGetEnv closure idx -> OpClosureGetEnv (sub closure) idx
    OpClosureGetFunc closure -> OpClosureGetFunc (sub closure)
    -- Specialized closure duplication (Session 13)
    OpDupClosure label closure slotInfo -> OpDupClosure label (sub closure) slotInfo
    OpDupClosureProj0 handle envSz slotInfo -> OpDupClosureProj0 (sub handle) envSz slotInfo
    OpDupClosureProj1 handle envSz slotInfo -> OpDupClosureProj1 (sub handle) envSz slotInfo
    OpClosureGetEnvDirect closure idx -> OpClosureGetEnvDirect (sub closure) idx
    OpClosureGetEnvSUP closure idx -> OpClosureGetEnvSUP (sub closure) idx
    -- Parallel projection (Session 19)
    OpParProj0 handle work -> OpParProj0 (sub handle) work
    OpParProj1 handle work -> OpParProj1 (sub handle) work
    OpParClosureProj0 handle envSz slotInfo work ->
        OpParClosureProj0 (sub handle) envSz slotInfo work
    OpParClosureProj1 handle envSz slotInfo work ->
        OpParClosureProj1 (sub handle) envSz slotInfo work
  where
    sub = substOperand env

-- | Substitute variables in an effect
substEffect :: Map Name AOperand -> AEffect -> AEffect
substEffect env = \case
    EffStore p v -> EffStore (sub p) (sub v)
    EffStoreIndex a i v -> EffStoreIndex (sub a) (sub i) (sub v)
    EffDrop a -> EffDrop (sub a)
    EffClosureSetEnv closure idx val -> EffClosureSetEnv (sub closure) idx (sub val)
  where
    sub = substOperand env

-- | Substitute variables in a terminator
substTerminator :: Map Name AOperand -> ATerminator -> ATerminator
substTerminator env = \case
    ABr b args -> ABr b (map sub args)
    ACondBr c tb ta fb fa ->
        ACondBr (sub c) tb (map sub ta) fb (map sub fa)
    ASwitch v cases mdef -> ASwitch (sub v) cases mdef
    ARet mv -> ARet (fmap sub mv)
    AUnreachable -> AUnreachable
  where
    sub = substOperand env

-- | Substitute variables in an instruction
substInstr :: Map Name AOperand -> AInstr -> AInstr
substInstr env = \case
    ILet n t op -> ILet n t (substOp env op)
    IEffect eff -> IEffect (substEffect env eff)

-- | Substitute variables in a block (instructions and terminator only)
substBlock :: Map Name AOperand -> ABlock -> ABlock
substBlock env blk =
    blk
        { abInstrs = map (substInstr env) (abInstrs blk)
        , abTerminator = substTerminator env (abTerminator blk)
        }

-- ============================================================================
-- Variable Extraction Functions
-- ============================================================================

-- | Get variables referenced in an operand
operandVars :: AOperand -> [Name]
operandVars (OpVar n) = [n]
operandVars (OpConst _) = []

-- | Get variables referenced in a callable
callableVars :: ACallable -> [Name]
callableVars (Direct _) = []
callableVars (Indirect a) = operandVars a

-- | Get all variables referenced in an operation
opVars :: AOp -> [Name]
opVars = \case
    OpBin _ a b -> vars a ++ vars b
    OpUnary _ a -> vars a
    OpCmp _ a b -> vars a ++ vars b
    OpLoad a -> vars a
    OpAllocStack _ -> []
    OpAllocHeap _ -> []
    OpCall callee args -> callableVars callee ++ concatMap vars args
    OpConstruct _ _ fields -> concatMap vars fields
    OpTagOf a -> vars a
    OpProject a _ -> vars a
    OpIndex a i -> vars a ++ vars i
    OpMakeArray xs -> concatMap vars xs
    OpMakeTuple xs -> concatMap vars xs
    OpGetDict _ _ -> []
    OpDictCall d _ _ args -> vars d ++ concatMap vars args
    OpDup _ v -> vars v
    OpDupProj0 h -> vars h
    OpDupProj1 h -> vars h
    OpWrapClosure fn -> vars fn
    OpAllocClosure fn _ _ -> vars fn
    OpClosureSetEnv c _ v -> vars c ++ vars v
    OpClosureGetEnv c _ -> vars c
    OpClosureGetFunc c -> vars c
    OpDupClosure _ c _ -> vars c
    OpDupClosureProj0 h _ _ -> vars h
    OpDupClosureProj1 h _ _ -> vars h
    OpClosureGetEnvDirect c _ -> vars c
    OpClosureGetEnvSUP c _ -> vars c
    OpParProj0 h _ -> vars h
    OpParProj1 h _ -> vars h
    OpParClosureProj0 h _ _ _ -> vars h
    OpParClosureProj1 h _ _ _ -> vars h
  where
    vars = operandVars

-- | Get all variables referenced in an effect
effectVars :: AEffect -> [Name]
effectVars = \case
    EffStore p v -> operandVars p ++ operandVars v
    EffStoreIndex a i v -> operandVars a ++ operandVars i ++ operandVars v
    EffDrop a -> operandVars a
    EffClosureSetEnv c _ v -> operandVars c ++ operandVars v

-- | Get all variables referenced in a terminator
terminatorVars :: ATerminator -> [Name]
terminatorVars = \case
    ARet (Just op) -> operandVars op
    ARet Nothing -> []
    ABr _ args -> concatMap operandVars args
    ACondBr c _ ta _ fa -> operandVars c ++ concatMap operandVars ta ++ concatMap operandVars fa
    ASwitch v _ _ -> operandVars v
    AUnreachable -> []

-- | Get all variables referenced in an instruction
instrVars :: AInstr -> [Name]
instrVars = \case
    ILet _ _ op -> opVars op
    IEffect eff -> effectVars eff
