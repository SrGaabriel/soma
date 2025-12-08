{-# LANGUAGE LambdaCase #-}

module Alloy.Subst (
    Subst,
    substOperand,
    substCallable,
    substOp,
    substEffect,
    substTerminator,
    substInstr,
    substBlock,
    operandVars,
    opVars,
    effectVars,
    terminatorVars,
    instrVars,
) where

import Alloy.Ir
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- Name is re-exported from Alloy.Ir

-- | Substitution map from variable names to operands
type Subst = Map Name AOperand

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
    OpSelect c t f -> OpSelect (sub c) (sub t) (sub f)
    OpLoad a -> OpLoad (sub a)
    OpAllocStack t -> OpAllocStack t
    OpAllocHeap t -> OpAllocHeap t
    OpCall callee args -> OpCall (substCallable env callee) (map sub args)
    OpConstruct tn tag fields -> OpConstruct tn tag (map sub fields)
    OpTagOf a -> OpTagOf (sub a)
    OpArrayLength a -> OpArrayLength (sub a)
    OpCons elem arr -> OpCons (sub elem) (sub arr)
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
    -- Specialized closure duplication
    OpDupClosure label closure slotInfo -> OpDupClosure label (sub closure) slotInfo
    OpDupClosureProj0 handle envSz slotInfo -> OpDupClosureProj0 (sub handle) envSz slotInfo
    OpDupClosureProj1 handle envSz slotInfo -> OpDupClosureProj1 (sub handle) envSz slotInfo
    OpClosureGetEnvDirect closure idx -> OpClosureGetEnvDirect (sub closure) idx
    OpClosureGetEnvSUP closure idx -> OpClosureGetEnvSUP (sub closure) idx
    -- Parallel projection
    OpParProj0 handle work -> OpParProj0 (sub handle) work
    OpParProj1 handle work -> OpParProj1 (sub handle) work
    OpParClosureProj0 handle envSz slotInfo work ->
        OpParClosureProj0 (sub handle) envSz slotInfo work
    OpParClosureProj1 handle envSz slotInfo work ->
        OpParClosureProj1 (sub handle) envSz slotInfo work
    -- Panic (no operands to substitute)
    OpPanic msg -> OpPanic msg
    -- Graph reduction operations
    OpGraphInit n -> OpGraphInit n
    OpGraphShutdown -> OpGraphShutdown
    OpGraphNum v -> OpGraphNum (sub v)
    OpGraphAdd l r -> OpGraphAdd (sub l) (sub r)
    OpGraphSub l r -> OpGraphSub (sub l) (sub r)
    OpGraphMul l r -> OpGraphMul (sub l) (sub r)
    OpGraphDiv l r -> OpGraphDiv (sub l) (sub r)
    OpGraphMod l r -> OpGraphMod (sub l) (sub r)
    OpGraphCall fnIdx args -> OpGraphCall fnIdx (map sub args)
    OpGraphReduce root -> OpGraphReduce (sub root)
    OpGraphExtractNum term -> OpGraphExtractNum (sub term)
    OpGraphRegisterFunc name arity impl -> OpGraphRegisterFunc name arity (sub impl)
    -- Graph reduction interaction net operations
    OpGraphDup label target -> OpGraphDup label (sub target)
    OpGraphDupGetProj0 dup -> OpGraphDupGetProj0 (sub dup)
    OpGraphDupGetProj1 dup -> OpGraphDupGetProj1 (sub dup)
    OpGraphSup label l r -> OpGraphSup label (sub l) (sub r)
    OpGraphLam varSlot body -> OpGraphLam (sub varSlot) (sub body)
    OpGraphApp fn arg -> OpGraphApp (sub fn) (sub arg)
    OpGraphEra -> OpGraphEra
    OpGraphCon fstOp sndOp -> OpGraphCon (sub fstOp) (sub sndOp)
    OpGraphConGet conOp idx -> OpGraphConGet (sub conOp) idx
    OpGraphRef name idx arg -> OpGraphRef name idx (sub arg)
    OpGraphClosure funcIdx arity envVals -> OpGraphClosure funcIdx arity (map sub envVals)
    OpGraphClosureApp clo arg -> OpGraphClosureApp (sub clo) (sub arg)
    OpGraphClosureGetEnv clo idx -> OpGraphClosureGetEnv (sub clo) idx
    OpFork fn args -> OpFork (sub fn) (map sub args)
    OpJoin handle -> OpJoin (sub handle)
  where
    sub = substOperand env

-- | Substitute variables in an effect
substEffect :: Map Name AOperand -> AEffect -> AEffect
substEffect env = \case
    EffStore p v -> EffStore (sub p) (sub v)
    EffStoreIndex a i v -> EffStoreIndex (sub a) (sub i) (sub v)
    EffDrop a -> EffDrop (sub a)
    EffClosureSetEnv closure idx val -> EffClosureSetEnv (sub closure) idx (sub val)
    EffGraphInit n -> EffGraphInit n
    EffGraphShutdown -> EffGraphShutdown
    EffGraphRegisterFunc name arity impl -> EffGraphRegisterFunc name arity (sub impl)
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
    OpSelect c t f -> vars c ++ vars t ++ vars f
    OpLoad a -> vars a
    OpAllocStack _ -> []
    OpAllocHeap _ -> []
    OpCall callee args -> callableVars callee ++ concatMap vars args
    OpConstruct _ _ fields -> concatMap vars fields
    OpTagOf a -> vars a
    OpArrayLength a -> vars a
    OpCons elem arr -> vars elem ++ vars arr
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
    OpPanic _ -> []
    OpGraphInit _ -> []
    OpGraphShutdown -> []
    OpGraphNum v -> vars v
    OpGraphAdd l r -> vars l ++ vars r
    OpGraphSub l r -> vars l ++ vars r
    OpGraphMul l r -> vars l ++ vars r
    OpGraphDiv l r -> vars l ++ vars r
    OpGraphMod l r -> vars l ++ vars r
    OpGraphCall _ args -> concatMap vars args
    OpGraphReduce root -> vars root
    OpGraphExtractNum term -> vars term
    OpGraphRegisterFunc _ _ impl -> vars impl
    OpGraphDup _ target -> vars target
    OpGraphDupGetProj0 dup -> vars dup
    OpGraphDupGetProj1 dup -> vars dup
    OpGraphSup _ l r -> vars l ++ vars r
    OpGraphLam varSlot body -> vars varSlot ++ vars body
    OpGraphApp fn arg -> vars fn ++ vars arg
    OpGraphEra -> []
    OpGraphCon fstOp sndOp -> vars fstOp ++ vars sndOp
    OpGraphConGet conOp _ -> vars conOp
    OpGraphRef _ _ arg -> vars arg
    OpGraphClosure _ _ envVals -> concatMap vars envVals
    OpGraphClosureApp clo arg -> vars clo ++ vars arg
    OpGraphClosureGetEnv clo _ -> vars clo
    OpFork fn args -> vars fn ++ concatMap vars args
    OpJoin h -> vars h
  where
    vars = operandVars

-- | Get all variables referenced in an effect
effectVars :: AEffect -> [Name]
effectVars = \case
    EffStore p v -> operandVars p ++ operandVars v
    EffStoreIndex a i v -> operandVars a ++ operandVars i ++ operandVars v
    EffDrop a -> operandVars a
    EffClosureSetEnv c _ v -> operandVars c ++ operandVars v
    EffGraphInit _ -> []
    EffGraphShutdown -> []
    EffGraphRegisterFunc _ _ impl -> operandVars impl

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
