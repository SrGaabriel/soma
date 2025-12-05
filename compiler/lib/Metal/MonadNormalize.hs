{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NamedFieldPuns #-}

{- HLINT ignore "Use newtype instead of data" -}

module Metal.MonadNormalize (
    normalizeModule,
    normalizeFunction,
    normalizeExpr,
) where

import Control.Monad.State.Strict
import Metal.Expr
import Metal.Function
import Metal.Module

normalizeModule :: MetallicModule -> MetallicModule
normalizeModule m@MetallicModule{mmFunctions} =
    m{mmFunctions = map normalizeFunction mmFunctions}

normalizeFunction :: MetallicFunction -> MetallicFunction
normalizeFunction fn@MetallicFunction{mfBody} =
    fn{mfBody = normalizeExpr mfBody}

normalizeExpr :: TypedExpr -> TypedExpr
normalizeExpr e = evalState (go e) initialState
  where
    initialState = NormalizeState{nsCounter = 0}

    go :: TypedExpr -> NormalizeM TypedExpr
    go (MVar n t s) = pure (MVar n t s)
    go (MLit lit s) = pure (MLit lit s)
    go (MCall f args t s) = do
        f' <- go f
        args' <- mapM go args
        pure (MCall f' args' t s)
    go (MTypeApp e' tys t s) = do
        e'' <- go e'
        pure (MTypeApp e'' tys t s)
    go (MLet n v b t s) = do
        v' <- go v
        b' <- go b
        pure (MLet n v' b' t s)
    go (MLambda ps b t s) = do
        b' <- go b
        pure (MLambda ps b' t s)
    go (MConstruct tn tag fs t s) = do
        fs' <- mapM go fs
        pure (MConstruct tn tag fs' t s)
    go (MArrayLit xs t s) = do
        xs' <- mapM go xs
        pure (MArrayLit xs' t s)
    go (MTuple xs t s) = do
        xs' <- mapM go xs
        pure (MTuple xs' t s)
    go (MCase scr arms mdef t s) = do
        scr' <- mapM go scr
        arms' <- mapM normArm arms
        mdef' <- mapM go mdef
        pure (MCase scr' arms' mdef' t s)
      where
        normArm :: TypedArm -> NormalizeM TypedArm
        normArm (MCaseArm ps b) = do
            b' <- go b
            pure (MCaseArm ps b')
    go (MFieldAccess e' idx t s) = do
        e'' <- go e'
        pure (MFieldAccess e'' idx t s)
    go (MPanic msg t s) = pure (MPanic msg t s)
    go (MIf cond thenE elseE t s) = do
        cond' <- go cond
        thenE' <- go thenE
        elseE' <- go elseE
        pure (MIf cond' thenE' elseE' t s)
    go (MClosure liftedName capturedVars t s) =
        pure (MClosure liftedName capturedVars t s)

type NormalizeM = State NormalizeState

data NormalizeState = NormalizeState
    { nsCounter :: !Int
    }
