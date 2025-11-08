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

normalizeExpr :: MetallicExpr -> MetallicExpr
normalizeExpr e = evalState (go e) initialState
  where
    initialState = NormalizeState{nsCounter = 0}

    go :: MetallicExpr -> NormalizeM MetallicExpr
    go (MVar n t) = pure (MVar n t)
    go (MLit lit) = pure (MLit lit)
    go (MCall f args t) = do
        f' <- go f
        args' <- mapM go args
        pure (MCall f' args' t)
    go (MTypeApp e' tys t) = do
        e'' <- go e'
        pure (MTypeApp e'' tys t)
    go (MLet n v b t) = do
        v' <- go v
        b' <- go b
        pure (MLet n v' b' t)
    go (MLambda ps b t) = do
        b' <- go b
        pure (MLambda ps b' t)
    go (MConstruct tn tag fs t) = do
        fs' <- mapM go fs
        pure (MConstruct tn tag fs' t)
    go (MArrayLit xs t) = do
        xs' <- mapM go xs
        pure (MArrayLit xs' t)
    go (MTuple xs t) = do
        xs' <- mapM go xs
        pure (MTuple xs' t)
    go (MCase scr arms mdef t) = do
        scr' <- mapM go scr
        arms' <- mapM normArm arms
        mdef' <- mapM go mdef
        pure (MCase scr' arms' mdef' t)
      where
        normArm :: MCaseArm -> NormalizeM MCaseArm
        normArm (MCaseArm ps b) = do
            b' <- go b
            pure (MCaseArm ps b')
    go (MFieldAccess e' idx t) = do
        e'' <- go e'
        pure (MFieldAccess e'' idx t)
    go (MPanic msg t) = pure (MPanic msg t)
    go (MCompose stmts t) = do
        stmts' <- mapM normComposeStmt stmts
        pure (MCompose stmts' t)
    go (MIf cond thenE elseE t) = do
        cond' <- go cond
        thenE' <- go thenE
        elseE' <- go elseE
        pure (MIf cond' thenE' elseE' t)

    normComposeStmt :: MetallicComposeStmt -> NormalizeM MetallicComposeStmt
    normComposeStmt (MCBind n e') = do
        e'' <- go e'
        pure (MCBind n e'')
    normComposeStmt (MCLet n e') = do
        e'' <- go e'
        pure (MCLet n e'')
    normComposeStmt (MCExpr e') = do
        e'' <- go e'
        pure (MCExpr e'')

type NormalizeM = State NormalizeState

data NormalizeState = NormalizeState
    { nsCounter :: !Int
    }
