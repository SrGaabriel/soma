module Alloy.Subst (
    Subst,
    emptySubst,
    singleSubst,
    insertSubst,
    substOperand,
    substCallable,
    substOp,
    substEffect,
    substTerminator,
) where

import Alloy.Ir
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

type Subst = Map Name AOperand

emptySubst :: Subst
emptySubst = Map.empty

singleSubst :: Name -> AOperand -> Subst
singleSubst = Map.singleton

insertSubst :: Name -> AOperand -> Subst -> Subst
insertSubst = Map.insert

substOperand :: Subst -> AOperand -> AOperand
substOperand env (OpVar n) = Map.findWithDefault (OpVar n) n env
substOperand _ c@(OpConst _) = c

substCallable :: Subst -> ACallable -> ACallable
substCallable _ (Direct n) = Direct n
substCallable env (Indirect a) = Indirect (substOperand env a)

substOp :: Subst -> AOp -> AOp
substOp env op =
    case op of
        OpBin k a b -> OpBin k (substOperand env a) (substOperand env b)
        OpUnary k a -> OpUnary k (substOperand env a)
        OpCmp k a b -> OpCmp k (substOperand env a) (substOperand env b)
        OpLoad a -> OpLoad (substOperand env a)
        OpAllocStack t -> OpAllocStack t
        OpAllocHeap t -> OpAllocHeap t
        OpCall callee args -> OpCall (substCallable env callee) (map (substOperand env) args)
        OpConstruct tn tag fields -> OpConstruct tn tag (map (substOperand env) fields)
        OpTagOf a -> OpTagOf (substOperand env a)
        OpProject a i -> OpProject (substOperand env a) i
        OpIndex a i -> OpIndex (substOperand env a) (substOperand env i)
        OpMakeArray xs -> OpMakeArray (map (substOperand env) xs)
        OpMakeTuple xs -> OpMakeTuple (map (substOperand env) xs)
        OpGetDict className ty -> OpGetDict className ty
        OpDictCall dict methodIdx method args -> OpDictCall (substOperand env dict) methodIdx method (map (substOperand env) args)

substEffect :: Subst -> AEffect -> AEffect
substEffect env eff =
    case eff of
        EffStore p v -> EffStore (substOperand env p) (substOperand env v)
        EffStoreIndex a i v -> EffStoreIndex (substOperand env a) (substOperand env i) (substOperand env v)
        EffDrop a -> EffDrop (substOperand env a)

substTerminator :: Subst -> ATerminator -> ATerminator
substTerminator env t =
    case t of
        ABr b args -> ABr b (map (substOperand env) args)
        ACondBr c tb ta fb fa ->
            ACondBr
                (substOperand env c)
                tb
                (map (substOperand env) ta)
                fb
                (map (substOperand env) fa)
        ASwitch v cases mdef ->
            ASwitch (substOperand env v) cases mdef
        ARet mv -> ARet (fmap (substOperand env) mv)
        AUnreachable -> AUnreachable
