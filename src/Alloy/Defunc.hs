{-# LANGUAGE NamedFieldPuns #-}

module Alloy.Defunc (
    defunctionalizeModule,
    defunctionalizeFunction,
) where

import Alloy.Ir
import Data.Set (Set)
import qualified Data.Set as Set

defunctionalizeModule :: AlloyModule -> AlloyModule
defunctionalizeModule m@AlloyModule{amFunctions} =
    let fnNames = Set.fromList (map afName amFunctions)
        amFunctions' = map (defunctionalizeFunction fnNames) amFunctions
    in m{amFunctions = amFunctions'}

defunctionalizeFunction :: Set Name -> AlloyFunction -> AlloyFunction
defunctionalizeFunction knownFns fn@AlloyFunction{afBlocks} =
    let afBlocks' = map (rewriteBlock knownFns) afBlocks
    in fn{afBlocks = afBlocks'}

rewriteBlock :: Set Name -> ABlock -> ABlock
rewriteBlock known b@ABlock{abInstrs, abTerminator} =
    let abInstrs' = map (rewriteInstr known) abInstrs
        abTerminator' = rewriteTerm known abTerminator
    in b{abInstrs = abInstrs', abTerminator = abTerminator'}

rewriteInstr :: Set Name -> AInstr -> AInstr
rewriteInstr known (ILet n ty op) = ILet n ty (rewriteOp known op)
rewriteInstr _ eff@(IEffect _) = eff

rewriteOp :: Set Name -> AOp -> AOp
rewriteOp known op =
    case op of
        OpBin k a b -> OpBin k a b
        OpUnary k a -> OpUnary k a
        OpCmp k a b -> OpCmp k a b
        OpLoad a -> OpLoad a
        OpAllocStack t -> OpAllocStack t
        OpAllocHeap t -> OpAllocHeap t
        OpCall callee args -> OpCall (rewriteCallable known callee) args
        OpConstruct tn tag fields -> OpConstruct tn tag fields
        OpTagOf a -> OpTagOf a
        OpProject a i -> OpProject a i
        OpIndex a i -> OpIndex a i
        OpMakeArray xs -> OpMakeArray xs
        OpMakeTuple xs -> OpMakeTuple xs

rewriteCallable :: Set Name -> ACallable -> ACallable
rewriteCallable known (Indirect (OpVar n))
    | n `Set.member` known = Direct n
rewriteCallable _ c = c

rewriteTerm :: Set Name -> ATerminator -> ATerminator
rewriteTerm _ t = t
