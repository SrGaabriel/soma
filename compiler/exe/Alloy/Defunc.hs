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
    in m{amFunctions = map (defunctionalizeFunction fnNames) amFunctions}

defunctionalizeFunction :: Set Name -> AlloyFunction -> AlloyFunction
defunctionalizeFunction knownFns fn@AlloyFunction{afBlocks} =
    fn{afBlocks = map (rewriteBlock knownFns) afBlocks}

rewriteBlock :: Set Name -> ABlock -> ABlock
rewriteBlock known b@ABlock{abInstrs, abTerminator} =
    b
        { abInstrs = map (rewriteInstr known) abInstrs
        , abTerminator = rewriteTerm known abTerminator
        }

rewriteInstr :: Set Name -> AInstr -> AInstr
rewriteInstr known (ILet n ty op) = ILet n ty (rewriteOp known op)
rewriteInstr _ instr@(IEffect _) = instr

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
        OpGetDict className ty -> OpGetDict className ty
        OpDictCall dict methodIdx method args -> OpDictCall dict methodIdx method args

rewriteCallable :: Set Name -> ACallable -> ACallable
rewriteCallable known (Indirect (OpVar n))
    | n `Set.member` known = Direct n
rewriteCallable _ callable = callable

rewriteTerm :: Set Name -> ATerminator -> ATerminator
rewriteTerm _ t = t
