{-# LANGUAGE NamedFieldPuns #-}

module Alloy.ExpandIntrinsics (
    expandIntrinsicsModule,
) where

import Alloy.Ir (
    ABinOpKind (And, IAdd, IDiv, IMod, IMul, ISub, Or, Xor),
    ABlock (ABlock, abInstrs),
    ACallable (Direct),
    ACmpOp (CEq, CNe, CSge, CSgt, CSle, CSlt),
    AInstr (ILet),
    AOp (OpBin, OpCall, OpCmp, OpUnary),
    AOperand,
    AUnaryOpKind (Neg, Not),
    AlloyFunction (AlloyFunction, afBlocks),
    AlloyModule (AlloyModule, amFunctions),
 )
import Utils.Lists (hardHead)

expandIntrinsicsModule :: AlloyModule -> AlloyModule
expandIntrinsicsModule m@AlloyModule{amFunctions} =
    m{amFunctions = map expandIntrinsicsFunction amFunctions}

expandIntrinsicsFunction :: AlloyFunction -> AlloyFunction
expandIntrinsicsFunction fn@AlloyFunction{afBlocks} =
    fn{afBlocks = map expandIntrinsicsBlock afBlocks}

expandIntrinsicsBlock :: ABlock -> ABlock
expandIntrinsicsBlock blk@ABlock{abInstrs} =
    blk{abInstrs = map expandIntrinsicsInstr abInstrs}

expandIntrinsicsInstr :: AInstr -> AInstr
expandIntrinsicsInstr (ILet name ty op) =
    ILet name ty (expandIntrinsicsOp op)
expandIntrinsicsInstr instr = instr

expandIntrinsicsOp :: AOp -> AOp
expandIntrinsicsOp (OpCall (Direct callee) args) =
    case expandIntrinsicCall callee args of
        Just expandedOp -> expandedOp
        Nothing -> OpCall (Direct callee) args
expandIntrinsicsOp op = op

expandIntrinsicCall :: String -> [AOperand] -> Maybe AOp
expandIntrinsicCall callee args
    | callee == "+" && length args == 2 =
        Just $ OpBin IAdd (hardHead args) (args !! 1)
    | callee == "-" && length args == 2 =
        Just $ OpBin ISub (hardHead args) (args !! 1)
    | callee == "*" && length args == 2 =
        Just $ OpBin IMul (hardHead args) (args !! 1)
    | callee == "/" && length args == 2 =
        Just $ OpBin IDiv (hardHead args) (args !! 1)
    | callee == "%" && length args == 2 =
        Just $ OpBin IMod (hardHead args) (args !! 1)
    | callee == "&" && length args == 2 =
        Just $ OpBin And (hardHead args) (args !! 1)
    | callee == "|" && length args == 2 =
        Just $ OpBin Or (hardHead args) (args !! 1)
    | callee == "^" && length args == 2 =
        Just $ OpBin Xor (hardHead args) (args !! 1)
    | callee == "==" && length args == 2 =
        Just $ OpCmp CEq (hardHead args) (args !! 1)
    | callee == "!=" && length args == 2 =
        Just $ OpCmp CNe (hardHead args) (args !! 1)
    | callee == "<" && length args == 2 =
        Just $ OpCmp CSlt (hardHead args) (args !! 1)
    | callee == "<=" && length args == 2 =
        Just $ OpCmp CSle (hardHead args) (args !! 1)
    | callee == ">" && length args == 2 =
        Just $ OpCmp CSgt (hardHead args) (args !! 1)
    | callee == ">=" && length args == 2 =
        Just $ OpCmp CSge (hardHead args) (args !! 1)
    | callee == "neg" && length args == 1 =
        Just $ OpUnary Neg (hardHead args)
    | callee == "not" && length args == 1 =
        Just $ OpUnary Not (hardHead args)
    | otherwise = Nothing
