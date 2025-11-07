{-# LANGUAGE NamedFieldPuns #-}

module Alloy.ExpandIntrinsics (
    expandIntrinsicsModule,
) where

import Alloy.Ir
import Data.List (isPrefixOf)

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
        Just $ OpBin IAdd (args !! 0) (args !! 1)
    | callee == "-" && length args == 2 =
        Just $ OpBin ISub (args !! 0) (args !! 1)
    | callee == "*" && length args == 2 =
        Just $ OpBin IMul (args !! 0) (args !! 1)
    | callee == "/" && length args == 2 =
        Just $ OpBin IDiv (args !! 0) (args !! 1)
    | callee == "%" && length args == 2 =
        Just $ OpBin IMod (args !! 0) (args !! 1)
    | callee == "&" && length args == 2 =
        Just $ OpBin And (args !! 0) (args !! 1)
    | callee == "|" && length args == 2 =
        Just $ OpBin Or (args !! 0) (args !! 1)
    | callee == "^" && length args == 2 =
        Just $ OpBin Xor (args !! 0) (args !! 1)
    | callee == "==" && length args == 2 =
        Just $ OpCmp CEq (args !! 0) (args !! 1)
    | callee == "!=" && length args == 2 =
        Just $ OpCmp CNe (args !! 0) (args !! 1)
    | callee == "<" && length args == 2 =
        Just $ OpCmp CSlt (args !! 0) (args !! 1)
    | callee == "<=" && length args == 2 =
        Just $ OpCmp CSle (args !! 0) (args !! 1)
    | callee == ">" && length args == 2 =
        Just $ OpCmp CSgt (args !! 0) (args !! 1)
    | callee == ">=" && length args == 2 =
        Just $ OpCmp CSge (args !! 0) (args !! 1)
    | callee == "neg" && length args == 1 =
        Just $ OpUnary Neg (args !! 0)
    | callee == "not" && length args == 1 =
        Just $ OpUnary Not (args !! 0)
    | otherwise = Nothing
