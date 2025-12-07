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
    Name,
 )
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Project.Name (nameToString)

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

data IntrinsicSpec
    = BinOp ABinOpKind
    | CmpOp ACmpOp
    | UnaryOp AUnaryOpKind

intrinsicTable :: Map String IntrinsicSpec
intrinsicTable =
    Map.fromList
        [ ("+", BinOp IAdd)
        , ("-", BinOp ISub)
        , ("*", BinOp IMul)
        , ("/", BinOp IDiv)
        , ("%", BinOp IMod)
        , ("&", BinOp And)
        , ("|", BinOp Or)
        , ("^", BinOp Xor)
        , ("==", CmpOp CEq)
        , ("!=", CmpOp CNe)
        , ("<", CmpOp CSlt)
        , ("<=", CmpOp CSle)
        , (">", CmpOp CSgt)
        , (">=", CmpOp CSge)
        , ("neg", UnaryOp Neg)
        , ("not", UnaryOp Not)
        ]

expandIntrinsicCall :: Name -> [AOperand] -> Maybe AOp
expandIntrinsicCall callee args = do
    spec <- Map.lookup (nameToString callee) intrinsicTable
    case (spec, args) of
        (BinOp op, [a, b]) -> Just $ OpBin op a b
        (CmpOp op, [a, b]) -> Just $ OpCmp op a b
        (UnaryOp op, [a]) -> Just $ OpUnary op a
        _ -> Nothing
