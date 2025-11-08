{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Alloy.Verify (
    VerificationConfig (..),
    VerificationError (..),
    VerificationReport (..),
    defaultVerificationConfig,
    verifyModule,
    verifyFunction,
    hasErrors,
    errorCount,
) where

import Alloy.Ir
import Data.Char (toLower)
import Data.List (isInfixOf)
import Typing.Types (Type)

data VerificationConfig = VerificationConfig
    { banHeapAllocOps :: Bool
    , bannedCalleeSubstrings :: [String]
    , bannedExactCallees :: [String]
    , banIndirectCalls :: Bool
    }
    deriving (Eq, Show)

defaultVerificationConfig :: VerificationConfig
defaultVerificationConfig =
    VerificationConfig
        { banHeapAllocOps = True
        , bannedCalleeSubstrings = toLowerList bannedSubstrings
        , bannedExactCallees = toLowerList bannedExact
        , banIndirectCalls = False
        }
  where
    toLowerList = map (map toLower)
    bannedSubstrings =
        [ "malloc"
        , "calloc"
        , "realloc"
        , "posix_memalign"
        , "aligned_alloc"
        , "valloc"
        , "memalign"
        , "_aligned_malloc"
        , "heapalloc"
        , "virtualalloc"
        ]
    bannedExact =
        [ "free"
        , "_aligned_free"
        , "heapfree"
        , "virtualfree" -- Win32
        , "operator new"
        , "operator delete"
        , "new"
        , "delete"
        ]

data VerificationError
    = HeapAllocFound
        { veFunction :: Name
        , veBlock :: BlockName
        , veInstrIndex :: Int
        , veType :: Type
        }
    | BannedCallFound
        { veFunction :: Name
        , veBlock :: BlockName
        , veInstrIndex :: Int
        , veCallee :: Name
        }
    | IndirectCallFound
        { veFunction :: Name
        , veBlock :: BlockName
        , veInstrIndex :: Int
        }
    deriving (Eq, Show)

newtype VerificationReport = VerificationReport
    { vrErrors :: [VerificationError]
    }
    deriving (Eq, Show)

hasErrors :: VerificationReport -> Bool
hasErrors = not . null . vrErrors

errorCount :: VerificationReport -> Int
errorCount = length . vrErrors

verifyModule :: VerificationConfig -> AlloyModule -> VerificationReport
verifyModule cfg AlloyModule{amFunctions} =
    VerificationReport{vrErrors = concatMap (verifyFunction cfg) amFunctions}

verifyFunction :: VerificationConfig -> AlloyFunction -> [VerificationError]
verifyFunction cfg AlloyFunction{afName, afBlocks} =
    concatMap (verifyBlock cfg afName) afBlocks

verifyBlock :: VerificationConfig -> Name -> ABlock -> [VerificationError]
verifyBlock cfg funName ABlock{..} =
    concat (zipWith (verifyInstr cfg funName abName) [0 ..] abInstrs)

verifyInstr :: VerificationConfig -> Name -> BlockName -> Int -> AInstr -> [VerificationError]
verifyInstr cfg funName blkName idx instr =
    case instr of
        ILet _ _ op -> verifyOp cfg funName blkName idx op
        IEffect _ -> []

verifyOp :: VerificationConfig -> Name -> BlockName -> Int -> AOp -> [VerificationError]
verifyOp VerificationConfig{..} funName blkName idx op =
    case op of
        OpAllocHeap ty ->
            [HeapAllocFound funName blkName idx ty | banHeapAllocOps]
        OpCall callee _args ->
            case callee of
                Direct name ->
                    [BannedCallFound funName blkName idx name | isBannedCallee name]
                Indirect _ ->
                    [IndirectCallFound funName blkName idx | banIndirectCalls]
        _ -> []
  where
    isBannedCallee :: Name -> Bool
    isBannedCallee nm =
        let lowerName = map toLower nm
        in lowerName `elem` bannedExactCallees
            || any (`isInfixOf` lowerName) bannedCalleeSubstrings
