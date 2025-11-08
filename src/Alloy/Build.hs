{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Alloy.Build (
    AlloyBuilder,
    runAlloyBuilder,
    beginFunction,
    endFunction,
    beginBlock,
    terminate,
    emitLetAs,
    emitLetTmp,
    emitEffect,
    freshName,
    freshBlockName,
    module Alloy.Ir,
) where

import Control.Monad (when)
import Control.Monad.State.Strict
import Typing.Types (Type)

import Alloy.Ir
import Data.Maybe (isNothing)

data BuildState = BuildState
    { bsModuleName :: String
    , bsFunctions :: [AlloyFunction]
    , bsNextTmp :: !Int
    , bsNextBlk :: !Int
    , bsCurFun :: Maybe FunBuild
    , bsCurBlk :: Maybe BlockBuild
    }

data FunBuild = FunBuild
    { fbName :: Name
    , fbParams :: [(Name, Type)]
    , fbReturnType :: Type
    , fbEntry :: Maybe BlockName
    , fbBlocks :: [ABlock]
    }

data BlockBuild = BlockBuild
    { bbName :: BlockName
    , bbParams :: [(Name, Type)]
    , bbInstrs :: [AInstr]
    , bbTerminator :: Maybe ATerminator
    }

type AlloyBuilder = State BuildState

runAlloyBuilder :: String -> AlloyBuilder a -> (a, AlloyModule)
runAlloyBuilder modName action =
    let initState =
            BuildState
                { bsModuleName = modName
                , bsFunctions = []
                , bsNextTmp = 0
                , bsNextBlk = 0
                , bsCurFun = Nothing
                , bsCurBlk = Nothing
                }
        (res, st) = runState action initState
        mdl =
            AlloyModule
                { amName = bsModuleName st
                , amFunctions = bsFunctions st
                }
    in (res, mdl)

beginFunction :: Name -> [(Name, Type)] -> Type -> AlloyBuilder ()
beginFunction name params retTy = do
    st@BuildState{..} <- get
    when (isJust bsCurFun)
        $ error "Alloy.Build: beginFunction called while another function is open"
    let fb =
            FunBuild
                { fbName = name
                , fbParams = params
                , fbReturnType = retTy
                , fbEntry = Nothing
                , fbBlocks = []
                }
    put st{bsCurFun = Just fb, bsCurBlk = Nothing}

endFunction :: AlloyBuilder ()
endFunction = do
    st@BuildState{..} <- get
    FunBuild{..} <- requireOpenFunction "endFunction"

    when (isJust bsCurBlk)
        $ error "Alloy.Build: endFunction called but current block is not terminated"

    entryName <- case fbEntry of
        Nothing -> error "Alloy.Build: endFunction with no entry block"
        Just e -> pure e

    let fn =
            AlloyFunction
                { afName = fbName
                , afParams = fbParams
                , afReturnType = fbReturnType
                , afEntry = entryName
                , afBlocks = fbBlocks
                }
    put
        st
            { bsFunctions = bsFunctions ++ [fn]
            , bsCurFun = Nothing
            , bsCurBlk = Nothing
            }

beginBlock :: BlockName -> [(Name, Type)] -> AlloyBuilder ()
beginBlock name params = do
    st@BuildState{..} <- get
    fb@FunBuild{..} <- requireOpenFunction "beginBlock"

    -- Check current block is terminated if it exists
    case bsCurBlk of
        Just BlockBuild{bbTerminator = Nothing} ->
            error "Alloy.Build: switching blocks before terminating the current block"
        _ -> pure ()

    let newBlk =
            BlockBuild
                { bbName = name
                , bbParams = params
                , bbInstrs = []
                , bbTerminator = Nothing
                }
        fb' = if isNothing fbEntry then fb{fbEntry = Just name} else fb
    put st{bsCurFun = Just fb', bsCurBlk = Just newBlk}

terminate :: ATerminator -> AlloyBuilder ()
terminate term = do
    st <- get
    fb@FunBuild{..} <- requireOpenFunction "terminate"
    BlockBuild{..} <- requireOpenBlock "terminate"

    when (isJust bbTerminator)
        $ error "Alloy.Build: block already has a terminator"

    let finalized =
            ABlock
                { abName = bbName
                , abParams = bbParams
                , abInstrs = bbInstrs
                , abTerminator = term
                }
        fb' = fb{fbBlocks = fbBlocks ++ [finalized]}
    put st{bsCurFun = Just fb', bsCurBlk = Nothing}

emitLetAs :: Name -> Type -> AOp -> AlloyBuilder ()
emitLetAs name ty op = do
    st <- get
    blk@BlockBuild{..} <- requireOpenBlock "emitLetAs"

    when (isJust bbTerminator)
        $ error "Alloy.Build: cannot emit instructions after terminator"

    let instr = ILet name ty op
    put st{bsCurBlk = Just blk{bbInstrs = bbInstrs ++ [instr]}}

emitLetTmp :: Type -> AOp -> AlloyBuilder Name
emitLetTmp ty op = do
    name <- freshName
    emitLetAs name ty op
    pure name

emitEffect :: AEffect -> AlloyBuilder ()
emitEffect eff = do
    st <- get
    blk@BlockBuild{..} <- requireOpenBlock "emitEffect"

    when (isJust bbTerminator)
        $ error "Alloy.Build: cannot emit instructions after terminator"

    let instr = IEffect eff
    put st{bsCurBlk = Just blk{bbInstrs = bbInstrs ++ [instr]}}

freshName :: AlloyBuilder Name
freshName = do
    st@BuildState{..} <- get
    put st{bsNextTmp = bsNextTmp + 1}
    pure $ "t" ++ show bsNextTmp

freshBlockName :: AlloyBuilder BlockName
freshBlockName = do
    st@BuildState{..} <- get
    put st{bsNextBlk = bsNextBlk + 1}
    pure $ "block" ++ show bsNextBlk

-- | Helper to require an open function, throwing a descriptive error if none
requireOpenFunction :: String -> AlloyBuilder FunBuild
requireOpenFunction context = do
    st <- get
    case bsCurFun st of
        Just fb -> pure fb
        Nothing -> error $ "Alloy.Build: " ++ context ++ " called with no open function"

-- | Helper to require an open block, throwing a descriptive error if none
requireOpenBlock :: String -> AlloyBuilder BlockBuild
requireOpenBlock context = do
    st <- get
    case bsCurBlk st of
        Just blk -> pure blk
        Nothing -> error $ "Alloy.Build: " ++ context ++ " called with no open block"

-- | Helper to check if a Maybe value is Just
isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust Nothing = False
