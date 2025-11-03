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
    case bsCurFun of
        Just _ -> error "Alloy.Build: beginFunction called while another function is open"
        Nothing -> do
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
    case bsCurFun of
        Nothing -> error "Alloy.Build: endFunction called but no function is open"
        Just FunBuild{..} -> do
            case bsCurBlk of
                Just _ -> error "Alloy.Build: endFunction called but current block is not terminated"
                Nothing -> pure ()
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
    case bsCurFun of
        Nothing -> error "Alloy.Build: beginBlock called with no open function"
        Just fb@FunBuild{..} -> do
            case bsCurBlk of
                Just BlockBuild{..} ->
                    case bbTerminator of
                        Nothing -> error "Alloy.Build: switching blocks before terminating the current block"
                        Just _ -> pure ()
                Nothing -> pure ()
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
    st@BuildState{..} <- get
    case (bsCurFun, bsCurBlk) of
        (Nothing, _) -> error "Alloy.Build: terminate called with no open function"
        (_, Nothing) -> error "Alloy.Build: terminate called with no open block"
        (Just fb@FunBuild{..}, Just BlockBuild{..}) -> do
            case bbTerminator of
                Just _ -> error "Alloy.Build: block already has a terminator"
                Nothing -> do
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
    st@BuildState{..} <- get
    case bsCurBlk of
        Nothing -> error "Alloy.Build: emitLetAs called with no open block"
        Just blk@BlockBuild{..} ->
            case bbTerminator of
                Just _ -> error "Alloy.Build: cannot emit instructions after terminator"
                Nothing -> do
                    let instr = ILet name ty op
                    put st{bsCurBlk = Just blk{bbInstrs = bbInstrs ++ [instr]}}

emitLetTmp :: Type -> AOp -> AlloyBuilder Name
emitLetTmp ty op = do
    name <- freshName
    emitLetAs name ty op
    pure name

emitEffect :: AEffect -> AlloyBuilder ()
emitEffect eff = do
    st@BuildState{..} <- get
    case bsCurBlk of
        Nothing -> error "Alloy.Build: emitEffect called with no open block"
        Just blk@BlockBuild{..} ->
            case bbTerminator of
                Just _ -> error "Alloy.Build: cannot emit instructions after terminator"
                Nothing -> do
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
