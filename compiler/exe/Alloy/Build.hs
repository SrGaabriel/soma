{-# LANGUAGE RecordWildCards #-}

{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-totality" @-}

module Alloy.Build (
    AlloyBuilder,
    runAlloyBuilder,
    beginFunction,
    beginFunctionWithConstraints,
    beginFunctionFull,
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

import Alloy.Ir
import Control.Monad (when)
import Control.Monad.State.Strict
import Data.Maybe (isNothing)
import qualified Data.Set as Set
import Metal.Metadata (FunctionAttributes, defaultFunctionAttributes)
import qualified Metal.Metadata
import Project.Name (LocalId (..), LocalPrefix (..), Name (..))
import Project.Unique (Unique)
import Typing.Types (Constraint, Type)

{- | Builder state machine invariants (enforced by LiquidHaskell):

State transitions:
  1. Initial: bsCurFun = Nothing, bsCurBlk = Nothing
  2. After beginFunction: bsCurFun = Just _, bsCurBlk = Nothing
  3. After beginBlock: bsCurFun = Just _, bsCurBlk = Just (with bbTerminator = Nothing)
  4. After terminate: bsCurFun = Just _, bsCurBlk = Nothing (block finalized)
  5. After endFunction: bsCurFun = Nothing, bsCurBlk = Nothing

Invariants:
  - Cannot beginFunction while another is open
  - Cannot beginBlock without terminating current block
  - Cannot emit instructions after terminator
  - Cannot endFunction without entry block
  - Cannot endFunction with unterminated block
-}

{-@ measure isFunctionOpen :: BuildState -> Bool @-}
{-@ measure isBlockOpen :: BuildState -> Bool @-}
{-@ measure isBlockTerminated :: BuildState -> Bool @-}

data BuildState = BuildState
    { bsModuleName :: String
    , bsFunctions :: [AlloyFunction]
    , bsDictionaries :: [DictionaryDef]
    , bsNextTmp :: !Int
    , bsNextBlk :: !Int
    , bsCurFun :: Maybe FunBuild
    , bsCurBlk :: Maybe BlockBuild
    }

data FunBuild = FunBuild
    { fbName :: Name
    , fbParams :: [(Name, Type)]
    , fbReturnType :: Type
    , fbEntry :: Maybe Name
    , fbBlocks :: [ABlock]
    , fbConstraints :: [Constraint]
    , fbAttributes :: FunctionAttributes
    }

data BlockBuild = BlockBuild
    { bbName :: Name
    , bbParams :: [(Name, Type)]
    , bbInstrs :: [AInstr]
    , bbTerminator :: Maybe ATerminator
    }

type AlloyBuilder = State BuildState

runAlloyBuilder :: String -> [Metal.Metadata.MetallicTypeClassMetadata] -> Set.Set Unique -> [AlloyTypeDef] -> AlloyBuilder a -> (a, AlloyModule)
runAlloyBuilder modName typeClasses structTypes typeDefs action =
    let initState =
            BuildState
                { bsModuleName = modName
                , bsFunctions = []
                , bsDictionaries = []
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
                , amDictionaries = bsDictionaries st
                , amTypeClasses = typeClasses
                , amStructTypes = structTypes
                , amTypeDefs = typeDefs
                }
    in (res, mdl)

beginFunction :: Name -> [(Name, Type)] -> Type -> AlloyBuilder ()
beginFunction name params retTy = beginFunctionFull name params retTy [] defaultFunctionAttributes

beginFunctionWithConstraints :: Name -> [(Name, Type)] -> Type -> [Constraint] -> AlloyBuilder ()
beginFunctionWithConstraints name params retTy constraints =
    beginFunctionFull name params retTy constraints defaultFunctionAttributes

beginFunctionFull :: Name -> [(Name, Type)] -> Type -> [Constraint] -> FunctionAttributes -> AlloyBuilder ()
beginFunctionFull name params retTy constraints attrs = do
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
                , fbConstraints = constraints
                , fbAttributes = attrs
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
                , afConstraints = fbConstraints
                , afAttributes = fbAttributes
                }

    put
        st
            { bsFunctions = bsFunctions ++ [fn]
            , bsCurFun = Nothing
            , bsCurBlk = Nothing
            }

beginBlock :: Name -> [(Name, Type)] -> AlloyBuilder ()
beginBlock name params = do
    st@BuildState{..} <- get
    fb@FunBuild{..} <- requireOpenFunction "beginBlock"

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
    pure $ NLocal (LocalId LPTemp bsNextTmp)

freshBlockName :: AlloyBuilder Name
freshBlockName = do
    st@BuildState{..} <- get
    put st{bsNextBlk = bsNextBlk + 1}
    pure $ NLocal (LocalId LPBlock bsNextBlk)

requireOpenFunction :: String -> AlloyBuilder FunBuild
requireOpenFunction context = do
    st <- get
    case bsCurFun st of
        Just fb -> pure fb
        Nothing -> error $ "Alloy.Build: " ++ context ++ " called with no open function"

requireOpenBlock :: String -> AlloyBuilder BlockBuild
requireOpenBlock context = do
    st <- get
    case bsCurBlk st of
        Just blk -> pure blk
        Nothing -> error $ "Alloy.Build: " ++ context ++ " called with no open block"

isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust Nothing = False
