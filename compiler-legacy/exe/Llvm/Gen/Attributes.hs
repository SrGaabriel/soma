{-# LANGUAGE RecordWildCards #-}

module Llvm.Gen.Attributes (
    FunctionAttrs (..),
    analyzeFunctionAttrs,
    defaultAttrs,
    noAttrs,
) where

import Alloy.Ir

data FunctionAttrs = FunctionAttrs
    { attrNoUnwind :: !Bool
    , attrNoSync :: !Bool
    , attrNoFree :: !Bool
    , attrMemoryNone :: !Bool
    , attrWillReturn :: !Bool
    , attrNoRecurse :: !Bool
    }
    deriving (Show, Eq)

defaultAttrs :: FunctionAttrs
defaultAttrs =
    FunctionAttrs
        { attrNoUnwind = True
        , attrNoSync = True
        , attrNoFree = True
        , attrMemoryNone = True
        , attrWillReturn = True
        , attrNoRecurse = True
        }

noAttrs :: FunctionAttrs
noAttrs =
    FunctionAttrs
        { attrNoUnwind = False
        , attrNoSync = False
        , attrNoFree = False
        , attrMemoryNone = False
        , attrWillReturn = False
        , attrNoRecurse = False
        }

data AnalysisState = AnalysisState
    { asHasPanic :: !Bool
    , asHasSync :: !Bool
    , asHasFree :: !Bool
    , asHasMemoryAccess :: !Bool
    , asCallsSelf :: !Bool
    , asFunctionName :: !Name
    }

emptyState :: Name -> AnalysisState
emptyState name =
    AnalysisState
        { asHasPanic = False
        , asHasSync = False
        , asHasFree = False
        , asHasMemoryAccess = False
        , asCallsSelf = False
        , asFunctionName = name
        }

analyzeFunctionAttrs :: AlloyFunction -> FunctionAttrs
analyzeFunctionAttrs AlloyFunction{..} =
    let initState = emptyState afName
        finalState = foldr analyzeBlock initState afBlocks
    in stateToAttrs finalState

stateToAttrs :: AnalysisState -> FunctionAttrs
stateToAttrs AnalysisState{..} =
    FunctionAttrs
        { attrNoUnwind = True
        , attrNoSync = not asHasSync
        , attrNoFree = not asHasFree
        , attrMemoryNone = not asHasMemoryAccess
        , attrWillReturn = not asHasPanic && not asCallsSelf
        , attrNoRecurse = not asCallsSelf
        }

analyzeBlock :: ABlock -> AnalysisState -> AnalysisState
analyzeBlock ABlock{..} st =
    let st' = foldr analyzeInstr st abInstrs
        st'' = analyzeTerminator abTerminator st'
    in st''

analyzeInstr :: AInstr -> AnalysisState -> AnalysisState
analyzeInstr instr st = case instr of
    ILet _ _ op -> analyzeOp op st
    IEffect eff -> analyzeEffect eff st

-- todo: refine this analysis further and make it a proper pass
analyzeOp :: AOp -> AnalysisState -> AnalysisState
analyzeOp op st = case op of
    OpLoad _ -> st{asHasMemoryAccess = True}
    OpAllocStack _ -> st{asHasMemoryAccess = True}
    OpAllocHeap _ -> st{asHasMemoryAccess = True}
    OpIndex _ _ -> st{asHasMemoryAccess = True}
    OpProject _ _ -> st{asHasMemoryAccess = True}
    OpConstruct{} -> st{asHasMemoryAccess = True}
    OpMakeArray _ -> st{asHasMemoryAccess = True}
    OpMakeTuple _ -> st{asHasMemoryAccess = True}
    OpAllocClosure{} -> st{asHasMemoryAccess = True}
    OpClosureGetEnv{} -> st{asHasMemoryAccess = True}
    OpClosureSetEnv{} -> st{asHasMemoryAccess = True}
    OpClosureGetFunc _ -> st{asHasMemoryAccess = True}
    OpWrapClosure _ -> st{asHasMemoryAccess = True}
    OpDup{} -> st{asHasMemoryAccess = True}
    OpDupProj0 _ -> st{asHasMemoryAccess = True}
    OpDupProj1 _ -> st{asHasMemoryAccess = True}
    OpDupClosure{} -> st{asHasMemoryAccess = True}
    OpDupClosureProj0{} -> st{asHasMemoryAccess = True}
    OpDupClosureProj1{} -> st{asHasMemoryAccess = True}
    OpClosureGetEnvDirect{} -> st{asHasMemoryAccess = True}
    OpClosureGetEnvSUP{} -> st{asHasMemoryAccess = True}
    OpParProj0{} -> st{asHasSync = True, asHasMemoryAccess = True}
    OpParProj1{} -> st{asHasSync = True, asHasMemoryAccess = True}
    OpParClosureProj0{} -> st{asHasSync = True, asHasMemoryAccess = True}
    OpParClosureProj1{} -> st{asHasSync = True, asHasMemoryAccess = True}
    OpFork{} -> st{asHasSync = True, asHasMemoryAccess = True}
    OpJoin _ -> st{asHasSync = True, asHasMemoryAccess = True}
    OpGraphInit _ -> st{asHasMemoryAccess = True, asHasSync = True}
    OpGraphShutdown -> st{asHasMemoryAccess = True, asHasSync = True}
    OpGraphNum _ -> st{asHasMemoryAccess = True}
    OpGraphAdd{} -> st{asHasMemoryAccess = True}
    OpGraphSub{} -> st{asHasMemoryAccess = True}
    OpGraphMul{} -> st{asHasMemoryAccess = True}
    OpGraphDiv{} -> st{asHasMemoryAccess = True}
    OpGraphMod{} -> st{asHasMemoryAccess = True}
    OpGraphCall{} -> st{asHasMemoryAccess = True}
    OpGraphReduce _ -> st{asHasMemoryAccess = True, asHasSync = True}
    OpGraphExtractNum _ -> st
    OpGraphRegisterFunc{} -> st{asHasMemoryAccess = True}
    OpGraphDup{} -> st{asHasMemoryAccess = True}
    OpGraphDupGetProj0 _ -> st{asHasMemoryAccess = True}
    OpGraphDupGetProj1 _ -> st{asHasMemoryAccess = True}
    OpGraphSup{} -> st{asHasMemoryAccess = True}
    OpGraphLam{} -> st{asHasMemoryAccess = True}
    OpGraphApp{} -> st{asHasMemoryAccess = True}
    OpGraphEra -> st
    OpGraphRef{} -> st{asHasMemoryAccess = True}
    OpGraphClosure{} -> st{asHasMemoryAccess = True}
    OpGraphClosureApp{} -> st{asHasMemoryAccess = True}
    OpGraphClosureGetEnv{} -> st{asHasMemoryAccess = True}
    OpGraphCon{} -> st{asHasMemoryAccess = True}
    OpGraphConGet{} -> st{asHasMemoryAccess = True}
    OpPanic _ -> st{asHasPanic = True}
    OpCall callable _ ->
        let st' = st{asHasMemoryAccess = True}
        in case callable of
            Direct name
                | name == asFunctionName st -> st'{asCallsSelf = True}
                | otherwise -> st'
            Indirect _ -> st'
    OpDictCall{} -> st{asHasMemoryAccess = True}
    OpBin{} -> st
    OpUnary{} -> st
    OpCmp{} -> st
    OpSelect{} -> st
    OpTagOf _ -> st
    OpArrayLength _ -> st{asHasMemoryAccess = True}
    OpCons{} -> st{asHasMemoryAccess = True}
    OpArrayTail{} -> st{asHasMemoryAccess = True}
    OpGetDict{} -> st

analyzeEffect :: AEffect -> AnalysisState -> AnalysisState
analyzeEffect eff st = case eff of
    EffStore{} -> st{asHasMemoryAccess = True}
    EffStoreIndex{} -> st{asHasMemoryAccess = True}
    EffDrop _ -> st{asHasFree = True, asHasMemoryAccess = True}
    EffClosureSetEnv{} -> st{asHasMemoryAccess = True}
    EffGraphInit _ -> st{asHasMemoryAccess = True, asHasSync = True}
    EffGraphShutdown -> st{asHasMemoryAccess = True, asHasSync = True}
    EffGraphRegisterFunc{} -> st{asHasMemoryAccess = True}

analyzeTerminator :: ATerminator -> AnalysisState -> AnalysisState
analyzeTerminator _ st = st
