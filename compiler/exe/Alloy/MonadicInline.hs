{-# LANGUAGE NamedFieldPuns #-}

-- todo: improve everything here

module Alloy.MonadicInline (
    monadicInlineModule,
    monadicInlineFunction,
    MonadicOps (..),
    defaultMonadicOps,
) where

import Alloy.Ir
import Alloy.Subst (Subst, substEffect, substOp, substOperand, substTerminator)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Project.Name as PN
import Typing.Types (TyConstructor (..), TyPrimitive (..), TyUnique (..), Type (..))

{- | Configuration for monadic inlining patterns
Uses string patterns matched against nameOriginal for stdlib functions
-}
data MonadicOps = MonadicOps
    { ioPurePatterns :: [String]
    , ioBindPatterns :: [String]
    , ioSeqPatterns :: [String]
    , readerPurePatterns :: [String]
    , readerBindPatterns :: [String]
    , readerAskPatterns :: [String]
    , statePurePatterns :: [String]
    , stateBindPatterns :: [String]
    , stateGetPatterns :: [String]
    , statePutPatterns :: [String]
    , maybePurePatterns :: [String]
    , maybeBindPatterns :: [String]
    , eitherPurePatterns :: [String]
    , eitherBindPatterns :: [String]
    , refNewPatterns :: [String]
    , refReadPatterns :: [String]
    , refModifyPatterns :: [String]
    , allowLazyList :: Bool
    , ioPureIsPhantom :: Bool
    , readerPureIsPhantom :: Bool
    , statePureIsPhantom :: Bool
    , maybePureIsPhantom :: Bool
    , eitherPureIsPhantom :: Bool
    }

defaultMonadicOps :: MonadicOps
defaultMonadicOps =
    MonadicOps
        { ioPurePatterns = ["IO.pure", "IO$pure", "pure", "pureIO"]
        , ioBindPatterns = ["IO.bind", "IO$bind"]
        , ioSeqPatterns = [">>"]
        , readerPurePatterns = ["Reader.pure", "Reader$pure"]
        , readerBindPatterns = ["Reader.bind", "Reader$bind"]
        , readerAskPatterns = ["Reader.ask", "Reader$ask"]
        , statePurePatterns = ["State.pure", "State$pure"]
        , stateBindPatterns = ["State.bind", "State$bind"]
        , stateGetPatterns = ["State.get", "State$get"]
        , statePutPatterns = ["State.put", "State$put"]
        , maybePurePatterns = ["Maybe.pure", "Optional.pure", "Maybe$pure", "Optional$pure", "Either.right", "Either$right"]
        , maybeBindPatterns = ["Maybe.bind", "Optional.bind", "Maybe$bind", "Optional$bind"]
        , eitherPurePatterns = ["Either.pure", "Either$pure", "Right", "Either.right", "Either$right"]
        , eitherBindPatterns = ["Either.bind", "Either$bind"]
        , refNewPatterns = ["newRef", "Ref.new"]
        , refReadPatterns = ["readRef", "Ref.read"]
        , refModifyPatterns = ["modifyRef", "Ref.modify"]
        , allowLazyList = False
        , ioPureIsPhantom = True
        , readerPureIsPhantom = True
        , statePureIsPhantom = False
        , maybePureIsPhantom = False
        , eitherPureIsPhantom = False
        }

monadicInlineModule :: AlloyModule -> AlloyModule
monadicInlineModule = monadicInlineModuleWith defaultMonadicOps

monadicInlineFunction :: AlloyFunction -> AlloyFunction
monadicInlineFunction = monadicInlineFunctionWith defaultMonadicOps

monadicInlineModuleWith :: MonadicOps -> AlloyModule -> AlloyModule
monadicInlineModuleWith ops m@AlloyModule{amFunctions} =
    m{amFunctions = map (monadicInlineFunctionWith ops) amFunctions}

monadicInlineFunctionWith :: MonadicOps -> AlloyFunction -> AlloyFunction
monadicInlineFunctionWith ops fn@AlloyFunction{afBlocks} =
    let blocks' = rewireBlocks ops fn afBlocks
    in fn{afBlocks = blocks'}

rewireBlocks :: MonadicOps -> AlloyFunction -> [ABlock] -> [ABlock]
rewireBlocks ops _fn = map (rewireBlock ops)

rewireBlock :: MonadicOps -> ABlock -> ABlock
rewireBlock ops blk@ABlock{abInstrs, abTerminator} =
    let (instrs', subst) = foldl (rewireInstr ops) ([], Map.empty) abInstrs
        term' = substTerminator subst abTerminator
    in blk{abInstrs = reverse instrs', abTerminator = term'}

-- Note: Subst type now imported from Alloy.Subst

rewireInstr :: MonadicOps -> ([AInstr], Subst) -> AInstr -> ([AInstr], Subst)
rewireInstr ops (acc, env) instr =
    case instr of
        ILet n ty (OpCall (Direct callee) args)
            | isIoPure ops callee || isIoPureByType ops callee ty
            , ioPureIsPhantom ops
            , [v] <- args ->
                let v' = substOperand env v
                in (acc, Map.insert n v' env)
            | isReaderPure ops callee
            , readerPureIsPhantom ops
            , [v] <- args ->
                let v' = substOperand env v
                in (acc, Map.insert n v' env)
            | isStatePure ops callee
            , statePureIsPhantom ops
            , [v] <- args ->
                let v' = substOperand env v
                in (acc, Map.insert n v' env)
            | isMaybePure ops callee
            , maybePureIsPhantom ops
            , [v] <- args ->
                let v' = substOperand env v
                in (acc, Map.insert n v' env)
            | isEitherPure ops callee
            , eitherPureIsPhantom ops
            , [v] <- args ->
                let v' = substOperand env v
                in (acc, Map.insert n v' env)
            | isReaderAsk ops callee
            , [envArg] <- args ->
                let envOp = substOperand env envArg
                in (acc, Map.insert n envOp env)
            -- Both IO actions have already executed, so we just substitute with the second operand (or unit if both are void)
            | isIoSeq ops callee
            , [_a, b] <- args ->
                let b' = substOperand env b
                in (acc, Map.insert n b' env)
            | isRefRead ops callee
            , [r] <- args ->
                let r' = substOperand env r
                    op' = OpLoad r'
                in (ILet n ty op' : acc, env)
            | isRefModify ops callee
            , [r, v] <- args ->
                let r' = substOperand env r
                    v' = substOperand env v
                    eff = EffStore r' v'
                in (IEffect eff : acc, Map.insert n r' env)
            | isRefNew ops callee
            , [v] <- args ->
                let v' = substOperand env v
                    elemTy = fromMaybe ty (refInner ty)
                    allocInstr = ILet n ty (OpAllocStack elemTy)
                    storeInstr = IEffect (EffStore (OpVar n) v')
                in (storeInstr : allocInstr : acc, env)
            | isMaybeBind ops callee
                || isEitherBind ops callee
                || isIoBind ops callee
                || isReaderBind ops callee
                || isStateBind ops callee ->
                let op' = OpCall (Direct callee) (map (substOperand env) args)
                in (ILet n ty op' : acc, env)
            | isStateGet ops callee
                || isStatePut ops callee ->
                let op' = OpCall (Direct callee) (map (substOperand env) args)
                in (ILet n ty op' : acc, env)
            | otherwise ->
                let op' = OpCall (Direct callee) (map (substOperand env) args)
                in (ILet n ty op' : acc, env)
        ILet n ty op ->
            let op' = substOp env op
            in (ILet n ty op' : acc, env)
        IEffect eff ->
            let eff' = substEffect env eff
            in (IEffect eff' : acc, env)

matchesStdlib :: [String] -> Name -> Bool
matchesStdlib = PN.nameMatchesStdlib

isIoPure, isIoBind, isIoSeq, isReaderPure, isReaderBind, isReaderAsk :: MonadicOps -> Name -> Bool
isRefNew, isRefRead, isRefModify, isStatePure, isStateBind :: MonadicOps -> Name -> Bool
isStateGet, isStatePut, isMaybePure, isMaybeBind :: MonadicOps -> Name -> Bool
isEitherPure, isEitherBind :: MonadicOps -> Name -> Bool
isIoPure MonadicOps{ioPurePatterns} = matchesStdlib ioPurePatterns
isIoBind MonadicOps{ioBindPatterns} = matchesStdlib ioBindPatterns
isIoSeq MonadicOps{ioSeqPatterns} = matchesStdlib ioSeqPatterns
isReaderPure MonadicOps{readerPurePatterns} = matchesStdlib readerPurePatterns
isReaderBind MonadicOps{readerBindPatterns} = matchesStdlib readerBindPatterns
isReaderAsk MonadicOps{readerAskPatterns} = matchesStdlib readerAskPatterns

isRefNew MonadicOps{refNewPatterns} = matchesStdlib refNewPatterns

isRefRead MonadicOps{refReadPatterns} = matchesStdlib refReadPatterns

isRefModify MonadicOps{refModifyPatterns} = matchesStdlib refModifyPatterns

isStatePure MonadicOps{statePurePatterns} = matchesStdlib statePurePatterns

isStateBind MonadicOps{stateBindPatterns} = matchesStdlib stateBindPatterns

isStateGet MonadicOps{stateGetPatterns} = matchesStdlib stateGetPatterns

isStatePut MonadicOps{statePutPatterns} = matchesStdlib statePutPatterns

isMaybePure MonadicOps{maybePurePatterns} = matchesStdlib maybePurePatterns

isMaybeBind MonadicOps{maybeBindPatterns} = matchesStdlib maybeBindPatterns

isEitherPure MonadicOps{eitherPurePatterns} = matchesStdlib eitherPurePatterns

isEitherBind MonadicOps{eitherBindPatterns} = matchesStdlib eitherBindPatterns

-- | Check if a call is IO.pure by checking pattern match AND return type
isIoPureByType :: MonadicOps -> Name -> Type -> Bool
isIoPureByType ops callee ty =
    matchesStdlib (ioPurePatterns ops) callee && returnsIo ty

returnsIo :: Type -> Bool
returnsIo t =
    case t of
        TApp (TConstructor (TypeConstructor (TyPrim TPIO) _)) _ -> True
        TApp l _ -> returnsIo l
        _ -> False

refInner :: Type -> Maybe Type
refInner t =
    case t of
        TApp (TConstructor (TypeConstructor (TyPrim TPRef) _)) a -> Just a
        _ -> Nothing
