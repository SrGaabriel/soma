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
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Typing.Types (TyConstructor (..), Type (..))

data MonadicOps = MonadicOps
    { ioPure :: [Name]
    , ioBind :: [Name]
    , readerPure :: [Name]
    , readerBind :: [Name]
    , readerAsk :: [Name]
    , statePure :: [Name]
    , stateBind :: [Name]
    , stateGet :: [Name]
    , statePut :: [Name]
    , maybePure :: [Name]
    , maybeBind :: [Name]
    , eitherPure :: [Name]
    , eitherBind :: [Name]
    , refNew :: [Name]
    , refRead :: [Name]
    , refModify :: [Name]
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
        { ioPure = ["IO.pure", "IO$pure"]
        , ioBind = ["IO.bind", "IO$bind"]
        , readerPure = ["Reader.pure", "Reader$pure"]
        , readerBind = ["Reader.bind", "Reader$bind"]
        , readerAsk = ["Reader.ask", "Reader$ask"]
        , statePure = ["State.pure", "State$pure"]
        , stateBind = ["State.bind", "State$bind"]
        , stateGet = ["State.get", "State$get"]
        , statePut = ["State.put", "State$put"]
        , maybePure = ["Maybe.pure", "Optional.pure", "Maybe$pure", "Optional$pure", "Either.right", "Either$right"]
        , maybeBind = ["Maybe.bind", "Optional.bind", "Maybe$bind", "Optional$bind"]
        , eitherPure = ["Either.pure", "Either$pure", "Right", "Either.right", "Either$right"]
        , eitherBind = ["Either.bind", "Either$bind"]
        , refNew = ["newRef", "Ref.new"]
        , refRead = ["readRef", "Ref.read"]
        , refModify = ["modifyRef", "Ref.modify"]
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
            | isIoPure ops callee || isIoPureByType callee ty
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

matches :: [Name] -> Name -> Bool
matches candidates n = any (`isPrefixOf` n) candidates

isIoPure, isIoBind, isReaderPure, isReaderBind, isReaderAsk :: MonadicOps -> Name -> Bool
isRefNew, isRefRead, isRefModify, isStatePure, isStateBind :: MonadicOps -> Name -> Bool
isStateGet, isStatePut, isMaybePure, isMaybeBind :: MonadicOps -> Name -> Bool
isEitherPure, isEitherBind :: MonadicOps -> Name -> Bool
isIoPure MonadicOps{ioPure} = matches ioPure
isIoBind MonadicOps{ioBind} = matches ioBind
isReaderPure MonadicOps{readerPure} = matches readerPure
isReaderBind MonadicOps{readerBind} = matches readerBind
isReaderAsk MonadicOps{readerAsk} = matches readerAsk

isRefNew MonadicOps{refNew} = matches refNew

isRefRead MonadicOps{refRead} = matches refRead

isRefModify MonadicOps{refModify} = matches refModify

isStatePure MonadicOps{statePure} = matches statePure

isStateBind MonadicOps{stateBind} = matches stateBind

isStateGet MonadicOps{stateGet} = matches stateGet

isStatePut MonadicOps{statePut} = matches statePut

isMaybePure MonadicOps{maybePure} = matches maybePure

isMaybeBind MonadicOps{maybeBind} = matches maybeBind

isEitherPure MonadicOps{eitherPure} = matches eitherPure

isEitherBind MonadicOps{eitherBind} = matches eitherBind

isIoPureByType :: Name -> Type -> Bool
isIoPureByType callee ty =
    (callee == "pure" || callee == "pureIO") && returnsIo ty

returnsIo :: Type -> Bool
returnsIo t =
    case t of
        TApp (TConstructor (TypeConstructor "IO" _)) _ -> True
        TApp l _ -> returnsIo l
        _ -> False

refInner :: Type -> Maybe Type
refInner t =
    case t of
        TApp (TConstructor (TypeConstructor "Ref" _)) a -> Just a
        _ -> Nothing
