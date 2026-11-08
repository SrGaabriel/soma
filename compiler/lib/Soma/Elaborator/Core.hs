{-# LANGUAGE MonadComprehensions #-}

module Soma.Elaborator.Core where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Control.Monad.Reader (ReaderT, asks)
import Control.Monad.State.Strict (MonadIO (liftIO), StateT, get, gets, modify', put)
import Data.IORef (IORef, modifyIORef', readIORef, writeIORef)
import Soma.Calculus
import Soma.Diagnostic (Diagnostic)
import Soma.Elaborator.Context (Local (Local, localName, localType, localUnique, localValue), LocalCtx (LocalCtx), MetaCtx (MetaCtx), resolveLocal, xsLocal)
import Soma.Env (Item (itemUnique), Namespace, resolveItem)
import Soma.Syntax.Tree (Def)
import Soma.Unique (Unique (Unique), UniqueMap)
import Soma.Unique qualified as U
import Symbolize (Symbol)

newtype Decl = Decl
    { declSyntax :: Def
    }

data ItemState
    = Pending !Decl
    | SigInProgress !Decl
    | SigDone !Term !Decl
    | BodyInProgress !Term
    | Done !Term !(Maybe Term)

data GlobalEnv = GlobalEnv
    { envUniques :: !(IORef Unique)
    , envNamespace :: !Namespace
    , envItems :: !(IORef (UniqueMap ItemState))
    , envDiags :: !(IORef [Diagnostic])
    , envUnfold :: Unique -> Elab (Maybe Term)
    }

data DeclState = DeclState
    { declMetas :: !MetaCtx
    , declLocals :: !LocalCtx
    , declDiags :: ![Diagnostic]
    }

type Elab = ReaderT GlobalEnv (StateT DeclState IO)

emptyDeclState :: DeclState
emptyDeclState =
    DeclState
        { declMetas = MetaCtx U.empty
        , declLocals = LocalCtx U.empty
        , declDiags = []
        }

mkUnique :: Elab Unique
mkUnique = do
    ref <- asks envUniques
    Unique i <- liftIO $ readIORef ref
    let new = Unique $ i + 1
    liftIO $ writeIORef ref new
    pure new

report :: Diagnostic -> Elab ()
report d = modify' $ \st -> st{declDiags = d : declDiags st}

isolated :: Elab a -> Elab a
isolated m = do
    outer <- get
    put emptyDeclState
    a <- m
    inner <- get
    put outer
    sink <- asks envDiags
    liftIO $ modifyIORef' sink (reverse (declDiags inner) ++)
    pure a

lookupItem :: Unique -> Elab ItemState
lookupItem u = do
    ref <- asks envItems
    items <- liftIO $ readIORef ref
    case U.lookup u items of
        Just st -> pure st
        Nothing -> error $ "lookupItem: unknown item " <> show u

setItem :: Unique -> ItemState -> Elab ()
setItem u st = do
    ref <- asks envItems
    liftIO $ modifyIORef' ref (U.insert u st)

allItemIds :: Elab [Unique]
allItemIds = do
    ref <- asks envItems
    U.keys <$> liftIO (readIORef ref)

unfoldConst :: Unique -> Elab (Maybe Term)
unfoldConst u = do
    f <- asks envUnfold
    f u

freshLocal :: Maybe Symbol -> Term -> Elab Unique
freshLocal name typ = do
    unique <- mkUnique
    let local =
            Local
                { localUnique = unique
                , localName = name
                , localType = typ
                , localValue = Nothing
                }
    modify' (\s@DeclState{declLocals} -> s{declLocals = xsLocal declLocals local})
    pure unique

scoped :: Elab a -> Elab a
scoped m = do
    saved <- gets declLocals
    m <* modify' (\s -> s{declLocals = saved})

lookupName :: [Symbol] -> Symbol -> Elab (Maybe Term)
lookupName path member =
    [ (guard (null path) *> (TFree . localUnique <$> resolveLocal locals member))
        <|> (TConst . itemUnique <$> resolveItem ns path member)
    | locals <- gets declLocals
    , ns <- asks envNamespace
    ]
