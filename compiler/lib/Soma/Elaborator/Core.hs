module Soma.Elaborator.Core where

import Control.Monad.Reader (ReaderT, asks)
import Control.Monad.State.Strict (MonadIO (liftIO), StateT, get, modify', put)
import Data.IORef (IORef, modifyIORef', readIORef, writeIORef)
import Soma.Calculus (Term)
import Soma.Diagnostic (Diagnostic)
import Soma.Elaborator.Context (MetaCtx (MetaCtx))
import Soma.Env (Namespace)
import Soma.File (SourceFile)
import Soma.Syntax.Tree (Def)
import Soma.Unique (Unique (Unique), UniqueMap)
import Soma.Unique qualified as U

data Decl = Decl
    { declFile :: !SourceFile
    , declSyntax :: !Def
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
    , declDiags :: ![Diagnostic]
    }

type Elab = ReaderT GlobalEnv (StateT DeclState IO)

emptyDeclState :: DeclState
emptyDeclState = DeclState{declMetas = MetaCtx U.empty, declDiags = []}

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
