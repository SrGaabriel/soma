{-# LANGUAGE OverloadedStrings #-}

module Soma.Elaborator where

import Control.Monad.Reader (runReaderT)
import Control.Monad.State.Strict (evalStateT)
import Data.Foldable (for_)
import Data.HashMap.Strict qualified as HM
import Data.IORef (newIORef, readIORef)
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector.Strict qualified as V
import Soma.Calculus (Term (TError), prettyTerm)
import Soma.Diagnostic (Diagnostic)
import Soma.Elaborator.Core
import Soma.Elaborator.Decl (checkBody, elabSig, inferDecl)
import Soma.Elaborator.Diag (needsSignature)
import Soma.Env (Item (ItemId, itemFile, itemKind, itemName, itemParent, itemUnique), ItemKind (ItemDef), Namespace (Namespace, nsChildren, nsDecls))
import Soma.File (SourceFile (srcId))
import Soma.Print (Pretty (pretty))
import Soma.Syntax.Tree (Root, defName, defType, identText, rootDefs)
import Soma.Unique (UniqueMap)
import Soma.Unique qualified as U
import Symbolize (Symbol, intern, unintern)

typeOf :: U.Unique -> Elab Term
typeOf u =
    lookupItem u >>= \case
        Pending d -> do
            setItem u (SigInProgress d)
            case defType (declSyntax d) of
                Just _ -> do
                    ty <- isolated (elabSig d)
                    setItem u (SigDone ty d)
                    pure ty
                Nothing -> do
                    (ty, v) <- isolated (inferDecl d)
                    setItem u (Done ty (Just v))
                    pure ty
        SigInProgress d -> do
            report (needsSignature d)
            pure TError
        SigDone ty _ -> pure ty
        BodyInProgress ty -> pure ty
        Done ty _ -> pure ty

unfold :: U.Unique -> Elab (Maybe Term)
unfold u =
    lookupItem u >>= \case
        Pending _ -> typeOf u *> unfold u
        SigInProgress _ -> pure Nothing
        SigDone ty d -> do
            setItem u (BodyInProgress ty)
            v <- isolated (checkBody d ty)
            setItem u (Done ty (Just v))
            pure (Just v)
        BodyInProgress _ -> pure Nothing
        Done _ v -> pure v

elabPackage :: Elab ()
elabPackage = do
    us <- allItemIds
    for_ us $ \u -> typeOf u *> unfold u

data Elaborated = Elaborated
    { elabNames :: !(UniqueMap Symbol)
    , elabItems :: !(UniqueMap ItemState)
    }

instance Pretty Elaborated where
    pretty Elaborated{elabNames, elabItems} =
        T.intercalate "\n\n" (map item (U.toList elabItems))
      where
        term = prettyTerm elabNames
        item (u, st) = "def " <> nameOf u <> body st
        nameOf u@(U.Unique n) = maybe ("#" <> T.pack (show n)) unintern (U.lookup u elabNames)
        body :: ItemState -> Text
        body = \case
            Pending _ -> " <pending>"
            SigInProgress _ -> " <signature in progress>"
            SigDone ty _ -> " : " <> term ty <> " := <pending>"
            BodyInProgress ty -> " : " <> term ty <> " := <in progress>"
            Done ty Nothing -> " : " <> term ty
            Done ty (Just v) -> " : " <> term ty <> " := " <> term v

elaborateFile :: SourceFile -> Root -> IO (Elaborated, [Diagnostic])
elaborateFile src root = do
    let items = zip (map U.Unique [1 ..]) (V.toList (rootDefs root))
        namespace =
            Namespace
                { nsDecls = HM.fromList (mapMaybe declEntry items)
                , nsChildren = HM.empty
                }
        declEntry (u, d) = do
            sym <- intern . identText <$> defName d
            pure (sym, ItemId{itemUnique = u, itemFile = srcId src, itemName = sym, itemKind = ItemDef, itemParent = Nothing})
    uniquesRef <- newIORef (U.Unique (length items))
    itemsRef <- newIORef (U.fromList [(u, Pending (Decl d)) | (u, d) <- items])
    diagsRef <- newIORef []
    let env =
            GlobalEnv
                { envUniques = uniquesRef
                , envNamespace = namespace
                , envItems = itemsRef
                , envDiags = diagsRef
                , envUnfold = unfold
                }
    evalStateT (runReaderT elabPackage env) emptyDeclState
    finalItems <- readIORef itemsRef
    diags <- readIORef diagsRef
    let names = U.fromList [(itemUnique it, itemName it) | it <- HM.elems (nsDecls namespace)]
    pure (Elaborated{elabNames = names, elabItems = finalItems}, diags)
