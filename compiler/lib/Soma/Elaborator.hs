module Soma.Elaborator where

import Data.Foldable (for_)
import Soma.Calculus (Term (TError))
import Soma.Elaborator.Core
import Soma.Elaborator.Decl (elabSig, inferDecl, checkBody)
import Soma.Elaborator.Diag (needsSignature)
import Soma.Syntax.Tree (defType)
import Soma.Unique (Unique)

typeOf :: Unique -> Elab Term
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

unfold :: Unique -> Elab (Maybe Term)
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
