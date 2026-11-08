module Soma.Elaborator.Expr where

import Data.Traversable (for)
import Soma.Calculus
import Soma.Elaborator.Core (Elab, freshLocal, lookupName, report, scoped)
import Soma.Elaborator.Diag (unknownName)
import Soma.Elaborator.Subst (abstract)
import Soma.Syntax.Tree (Annotation (..), Binder (BEx, BIm), Expr (..), Name (Name), PiParam (..), appArgs, appFn, binderAnnotation, binderNames, identSymbol, identText, numberText, piCodomain, piParam, strLitValue)
import Soma.Unique (Unique)
import Symbolize (intern)

checkType :: Expr -> Elab Term
checkType = elabExpr -- todo checkExpr with Sort

checkExpr :: Expr -> Term -> Elab Term
checkExpr e _ = elabExpr e -- todo

inferExpr :: Expr -> Elab (Term, Term)
inferExpr = error "todo"

elabMaybeExpr :: Maybe Expr -> Elab Term
elabMaybeExpr (Just t) = elabExpr t
elabMaybeExpr Nothing = pure TError

elabMaybeType :: Maybe Expr -> Elab Term
elabMaybeType (Just t) = checkType t
elabMaybeType Nothing = pure TError

resolveName :: Name -> Elab Term
resolveName name@(Name path member) = do
    let sPath = map (intern . identText) path
    let sMember = (intern . identText) member
    mTerm <- lookupName sPath sMember
    case mTerm of
        Just term -> pure term
        Nothing -> TError <$ report (unknownName name)

elabExpr :: Expr -> Elab Term
elabExpr (EStrLit lit) = pure $ TLit $ LStr $ strLitValue lit
elabExpr (ENumLit lit) = pure $ TLit $ LNum $ numberText lit
elabExpr (EVar var) = resolveName var
elabExpr (EApp app) = do
    tf <- elabMaybeExpr (appFn app)
    args <- traverse elabExpr (appArgs app)
    pure $ foldl' TApp tf args
elabExpr (EBlock _) = pure TError -- todo
elabExpr (EPi p) = case piParam p of
    Just (PiBinder b) -> elabPis [b] codomain
    Just (PiAnon dom) -> TPi BinderExplicit <$> checkType dom <*> codomain
    Nothing -> TPi BinderExplicit TError <$> codomain
  where
    codomain = elabMaybeType (piCodomain p)

elabPis :: [Binder] -> Elab Term -> Elab Term
elabPis binders body = scoped $ do
    fbs <- concat <$> traverse elabBinder binders
    res <- body
    pure $ foldr (\FreeBinder{fvar, info, ty} acc -> TPi info ty (abstract acc fvar)) res fbs

data FreeBinder = FreeBinder
    { fvar :: Unique
    , info :: BinderInfo
    , ty :: Term
    }

elabBinder :: Binder -> Elab [FreeBinder]
elabBinder b = do
    ty <- case binderAnnotation b of
        Annotated ann -> elabMaybeType ann
        Omitted -> pure type0 -- todo: fresh meta
    for (binderNames b) $ \name -> do
        fvar <- freshLocal (Just (identSymbol name)) ty
        pure FreeBinder{fvar, info, ty}
  where
    info = case b of
        BIm _ -> BinderImplicit
        BEx _ -> BinderExplicit
