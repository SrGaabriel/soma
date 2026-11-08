{-# LANGUAGE OverloadedStrings #-}

module Soma.Calculus where

import Data.Maybe (fromMaybe)
import Data.Text qualified as T
import Soma.Print (Pretty (pretty))
import Soma.Unique (Unique (Unique), UniqueMap)
import Soma.Unique qualified as U
import Symbolize (Symbol, unintern)

data Level
    = LZero
    | LSucc !Level
    | LMax !Level !Level
    | LIMax !Level !Level
    deriving (Eq, Show)

type0 :: Term
type0 = TSort (LSucc LZero)

data Term
    = TMeta !Unique
    | TFree !Unique
    | TBound !Int
    | TSort !Level
    | TConst !Unique
    | TPi BinderInfo Term Term
    | TSigma Term Term
    | TApp Term Term
    | TLam Term Term
    | TLet Term Term Term
    | TLit Literal
    | TError
    deriving (Show, Eq)

data Literal
    = LStr T.Text
    | LNum T.Text
    deriving (Show, Eq)

instance Pretty Term where
    pretty = prettyTerm U.empty

instance Pretty Level where
    pretty = prettyLevel

data BinderInfo
    = BinderExplicit
    | BinderImplicit
    deriving (Show, Eq)

prettyTerm :: UniqueMap Symbol -> Term -> T.Text
prettyTerm names = go [] PBinder
  where
    go :: [T.Text] -> Prec -> Term -> T.Text
    go ctx p = \case
        TMeta u -> "?" <> showUnique u
        TFree u -> "%" <> showUnique u
        TBound i -> fromMaybe ("#" <> T.show i) (index ctx i)
        TSort l -> parensIf (p > PApp) ("Sort " <> prettyLevelAtom l)
        TConst u -> maybe ("#" <> showUnique u) unintern (U.lookup u names)
        TLit (LNum n) -> n
        TLit (LStr s) -> T.show s
        TError -> "<error>"
        TApp f a -> parensIf (p > PApp) (go ctx PApp f <> " " <> go ctx PAtom a)
        TPi _ a b -- todo: binder info
            | not (occurs 0 b) -> parensIf (p > PBinder) (go ctx PApp a <> " → " <> go ("_" : ctx) PBinder b)
            | otherwise -> binder ctx p "" " → " a b
        TSigma a b -> binder ctx p "" " × " a b
        TLam a b -> binder ctx p "fun " " => " a b
        TLet ty v b ->
            let x = fresh ctx
            in parensIf (p > PBinder)
                $ "let " <> x <> " : " <> go ctx PBinder ty <> " := " <> go ctx PBinder v <> "; " <> go (x : ctx) PBinder b

    binder ctx p kw sep a b =
        let x = fresh ctx
        in parensIf (p > PBinder)
            $ kw <> "(" <> x <> " : " <> go ctx PBinder a <> ")" <> sep <> go (x : ctx) PBinder b

    fresh ctx = "x" <> T.show (length ctx)

data Prec = PBinder | PApp | PAtom
    deriving (Eq, Ord)

occurs :: Int -> Term -> Bool
occurs k = \case
    TBound i -> i == k
    TApp f a -> occurs k f || occurs k a
    TPi _ a b -> occurs k a || occurs (k + 1) b
    TSigma a b -> occurs k a || occurs (k + 1) b
    TLam a b -> occurs k a || occurs (k + 1) b
    TLet ty v b -> occurs k ty || occurs k v || occurs (k + 1) b
    _ -> False

prettyLevel :: Level -> T.Text
prettyLevel l = case succs l of
    (n, LZero) -> T.show n
    (0, base) -> compound base
    (n, base) -> prettyLevelAtom base <> " + " <> T.show n
  where
    compound = \case
        LMax a b -> "max " <> prettyLevelAtom a <> " " <> prettyLevelAtom b
        LIMax a b -> "imax " <> prettyLevelAtom a <> " " <> prettyLevelAtom b
        other -> prettyLevel other

prettyLevelAtom :: Level -> T.Text
prettyLevelAtom l = case succs l of
    (_, LZero) -> prettyLevel l
    _ -> "(" <> prettyLevel l <> ")"

succs :: Level -> (Int, Level)
succs (LSucc l) = let (n, b) = succs l in (n + 1, b)
succs l = (0, l)

index :: [a] -> Int -> Maybe a
index xs i
    | i < 0 = Nothing
    | otherwise = case drop i xs of
        x : _ -> Just x
        [] -> Nothing

parensIf :: Bool -> T.Text -> T.Text
parensIf True t = "(" <> t <> ")"
parensIf False t = t

showUnique :: Unique -> T.Text
showUnique (Unique n) = T.show n
