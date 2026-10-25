{-# LANGUAGE DerivingVia #-}

module Soma.Syntax.Tree where

import Control.Applicative ((<|>))
import Data.Text (Text)
import Data.Vector.Strict qualified as V
import GHC.Generics (Generic, Generically (Generically))
import Maple.Ast
import Maple.Red (Red (RNode, RToken), RedNode, RedToken, materializeChildren, tokenKind, tokenText)
import Soma.Syntax.Kind

-- Tokens

newtype Ident = Ident RedToken
    deriving (AstToken) via (TokenOfKind 'KIdent)

newtype Number = Number RedToken
    deriving (AstToken) via (TokenOfKind 'KNumber)

identText :: Ident -> Text
identText = tokenText . syntaxToken

-- Nodes

newtype Root = Root RedNode
    deriving (AstNode) via (OfKind 'KRoot)

newtype Def = Def RedNode
    deriving (AstNode) via (OfKind 'KDef)

newtype Type = Type RedNode
    deriving (AstNode) via (OfKind 'KType)

newtype Block = Block RedNode
    deriving (AstNode) via (OfKind 'KBlock)

newtype ExBinder = ExBinder RedNode
    deriving (AstNode) via (OfKind 'KExBinder)

newtype ImBinder = ImBinder RedNode
    deriving (AstNode) via (OfKind 'KImBinder)

newtype Implicits = Implicits RedNode
    deriving (AstNode) via (OfKind 'KImplicits)

data Binder
    = BIm ImBinder
    | BEx ExBinder
    deriving (Generic)
    deriving (AstNode) via (Generically Binder)

data Expr
    = EVar Ident
    | ELit Number
    | EBlock Block

castExpr :: Red -> Maybe Expr
castExpr (RNode n) = EBlock <$> cast n
castExpr (RToken t) = (EVar <$> castToken t) <|> (ELit <$> castToken t)

rootDefs :: Root -> V.Vector Def
rootDefs = children . syntax

defName :: Def -> Maybe Ident
defName = firstJust castTokenRed . fst . splitAtToken KColonEq . syntax

defImplicits :: Def -> V.Vector ImBinder
defImplicits = maybe V.empty (children . syntax) . (child @Implicits) . syntax

defExplicits :: Def -> V.Vector ExBinder
defExplicits = children . syntax

defBinders :: Def -> V.Vector Binder
defBinders d = fmap BIm (defImplicits d) <> fmap BEx (defExplicits d)

defType :: Def -> Maybe Type
defType = child . syntax

defBody :: Def -> Maybe Expr
defBody = firstJust castExpr . snd . splitAtToken KColonEq . syntax

binderName :: Binder -> Maybe Ident
binderName = childToken . syntax

data Annotation
    = Omitted
    | Annotated (Maybe Type)

binderAnnotation :: Binder -> Annotation
binderAnnotation b = case tokenOf KColon n of
    Just _ -> Annotated (child n)
    Nothing -> Omitted
  where
    n = syntax b

typeName :: Type -> Maybe Ident
typeName = childToken . syntax

splitAtToken :: Kind -> RedNode -> (V.Vector Red, V.Vector Red)
splitAtToken k n =
    case V.findIndex isK cs of
        Just i -> (V.take i cs, V.drop (i + 1) cs)
        Nothing -> (cs, V.empty)
  where
    cs = materializeChildren n
    raw = toRaw k
    isK (RToken t) = tokenKind t == raw
    isK _ = False
