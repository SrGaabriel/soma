{-# LANGUAGE DerivingVia #-}

module Soma.Syntax.Tree where

import Control.Applicative ((<|>))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector.Strict qualified as V
import GHC.Generics (Generic, Generically (Generically))
import Maple.Ast
import Maple.Position (Range (Range), Span (Span))
import Maple.Red (Red (RNode, RToken), RedNode, RedToken, materializeChildren, tokenKind, tokenText)
import Soma.Syntax.Kind
import Symbolize (Symbol, intern)

-- Tokens

newtype Ident = Ident RedToken
    deriving (AstToken) via (TokenOfKind 'KIdent)

newtype Number = Number RedToken
    deriving (AstToken) via (TokenOfKind 'KNumber)

newtype StrLit = StrLit RedToken
    deriving (AstToken) via (TokenOfKind 'KString)

identText :: Ident -> Text
identText = tokenText . syntaxToken

identSymbol :: Ident -> Symbol
identSymbol = intern . identText

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

data Name = Name [Ident] Ident

newtype NameNode = NameNode RedNode
    deriving (AstNode) via (OfKind 'KName)

castName :: RedNode -> Maybe Name
castName n = do
    NameNode node <- cast n
    let tokens = materializeChildren node
    member <- if V.null tokens then Nothing else castTokenRed (V.last tokens)
    pure $ Name (V.toList (V.init (childTokens node))) member

nameSpan :: Name -> Span
nameSpan (Name path member) = Span file (Range start end)
  where
    Span file (Range _ end) = syntaxTokenSpan member
    Span _ (Range start _) = syntaxTokenSpan (case path of first : _ -> first; [] -> member)

data Expr
    = EVar Name
    | ENumLit Number
    | EStrLit StrLit
    | EBlock Block

castExpr :: Red -> Maybe Expr
castExpr (RNode n) = (EVar <$> castName n) <|> (EBlock <$> cast n)
castExpr (RToken t) = (ENumLit <$> castToken t) <|> (EStrLit <$> castToken t)

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

strLitText :: StrLit -> Text
strLitText = tokenText . syntaxToken

numberText :: Number -> Text
numberText = tokenText . syntaxToken

strLitValue :: StrLit -> Text
strLitValue = T.pack . unescape . T.unpack . stripQuotes . strLitText
  where
    stripQuotes t = maybe t fst (T.unsnoc =<< fmap snd (T.uncons t))
    unescape ('\\' : c : cs) = escape c : unescape cs
    unescape (c : cs) = c : unescape cs
    unescape [] = []
    escape 'n' = '\n'
    escape 't' = '\t'
    escape 'r' = '\r'
    escape '0' = '\0'
    escape c = c

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
