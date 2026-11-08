{-# LANGUAGE DerivingVia #-}

module Soma.Syntax.Tree where

import Control.Applicative ((<|>))
import Data.Maybe (mapMaybe)
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

newtype Block = Block RedNode
    deriving (AstNode) via (OfKind 'KBlock)

newtype Implicits = Implicits RedNode
    deriving (AstNode) via (OfKind 'KImplicits)

newtype Explicits = Explicits RedNode
    deriving (AstNode) via (OfKind 'KExplicits)

data Binder
    = BIm Implicits
    | BEx Explicits
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

newtype Pi = Pi RedNode
    deriving (AstNode) via (OfKind 'KPi)

newtype App = App RedNode
    deriving (AstNode) via (OfKind 'KApp)

newtype Paren = Paren RedNode
    deriving (AstNode) via (OfKind 'KParen)

data Expr
    = EVar Name
    | ENumLit Number
    | EStrLit StrLit
    | EBlock Block
    | EApp App
    | EPi Pi

castExpr :: Red -> Maybe Expr
castExpr (RNode n) =
    (EVar <$> castName n)
        <|> (EBlock <$> cast n)
        <|> (EApp <$> cast n)
        <|> (EPi <$> cast n)
        <|> (parenContents n >>= firstJust castExpr)
castExpr (RToken t) = (ENumLit <$> castToken t) <|> (EStrLit <$> castToken t)

parenContents :: RedNode -> Maybe (V.Vector Red)
parenContents n = materializeChildren . syntax <$> cast @Paren n

data PiParam
    = PiBinder Binder
    | PiAnon Expr

piParam :: Pi -> Maybe PiParam
piParam p = (PiBinder <$> firstJust castRed params) <|> (PiAnon <$> firstJust castExpr params)
  where
    params = fst (splitAtToken KArrow (syntax p))

piCodomain :: Pi -> Maybe Expr
piCodomain = firstJust castExpr . snd . splitAtToken KArrow . syntax

appTerms :: App -> [Red]
appTerms = filter (not . isTriviaRed) . V.toList . materializeChildren . syntax

appFn :: App -> Maybe Expr
appFn a = case appTerms a of
    t : _ -> castExpr t
    [] -> Nothing

appArgs :: App -> [Expr]
appArgs = mapMaybe castExpr . drop 1 . appTerms

isTriviaRed :: Red -> Bool
isTriviaRed (RToken t) = isTrivia (fromRaw (tokenKind t))
isTriviaRed (RNode _) = False

rootDefs :: Root -> V.Vector Def
rootDefs = children . syntax

defName :: Def -> Maybe Ident
defName = firstJust castTokenRed . fst . splitAtToken KColonEq . syntax

defBinders :: Def -> V.Vector Binder
defBinders = children . syntax

defType :: Def -> Maybe Expr
defType = firstJust castExpr . fst . splitAtToken KColonEq . syntax

defBody :: Def -> Maybe Expr
defBody = firstJust castExpr . snd . splitAtToken KColonEq . syntax

binderNames :: Binder -> [Ident]
binderNames = mapMaybe castTokenRed . V.toList . fst . splitAtToken KColon . syntax

data Annotation
    = Omitted
    | Annotated (Maybe Expr)

binderAnnotation :: Binder -> Annotation
binderAnnotation b = case tokenOf KColon n of
    Just _ -> Annotated (firstJust castExpr (snd (splitAtToken KColon n)))
    Nothing -> Omitted
  where
    n = syntax b

strLitText :: StrLit -> Text
strLitText = tokenText . syntaxToken

numberText :: Number -> Text
numberText = tokenText . syntaxToken

strLitValue :: StrLit -> Text
strLitValue = T.pack . unescape . T.unpack . stripQuotes . strLitText
  where
    stripQuotes t = maybe t fst (T.unsnoc . snd =<< T.uncons t)
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
