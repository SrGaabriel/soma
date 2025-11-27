module Syntax.CST.GreenTree (
    GreenNode (..),
    GreenToken (..),
    GreenElement (..),
    NodeData (..),
    token,
    node,
    errorNode,
    errorToken,
    greenKind,
    greenTextLen,
    greenChildren,
    greenChildrenWithOffsets,
    greenText,
    greenTokenText,
    greenDescendants,
    greenTokens,
    GreenInterner,
    newInterner,
    internNode,
    internToken,
    TextRange (..),
    rangeLen,
    rangeContains,
    rangeIntersects,
) where

import qualified Data.HashMap.Strict as HM
import Data.Hashable (Hashable (..))
import Data.IORef
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word (Word32)
import Syntax.CST.SyntaxKind

data TextRange = TextRange
    { rangeStart :: {-# UNPACK #-} !Word32
    , rangeLength :: {-# UNPACK #-} !Word32
    }
    deriving (Eq, Ord, Show)

instance Hashable TextRange where
    hashWithSalt s (TextRange start len) = s `hashWithSalt` start `hashWithSalt` len

rangeLen :: TextRange -> Word32
rangeLen = rangeLength

rangeContains :: TextRange -> Word32 -> Bool
rangeContains (TextRange s l) offset = offset >= s && offset < s + l

rangeIntersects :: TextRange -> TextRange -> Bool
rangeIntersects (TextRange s1 l1) (TextRange s2 l2) =
    s1 < s2 + l2 && s2 < s1 + l1

data GreenToken = GreenToken
    { gtKind :: !SyntaxKind
    , gtText :: !Text
    }
    deriving (Eq, Show)

instance Hashable GreenToken where
    hashWithSalt s (GreenToken k t) = hashWithSalt s (k, t)

data NodeData = NodeData
    { ndKind :: !SyntaxKind
    , ndChildren :: ![GreenElement]
    , ndTextLen :: {-# UNPACK #-} !Word32 -- Cached total text length
    }
    deriving (Eq, Show)

instance Hashable NodeData where
    hashWithSalt s (NodeData k cs _) = hashWithSalt s (k, cs)

data GreenElement
    = GreenTokenElement !GreenToken
    | GreenNodeElement !GreenNode
    deriving (Eq, Show)

instance Hashable GreenElement where
    hashWithSalt s (GreenTokenElement t) = hashWithSalt s (0 :: Int, t)
    hashWithSalt s (GreenNodeElement n) = hashWithSalt s (1 :: Int, n)

newtype GreenNode = GreenNode {unGreenNode :: NodeData}
    deriving (Eq, Show)

instance Hashable GreenNode where
    hashWithSalt s (GreenNode nd) = hashWithSalt s nd

token :: SyntaxKind -> Text -> GreenElement
token kind txt = GreenTokenElement (GreenToken kind txt)

node :: SyntaxKind -> [GreenElement] -> GreenNode
node kind children' =
    GreenNode
        NodeData
            { ndKind = kind
            , ndChildren = children'
            , ndTextLen = sum (map elementTextLen children')
            }

errorNode :: [GreenElement] -> GreenNode
errorNode = node (SK_Node NK_ERROR)

errorToken :: Text -> GreenElement
errorToken = token SK_Error

greenKind :: GreenElement -> SyntaxKind
greenKind (GreenTokenElement t) = gtKind t
greenKind (GreenNodeElement n) = ndKind (unGreenNode n)

greenTextLen :: GreenElement -> Word32
greenTextLen = elementTextLen

elementTextLen :: GreenElement -> Word32
elementTextLen (GreenTokenElement t) = fromIntegral $ T.length (gtText t)
elementTextLen (GreenNodeElement n) = ndTextLen (unGreenNode n)

greenChildren :: GreenNode -> [GreenElement]
greenChildren = ndChildren . unGreenNode

greenChildrenWithOffsets :: GreenNode -> [(Word32, GreenElement)]
greenChildrenWithOffsets n = go 0 (greenChildren n)
  where
    go _ [] = []
    go offset (c : cs) = (offset, c) : go (offset + elementTextLen c) cs

greenText :: GreenElement -> Text
greenText (GreenTokenElement t) = gtText t
greenText (GreenNodeElement n) = T.concat $ map greenText (greenChildren n)

greenTokenText :: GreenElement -> Text
greenTokenText (GreenTokenElement t) = gtText t
greenTokenText (GreenNodeElement _) = T.empty

greenDescendants :: GreenNode -> [GreenElement]
greenDescendants n = concatMap go (greenChildren n)
  where
    go e@(GreenTokenElement _) = [e]
    go e@(GreenNodeElement child) = e : greenDescendants child

greenTokens :: GreenNode -> [GreenToken]
greenTokens n = concatMap go (greenChildren n)
  where
    go (GreenTokenElement t) = [t]
    go (GreenNodeElement child) = greenTokens child

data GreenInterner = GreenInterner
    { internerNodes :: !(IORef (HM.HashMap NodeData GreenNode))
    , internerTokens :: !(IORef (HM.HashMap GreenToken GreenToken))
    }

newInterner :: IO GreenInterner
newInterner =
    GreenInterner
        <$> newIORef HM.empty
        <*> newIORef HM.empty

internNode :: GreenInterner -> SyntaxKind -> [GreenElement] -> IO GreenNode
internNode interner kind children' = do
    let nd = NodeData kind children' (sum $ map elementTextLen children')
    nodes <- readIORef (internerNodes interner)
    case HM.lookup nd nodes of
        Just existing -> return existing
        Nothing -> do
            let newNode = GreenNode nd
            writeIORef (internerNodes interner) (HM.insert nd newNode nodes)
            return newNode

internToken :: GreenInterner -> SyntaxKind -> Text -> IO GreenElement
internToken interner kind txt = do
    let tok = GreenToken kind txt
    tokens' <- readIORef (internerTokens interner)
    case HM.lookup tok tokens' of
        Just existing -> return $ GreenTokenElement existing
        Nothing -> do
            writeIORef (internerTokens interner) (HM.insert tok tok tokens')
            return $ GreenTokenElement tok
