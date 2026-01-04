{-# LANGUAGE OverloadedStrings #-}

module Syntax.CST.RedTree (
    SyntaxNode (..),
    SyntaxToken (..),
    SyntaxElement (..),
    syntaxRoot,
    parent,
    children,
    childrenWithTokens,
    firstChild,
    lastChild,
    nextSibling,
    prevSibling,
    ancestors,
    descendants,
    tokens,
    syntaxKind,
    textRange,
    textOffset,
    textLen,
    text,
    containsOffset,
    tokenAtOffset,
    nodeAtOffset,
    coveringElement,
    childOfKind,
    childrenOfKind,
    firstToken,
    lastToken,
) where

import Data.List (find)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word (Word32)
import Syntax.CST.GreenTree
import Syntax.CST.SyntaxKind

data SyntaxNode = SyntaxNode
    { snGreen :: !GreenNode -- The underlying immutable green node
    , snParent :: !(Maybe SyntaxNode) -- Parent node (Nothing for root)
    , snOffset :: {-# UNPACK #-} !Word32 -- Absolute offset in source
    , snIndex :: {-# UNPACK #-} !Int -- Index in parent's children
    }

instance Eq SyntaxNode where
    a == b = snOffset a == snOffset b && snGreen a == snGreen b

instance Show SyntaxNode where
    show n =
        "SyntaxNode { kind = "
            ++ show (syntaxKind (SyntaxNodeElement n))
            ++ ", offset = "
            ++ show (snOffset n)
            ++ ", len = "
            ++ show (ndTextLen (unGreenNode (snGreen n)))
            ++ " }"

data SyntaxToken = SyntaxToken
    { stGreen :: !GreenToken
    , stParent :: !SyntaxNode
    , stOffset :: {-# UNPACK #-} !Word32
    , stIndex :: {-# UNPACK #-} !Int
    }

instance Eq SyntaxToken where
    a == b = stOffset a == stOffset b && stGreen a == stGreen b

instance Show SyntaxToken where
    show t =
        "SyntaxToken { kind = "
            ++ show (gtKind (stGreen t))
            ++ ", offset = "
            ++ show (stOffset t)
            ++ ", text = "
            ++ show (gtText (stGreen t))
            ++ " }"

data SyntaxElement
    = SyntaxNodeElement !SyntaxNode
    | SyntaxTokenElement !SyntaxToken
    deriving (Eq, Show)

syntaxRoot :: GreenNode -> SyntaxNode
syntaxRoot green =
    SyntaxNode
        { snGreen = green
        , snParent = Nothing
        , snOffset = 0
        , snIndex = 0
        }

parent :: SyntaxNode -> Maybe SyntaxNode
parent = snParent

children :: SyntaxNode -> [SyntaxNode]
children n = mapMaybe extractNode (childrenWithTokens n)
  where
    extractNode (SyntaxNodeElement child) = Just child
    extractNode (SyntaxTokenElement _) = Nothing

childrenWithTokens :: SyntaxNode -> [SyntaxElement]
childrenWithTokens n = zipWith mkChild [0 ..] (greenChildrenWithOffsets (snGreen n))
  where
    mkChild idx (relOffset, green) =
        let absOffset = snOffset n + relOffset
        in case green of
            GreenTokenElement tok ->
                SyntaxTokenElement
                    $ SyntaxToken
                        { stGreen = tok
                        , stParent = n
                        , stOffset = absOffset
                        , stIndex = idx
                        }
            GreenNodeElement gn ->
                SyntaxNodeElement
                    $ SyntaxNode
                        { snGreen = gn
                        , snParent = Just n
                        , snOffset = absOffset
                        , snIndex = idx
                        }

firstChild :: SyntaxNode -> Maybe SyntaxNode
firstChild = listToMaybe . children

lastChild :: SyntaxNode -> Maybe SyntaxNode
lastChild n = case children n of
    [] -> Nothing
    cs -> Just (last cs)

nextSibling :: SyntaxNode -> Maybe SyntaxNode
nextSibling n = do
    p <- snParent n
    let sibs = children p
        idx = snIndex n
    find (\s -> snIndex s > idx) sibs

prevSibling :: SyntaxNode -> Maybe SyntaxNode
prevSibling n = do
    p <- snParent n
    let sibs = children p
        idx = snIndex n
    listToMaybe $ reverse $ filter (\s -> snIndex s < idx) sibs

ancestors :: SyntaxNode -> [SyntaxNode]
ancestors n = case snParent n of
    Nothing -> []
    Just p -> p : ancestors p

descendants :: SyntaxNode -> [SyntaxNode]
descendants n = concatMap go (children n)
  where
    go child = child : descendants child

tokens :: SyntaxNode -> [SyntaxToken]
tokens n = concatMap go (childrenWithTokens n)
  where
    go (SyntaxTokenElement t) = [t]
    go (SyntaxNodeElement child) = tokens child

syntaxKind :: SyntaxElement -> SyntaxKind
syntaxKind (SyntaxNodeElement n) = ndKind (unGreenNode (snGreen n))
syntaxKind (SyntaxTokenElement t) = gtKind (stGreen t)

textRange :: SyntaxElement -> TextRange
textRange e = TextRange (textOffset e) (textLen e)

textOffset :: SyntaxElement -> Word32
textOffset (SyntaxNodeElement n) = snOffset n
textOffset (SyntaxTokenElement t) = stOffset t

textLen :: SyntaxElement -> Word32
textLen (SyntaxNodeElement n) = ndTextLen (unGreenNode (snGreen n))
textLen (SyntaxTokenElement t) = fromIntegral $ T.length $ gtText (stGreen t)

text :: SyntaxElement -> Text
text (SyntaxNodeElement n) = greenText (GreenNodeElement (snGreen n))
text (SyntaxTokenElement t) = gtText (stGreen t)

containsOffset :: SyntaxElement -> Word32 -> Bool
containsOffset e = rangeContains (textRange e)

tokenAtOffset :: SyntaxNode -> Word32 -> Maybe SyntaxToken
tokenAtOffset root offset
    | not (containsOffset (SyntaxNodeElement root) offset) = Nothing
    | otherwise = go root
  where
    go n = case filter (`containsOffset` offset) (childrenWithTokens n) of
        [] -> Nothing
        (SyntaxTokenElement t : _) -> Just t
        (SyntaxNodeElement child : _) -> go child

nodeAtOffset :: SyntaxNode -> Word32 -> Maybe SyntaxNode
nodeAtOffset root offset
    | not (containsOffset (SyntaxNodeElement root) offset) = Nothing
    | otherwise = Just $ go root
  where
    go :: SyntaxNode -> SyntaxNode
    go n = case filter (containsOffsetNode offset) (children n) of
        [] -> n
        (child : _) -> go child
    containsOffsetNode off node' = containsOffset (SyntaxNodeElement node') off

coveringElement :: SyntaxNode -> Word32 -> Maybe SyntaxElement
coveringElement root offset
    | not (containsOffset (SyntaxNodeElement root) offset) = Nothing
    | otherwise = Just $ go (SyntaxNodeElement root)
  where
    go (SyntaxTokenElement t) = SyntaxTokenElement t
    go (SyntaxNodeElement n) =
        case filter (`containsOffset` offset) (childrenWithTokens n) of
            [] -> SyntaxNodeElement n
            (child : _) -> go child

childOfKind :: SyntaxKind -> SyntaxNode -> Maybe SyntaxNode
childOfKind kind n = find (\c -> ndKind (unGreenNode (snGreen c)) == kind) (children n)

childrenOfKind :: SyntaxKind -> SyntaxNode -> [SyntaxNode]
childrenOfKind kind n = filter (\c -> ndKind (unGreenNode (snGreen c)) == kind) (children n)

firstToken :: SyntaxNode -> Maybe SyntaxToken
firstToken n = case childrenWithTokens n of
    [] -> Nothing
    (SyntaxTokenElement t : _) -> Just t
    (SyntaxNodeElement child : _) -> firstToken child

lastToken :: SyntaxNode -> Maybe SyntaxToken
lastToken n = case reverse (childrenWithTokens n) of
    [] -> Nothing
    (SyntaxTokenElement t : _) -> Just t
    (SyntaxNodeElement child : _) -> lastToken child
