module Soma.Syntax.TokenSet (
    TokenSet,
    tokenSet,
    member,
    toList,
) where

import Data.Bits (setBit, shiftR, testBit, (.|.))
import Data.Word (Word64)
import Soma.Syntax.Kind (Kind)

newtype TokenSet = TokenSet Word64
    deriving (Eq)

instance Semigroup TokenSet where
    TokenSet a <> TokenSet b = TokenSet (a .|. b)

instance Monoid TokenSet where
    mempty = TokenSet 0

instance Show TokenSet where
    show = show . toList

bit :: Kind -> Int
bit k
    | i < 64 = i
    | otherwise = error ("TokenSet: kind " <> show k <> " does not fit in a 64-bit set")
  where
    i = fromEnum k

tokenSet :: [Kind] -> TokenSet
tokenSet = TokenSet . foldl' (\acc k -> setBit acc (bit k)) 0

member :: Kind -> TokenSet -> Bool
member k (TokenSet s) = testBit s (bit k)

toList :: TokenSet -> [Kind]
toList (TokenSet s) = go s 0
  where
    go :: Word64 -> Int -> [Kind]
    go 0 _ = []
    go w i
        | testBit w 0 = toEnum i : go (w `shiftR` 1) (i + 1)
        | otherwise = go (w `shiftR` 1) (i + 1)
