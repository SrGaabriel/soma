{-@ LIQUID "--no-termination" @-}

module Utils.Lists (
    hardTail,
    hardHead,
    hardLast,
) where

-- | Non-empty list type alias for LiquidHaskell
{-@ type NonEmpty a = {v:[a] | len v > 0} @-}

-- | Safe head for non-empty lists
{-@ hardHead :: NonEmpty a -> a @-}
hardHead :: [a] -> a
hardHead [] = error "Empty list"
hardHead (x : _) = x

-- | Safe init (all but last) for non-empty lists
{-@ hardTail :: NonEmpty a -> [a] @-}
hardTail :: [a] -> [a]
hardTail [] = error "Empty list"
hardTail xs = take (length xs - 1) xs

-- | Safe last for non-empty lists
{-@ hardLast :: NonEmpty a -> a @-}
hardLast :: [a] -> a
hardLast [] = error "Empty list"
hardLast xs = xs !! (length xs - 1)
