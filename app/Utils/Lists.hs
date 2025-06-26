{-# LANGUAGE BangPatterns #-}

module Utils.Lists (hardTail, hardHead, zipReturningRHSExcess, debugTrace) where

import qualified Debug.Trace as Debug

hardHead :: [a] -> a
hardHead [] = error "Empty list"
hardHead (x : _) = x

hardTail :: [a] -> [a]
hardTail [] = error "Empty list"
hardTail xs = take (length xs - 1) xs

zipReturningRHSExcess :: [a] -> [b] -> ([(a, b)], [b])
zipReturningRHSExcess xs ys =
    let (zipped, excess) = splitAt (length xs) ys
    in (zip xs zipped, excess)

debugTrace :: (Monad m) => String -> m ()
debugTrace msg = let !_ = Debug.trace msg () in pure ()
