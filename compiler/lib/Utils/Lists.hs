module Utils.Lists (
    hardTail,
    hardHead,
    zipReturningRHSExcess,
    allEqual,
    foldMWithErrors,
    mapIndexed,
    breakLast,
    hardLast,
) where

import Data.List (group)

hardHead :: [a] -> a
hardHead [] = error "Empty list"
hardHead (x : _) = x

hardTail :: [a] -> [a]
hardTail [] = error "Empty list"
hardTail xs = take (length xs - 1) xs

hardLast :: [a] -> a
hardLast [] = error "Empty list"
hardLast xs = xs !! (length xs - 1)

breakLast :: (Eq a) => a -> [a] -> ([a], [a])
breakLast c =
    (\(x, y) -> (reverse y, reverse x))
        . span (/= c)
        . reverse

zipReturningRHSExcess :: [a] -> [b] -> ([(a, b)], [b])
zipReturningRHSExcess xs ys =
    let (zipped, excess) = splitAt (length xs) ys
    in (zip xs zipped, excess)

allEqual :: (Eq a) => [a] -> Bool
allEqual xs = length (group xs) == 1

foldMWithErrors :: (b -> a -> Either [err] b) -> b -> [a] -> Either [err] b
foldMWithErrors f = go []
  where
    go errs acc [] = if null errs then Right acc else Left errs
    go errs acc (x : xs) =
        case f acc x of
            Right acc' -> go errs acc' xs
            Left newErrs -> go (errs ++ newErrs) acc xs

mapIndexed :: (Int -> a -> b) -> [a] -> [b]
mapIndexed f = zipWith f [0 ..]
