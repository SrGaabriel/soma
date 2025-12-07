module Utils.Lists (
    hardTail,
    hardHead,
    hardLast,
) where

hardHead :: [a] -> a
hardHead [] = error "Empty list"
hardHead (x : _) = x

hardTail :: [a] -> [a]
hardTail [] = error "Empty list"
hardTail xs = take (length xs - 1) xs

hardLast :: [a] -> a
hardLast [] = error "Empty list"
hardLast xs = xs !! (length xs - 1)
