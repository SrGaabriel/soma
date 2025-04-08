module Utils.Lists (hardTail, hardHead) where

hardHead :: [a] -> a
hardHead [] = error "Empty list"
hardHead (x : _) = x

hardTail :: [a] -> [a]
hardTail [] = error "Empty list"
hardTail xs = take (length xs - 1) xs
