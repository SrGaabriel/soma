module Utils.Lists (hardHead) where

hardHead :: [a] -> a
hardHead [] = error "Empty list"
hardHead (x:_) = x