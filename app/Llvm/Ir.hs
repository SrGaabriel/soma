module Llvm.Ir where

class IR a where
    toLlvm :: a -> String