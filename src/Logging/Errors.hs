{-# LANGUAGE ExistentialQuantification #-}
module Logging.Errors where

class PrintableError a where
    errorMessage :: a -> String
    errorStart :: a -> Int
    errorEnd :: a -> Int

    errorDebugDevDetails :: a -> String
    errorDebugDevDetails _ = "No debug details available"

data SomeError = forall e. (PrintableError e) => SomeError e FilePath String String

instance PrintableError SomeError where
    errorStart (SomeError e _ _ _) = errorStart e
    errorEnd (SomeError e _ _ _) = errorEnd e
    errorMessage (SomeError e _ _ _) = errorMessage e