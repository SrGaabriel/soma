module Logging.Errors where

class PrintableError a where
    errorMessage :: a -> String
    errorStart :: a -> Int
    errorEnd :: a -> Int

    errorDebugDevDetails :: a -> String
    errorDebugDevDetails _ = "No debug details available"
