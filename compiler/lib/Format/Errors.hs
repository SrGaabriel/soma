{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}

module Format.Errors where

class PrintableError a where
    errorMessage :: a -> String
    errorStart :: a -> Int
    errorEnd :: a -> Int

    errorHint :: a -> Maybe String
    errorHint _ = Nothing

    errorDebugDevDetails :: a -> String
    errorDebugDevDetails _ = "No debug details available"

data SomeError where
    SomeError ::
        (PrintableError e) =>
        e -> FilePath -> String -> String -> SomeError

instance PrintableError SomeError where
    errorStart (SomeError e _ _ _) = errorStart e
    errorEnd (SomeError e _ _ _) = errorEnd e
    errorMessage (SomeError e _ _ _) = errorMessage e

newtype CycleError = CycleError [String]

instance PrintableError CycleError where
    errorMessage (CycleError modules) = "Cyclic import detected: " ++ unwords modules
    errorStart _ = 0
    errorEnd _ = 0
