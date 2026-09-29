module Soma.Diagnostic where

import Data.Text (Text)
import Maple.Position (Range)

data Severity
    = SError
    | SWarning
    | SLint
    deriving (Show, Eq)

data Label = Label
    { labRange :: Range
    , labMessage :: Maybe Text
    }

data Diagnostic = Diagnostic
    { diagSeverity :: Severity
    , diagCode :: Maybe Text
    , diagMessage :: Text
    , diagPrimary :: Label
    , diagSecondaries :: [Label]
    , diagNotes :: [Text]
    , diagHelps :: [Text]
    }
