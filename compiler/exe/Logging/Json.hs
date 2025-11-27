{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Logging.Json (
    JsonOutput (..),
    JsonDiagnostic (..),
    JsonPosition (..),
    JsonRange (..),
    DiagnosticSeverity (..),
    someErrorToJson,
    errorsToJsonOutput,
    failedJsonOutput,
    printJsonOutput,
) where

import Data.Aeson (ToJSON (..), encode, object, (.=))
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Text (Text)
import qualified Data.Text as T
import Format.Errors (PrintableError (..), SomeError (..))
import GHC.Generics (Generic)

data DiagnosticSeverity
    = SeverityError
    | SeverityWarning
    | SeverityInfo
    | SeverityHint
    deriving (Show, Eq, Generic)

instance ToJSON DiagnosticSeverity where
    toJSON SeverityError = toJSON (1 :: Int)
    toJSON SeverityWarning = toJSON (2 :: Int)
    toJSON SeverityInfo = toJSON (3 :: Int)
    toJSON SeverityHint = toJSON (4 :: Int)

data JsonPosition = JsonPosition
    { jpLine :: !Int
    , jpCharacter :: !Int
    }
    deriving (Show, Eq, Generic)

instance ToJSON JsonPosition where
    toJSON p =
        object
            [ "line" .= jpLine p
            , "character" .= jpCharacter p
            ]

data JsonRange = JsonRange
    { jrStart :: !JsonPosition
    , jrEnd :: !JsonPosition
    }
    deriving (Show, Eq, Generic)

instance ToJSON JsonRange where
    toJSON r =
        object
            [ "start" .= jrStart r
            , "end" .= jrEnd r
            ]

data JsonDiagnostic = JsonDiagnostic
    { jdFile :: !Text
    , jdRange :: !JsonRange
    , jdSeverity :: !DiagnosticSeverity
    , jdMessage :: !Text
    , jdSource :: !Text
    , jdCode :: !(Maybe Text)
    }
    deriving (Show, Eq, Generic)

instance ToJSON JsonDiagnostic where
    toJSON d =
        object
            [ "file" .= jdFile d
            , "range" .= jdRange d
            , "severity" .= jdSeverity d
            , "message" .= jdMessage d
            , "source" .= jdSource d
            , "code" .= jdCode d
            ]

data JsonOutput = JsonOutput
    { joSuccess :: !Bool
    , joDiagnostics :: ![JsonDiagnostic]
    , joModuleName :: !(Maybe Text)
    }
    deriving (Show, Eq, Generic)

instance ToJSON JsonOutput where
    toJSON o =
        object
            [ "success" .= joSuccess o
            , "diagnostics" .= joDiagnostics o
            , "module" .= joModuleName o
            ]

offsetToPosition :: String -> Int -> JsonPosition
offsetToPosition content offset =
    let safeOffset = max 0 (min offset (length content))
        prefix = take safeOffset content
        (line, col) = foldl' countLineCol (0, 0) prefix
    in JsonPosition line col
  where
    countLineCol (l, _) '\n' = (l + 1, 0)
    countLineCol (l, c) _ = (l, c + 1)

someErrorToJson :: SomeError -> JsonDiagnostic
someErrorToJson (SomeError err filePath code source) =
    let start = errorStart err
        end = errorEnd err
        startPos = offsetToPosition code start
        endPos = offsetToPosition code end
    in JsonDiagnostic
        { jdFile = T.pack filePath
        , jdRange = JsonRange startPos endPos
        , jdSeverity = SeverityError
        , jdMessage = T.pack (errorMessage err)
        , jdSource = T.pack source
        , jdCode = Nothing
        }

errorsToJsonOutput :: Maybe String -> [SomeError] -> JsonOutput
errorsToJsonOutput modName errors =
    JsonOutput
        { joSuccess = null errors
        , joDiagnostics = map someErrorToJson errors
        , joModuleName = T.pack <$> modName
        }

failedJsonOutput :: Maybe String -> JsonOutput
failedJsonOutput modName =
    JsonOutput
        { joSuccess = False
        , joDiagnostics = []
        , joModuleName = T.pack <$> modName
        }

printJsonOutput :: JsonOutput -> IO ()
printJsonOutput = BL.putStrLn . encode
