module Config.Options where

import Data.List (isPrefixOf)
import System.Environment (getArgs)
import Utils.Lists (hardHead, hardTail)

fileExt :: String
fileExt = ".soma"

data Options = Options
    { optionsInput :: String
    , optionsOutput :: Maybe String
    , optionsLlvmOnly :: Bool
    , optionsKeepAll :: Bool
    , optionsEmitTypes :: Bool
    , optionsRun :: Bool
    }
    deriving (Show)

defaultOptions :: Options
defaultOptions =
    Options
        { optionsInput = "app.soma"
        , optionsOutput = Nothing
        , optionsLlvmOnly = False
        , optionsKeepAll = False
        , optionsRun = False
        , optionsEmitTypes = True
        }

getInputFile :: Options -> String
getInputFile opts =
    case break (== '.') (optionsInput opts) of
        (name, ext) | ext == fileExt -> name ++ fileExt
        (name, _) -> name ++ fileExt

getInputName :: Options -> Maybe String
getInputName opts =
    case break (== '.') (optionsInput opts) of
        (name, ext) | ext == fileExt -> Just name
        _ -> Nothing

parseCommandLine :: [String] -> Either CommandLineError Options
parseCommandLine args = do
    let opts = processArgs args defaultOptions
    let indArgs = findIndependentArgs args
    if null indArgs
        then Left NoInputFile
        else Right opts{optionsInput = unwords indArgs}

processArgs :: [String] -> Options -> Options
processArgs [] opts = opts
processArgs (arg : rest) opts
    | arg == "--llvm-only" = processArgs rest (opts{optionsLlvmOnly = True})
    | arg == "--keep" = processArgs rest (opts{optionsKeepAll = True})
    | arg == "--run" = processArgs rest (opts{optionsRun = True})
    | arg == "-output" && not (null rest) =
        processArgs (hardTail rest) (opts{optionsOutput = Just (hardHead rest)})
    | arg == "--emit-types" =
        processArgs rest (opts{optionsEmitTypes = True})
    | "--output=" `isPrefixOf` arg =
        let value = drop (length "--output=") arg
        in processArgs rest (opts{optionsOutput = Just value})
    | otherwise = processArgs rest opts

findIndependentArgs :: [String] -> [String]
findIndependentArgs = filter (not . isPrefixOf "-")

extractOptions :: IO (Either CommandLineError Options)
extractOptions = parseCommandLine <$> getArgs

data CommandLineError
    = NoInputFile
    | InvalidArgument String
    deriving (Show, Eq)

formatError :: CommandLineError -> String
formatError NoInputFile =
    "Error: No input file specified. Please provide a source file with "
        ++ fileExt
        ++ " extension."
formatError (InvalidArgument arg) =
    "Error: Invalid argument: " ++ arg
