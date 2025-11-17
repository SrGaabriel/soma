module Config.Options (
    Options (..),
    CommandLineError (..),
    formatError,
    fileExt,
    getInputFile,
    getInputName,
    Command (..),
    commandParser,
    extractCommand
) where

import Data.List (isPrefixOf)
import Options.Applicative
import System.Environment (getArgs)

fileExt :: String
fileExt = ".soma"

data Command
    = Build Options
    | Lex String
    | Parse String
    deriving (Show)

data Options = Options
    { optionsInput :: String
    , optionsOutput :: Maybe String
    , optionsName :: Maybe String
    , optionsLib :: Bool
    , optionsLlvmOnly :: Bool
    , optionsKeepAll :: Bool
    , optionsEmitLib :: Bool
    , optionsDeps :: [(String, String)]
    , optionsRun :: Bool
    }
    deriving (Show)

commandParser :: Parser Command
commandParser =
    hsubparser
        ( command "lex" (info (Lex <$> inputParser) (progDesc "Run the lexer"))
            <> command "build" (info (Build <$> optionsParser) (progDesc "Build the program"))
            <> command "parse" (info (Parse <$> inputParser) (progDesc "Run the parser"))
        )
        <|> (Build <$> optionsParser)

inputParser :: Parser String
inputParser =
    argument
        str
        ( metavar "INPUT"
            <> help ("Input source file (" ++ fileExt ++ ")")
        )

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

optionsParser :: Parser Options
optionsParser =
    Options
        <$> inputParser
        <*> optional
            ( strOption
                ( long "out"
                    <> metavar "OUTPUT"
                    <> help "Output file path"
                )
            )
        <*> optional
            ( strOption
                ( long "name"
                    <> metavar "NAME"
                    <> help "Name of the compiled program or library"
                )
            )
        <*> switch
            ( long "lib"
                <> help "Compile as a Soma library"
            )
        <*> switch
            ( long "llvm-only"
                <> help "Emit LLVM IR only (no compilation or run)"
            )
        <*> switch
            ( long "keep"
                <> help "Keep intermediate compilation files"
            )
        <*> switch
            ( long "emit-lib"
                <> help "Emit output as a shared library"
            )
        <*> many
            ( option
                (eitherReader parseExtern)
                ( long "dep"
                    <> metavar "NAME=PATH"
                    <> help "Link external library (e.g. --dep foo=src/lib/foo.toria)"
                )
            )
        <*> switch
            ( long "run"
                <> help "Run the compiled program immediately"
            )

parseExtern :: String -> Either String (String, String)
parseExtern s =
    case break (== '=') s of
        (k, '=' : v) | not (null k) && not (null v) -> Right (k, v)
        _ -> Left "Expected format NAME=PATH"

commandInfo :: ParserInfo Command
commandInfo =
    info
        (commandParser <**> helper)
        ( fullDesc
            <> progDesc "Compile and/or run Soma source files"
            <> header "soma-compiler - a compiler for the Soma language"
        )

extractCommand :: IO (Either CommandLineError Command)
extractCommand = do
    args <- getArgs
    if all (isPrefixOf "-") args
        then pure (Left NoInputFile)
        else Right <$> execParser commandInfo
